//! A free-list-based page/frame allocator.
//!
//! The main type of this crate is [`FreeList`], which allocates [`PageRange`]s.
//!
//! # Examples
//!
//! ```
//! use free_list::{FreeList, PageLayout};
//!
//! let mut free_list = FreeList::<16>::new();
//!
//! unsafe {
//!     free_list.deallocate((0x1000..0x5000).try_into().unwrap()).unwrap();
//! }
//! assert_eq!(free_list.free_space(), 0x4000);
//!
//! let layout = PageLayout::from_size(0x4000).unwrap();
//! assert_eq!(free_list.allocate(layout).unwrap(), (0x1000..0x5000).try_into().unwrap());
//! ```

#![cfg_attr(not(test), no_std)]
#![cfg_attr(docsrs, feature(doc_auto_cfg))]
#![warn(missing_docs)]

#[doc = include_str!("../README.md")]
#[cfg(doctest)]
pub struct ReadmeDoctests;

mod page_layout;
mod page_list;
mod page_range;

use core::fmt;
use core::num::NonZeroUsize;

pub use self::page_layout::{PageLayout, PageLayoutError};
use self::page_list::PageList;
pub use self::page_range::{PageRange, PageRangeError, PageRangeSub};

/// The base page size.
///
/// [`PageRange`] and [`PageLayout`] may only refer to whole pages of this size.
pub const PAGE_SIZE: usize = 4096;

/// A free-list-based page/frame allocator.
///
/// This type can be used for managing (allocating and deallocating) physical and virtual memory at [`PAGE_SIZE`] granularity.
/// This is useful for ensuring pages and frames being currently unused before mapping them.
///
/// The `const N: usize` generic specifies how many internal [`PageRange`]s the free list can hold before needing to allocate more memory from the global allocator.
///
/// # Examples
///
/// ```
/// use free_list::{FreeList, PageLayout};
///
/// let mut free_list = FreeList::<16>::new();
///
/// unsafe {
///     free_list.deallocate((0x1000..0x5000).try_into().unwrap()).unwrap();
/// }
/// assert_eq!(free_list.free_space(), 0x4000);
///
/// let layout = PageLayout::from_size(0x4000).unwrap();
/// assert_eq!(free_list.allocate(layout).unwrap(), (0x1000..0x5000).try_into().unwrap());
/// ```
#[derive(Debug)]
pub struct FreeList<const N: usize> {
    list: PageList<N>,
}

/// Allocation failure.
#[derive(Clone, PartialEq, Eq, Debug)]
#[non_exhaustive]
pub struct AllocError;

impl fmt::Display for AllocError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("memory allocation failed")
    }
}

impl<const N: usize> FreeList<N> {
    /// Creates a new free list without any free space.
    ///
    /// # Examples
    ///
    /// ```
    /// use free_list::FreeList;
    ///
    /// let free_list = FreeList::<16>::new();
    /// ```
    pub const fn new() -> Self {
        Self {
            list: PageList::new(),
        }
    }

    /// Attempts to allocate a page range.
    ///
    /// On success, returns a [`PageRange`] meeting the size and alignment guarantees of `layout`.
    ///
    /// # Examples
    ///
    /// ```
    /// use free_list::{FreeList, PageLayout};
    ///
    /// let mut free_list = FreeList::<16>::new();
    ///
    /// unsafe {
    ///     free_list.deallocate((0x1000..0x5000).try_into().unwrap()).unwrap();
    /// }
    ///
    /// let layout = PageLayout::from_size(0x4000).unwrap();
    /// assert_eq!(free_list.allocate(layout).unwrap(), (0x1000..0x5000).try_into().unwrap());
    /// ```
    pub fn allocate(&mut self, layout: PageLayout) -> Result<PageRange, AllocError> {
        self.allocate_with(|range| range.fit(layout))
    }

    /// Attempts to deallocates a page range.
    ///
    /// This should also be used to add more free pages to the allocator, such as after initialization.
    /// This returns an error, if `range` overlaps with any pages that are already deallocated.
    ///
    /// # Examples
    ///
    /// ```
    /// use free_list::FreeList;
    ///
    /// let mut free_list = FreeList::<16>::new();
    ///
    /// unsafe {
    ///     free_list.deallocate((0x1000..0x2000).try_into().unwrap()).unwrap();
    /// }
    /// ```
    ///
    /// # Safety
    ///
    /// `range` must be valid to be allocated and used (again).
    pub unsafe fn deallocate(&mut self, range: PageRange) -> Result<(), AllocError> {
        self.list.add(range).map_err(|_| AllocError)
    }

    /// Attempts to allocate a specific page range.
    ///
    /// # Examples
    ///
    /// ```
    /// use free_list::FreeList;
    ///
    /// let mut free_list = FreeList::<16>::new();
    ///
    /// unsafe {
    ///     free_list.deallocate((0x1000..0x2000).try_into().unwrap()).unwrap();
    ///     free_list.deallocate((0x3000..0x4000).try_into().unwrap()).unwrap();
    /// }
    ///
    /// free_list.allocate_at((0x3000..0x4000).try_into().unwrap()).unwrap();
    /// ```
    pub fn allocate_at(&mut self, range: PageRange) -> Result<(), AllocError> {
        self.list.remove(range).map_err(|_| AllocError)
    }

    /// Attempts to allocate a page range according to a function.
    ///
    /// On success, allocates and returns the first non-none [`PageRange`] returned by `f`.
    ///
    /// # Examples
    ///
    /// ```
    /// use free_list::{FreeList, PageLayout};
    ///
    /// let mut free_list = FreeList::<16>::new();
    ///
    /// unsafe {
    ///     free_list.deallocate((0x1000..0x2000).try_into().unwrap()).unwrap();
    ///     free_list.deallocate((0x3000..0x4000).try_into().unwrap()).unwrap();
    /// }
    ///
    /// let layout = PageLayout::from_size(0x1000).unwrap();
    /// let allocated = free_list.allocate_with(|range| {
    ///     (range.start() > 0x2000)
    ///         .then_some(range)
    ///         .and_then(|range| range.fit(layout))
    /// });
    /// assert_eq!(allocated.unwrap(), (0x3000..0x4000).try_into().unwrap());
    /// ```
    pub fn allocate_with<F>(&mut self, f: F) -> Result<PageRange, AllocError>
    where
        F: FnMut(PageRange) -> Option<PageRange>,
    {
        let mut f = f;

        let (index, fit) = self
            .list
            .iter()
            .enumerate()
            .find_map(|(index, entry)| f(entry).map(|fit| (index, fit)))
            .ok_or(AllocError)?;

        self.list.remove_at(index, fit).unwrap();

        Ok(fit)
    }

    /// Attempts to allocate a page range outside of a given page range.
    ///
    /// On success, returns a [`PageRange`] meeting the size and alignment guarantees of `layout` outside of `range`.
    ///
    /// # Examples
    ///
    /// ```
    /// use free_list::{FreeList, PageLayout, PageRange};
    ///
    /// let mut free_list = FreeList::<16>::new();
    ///
    /// unsafe {
    ///     free_list.deallocate((0x1000..0x5000).try_into().unwrap()).unwrap();
    /// }
    ///
    /// let layout = PageLayout::from_size(0x1000).unwrap();
    /// let range = PageRange::new(0x0000, 0x2000).unwrap();
    /// let allocated = free_list.allocate_outside_of(layout, range);
    /// assert_eq!(allocated.unwrap(), (0x2000..0x3000).try_into().unwrap());
    /// ```
    pub fn allocate_outside_of(
        &mut self,
        layout: PageLayout,
        range: PageRange,
    ) -> Result<PageRange, AllocError> {
        self.allocate_with(|entry| match entry - range {
            PageRangeSub::None => None,
            PageRangeSub::One(a) => a.fit(layout),
            PageRangeSub::Two(a, b) => a.fit(layout).or_else(|| b.fit(layout)),
        })
    }

    /// Returns how much free space this allocator has in bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use free_list::FreeList;
    ///
    /// let mut free_list = FreeList::<16>::new();
    ///
    /// unsafe {
    ///     free_list.deallocate((0x1000..0x5000).try_into().unwrap()).unwrap();
    /// }
    /// assert_eq!(free_list.free_space(), 0x4000);
    /// ```
    pub fn free_space(&self) -> usize {
        self.list
            .iter()
            .map(PageRange::len)
            .map(NonZeroUsize::get)
            .sum()
    }
}

impl<const N: usize> Default for FreeList<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const N: usize> fmt::Display for FreeList<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.list.fmt(f)
    }
}

#[cfg(all(target_arch = "x86_64", feature = "x86_64"))]
mod frame_allocator {
    use x86_64::structures::paging::{FrameAllocator, FrameDeallocator, PageSize, PhysFrame};
    use x86_64::PhysAddr;

    use super::*;

    unsafe impl<S: PageSize, const N: usize> FrameAllocator<S> for FreeList<N> {
        fn allocate_frame(&mut self) -> Option<PhysFrame<S>> {
            let size = S::SIZE.try_into().unwrap();
            let layout = PageLayout::from_size_align(size, size).unwrap();
            let range = self.allocate(layout).ok()?;
            let address = PhysAddr::new(range.start().try_into().unwrap());
            Some(PhysFrame::from_start_address(address).unwrap())
        }
    }

    impl<S: PageSize, const N: usize> FrameDeallocator<S> for FreeList<N> {
        unsafe fn deallocate_frame(&mut self, frame: PhysFrame<S>) {
            unsafe {
                self.deallocate(frame.into())
                    .expect("frame could not be deallocated");
            }
        }
    }

    impl<S: PageSize> From<PhysFrame<S>> for PageRange {
        fn from(value: PhysFrame<S>) -> Self {
            let start = value.start_address().as_u64().try_into().unwrap();
            let len = value.size().try_into().unwrap();
            Self::from_start_len(start, len).unwrap()
        }
    }
}
