use core::alloc::Layout;
use core::fmt;

use align_address::usize_is_aligned_to;

use crate::PAGE_SIZE;

/// Invalid parameters used in [`PageLayout`] construction.
#[non_exhaustive]
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct PageLayoutError;

impl fmt::Display for PageLayoutError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("invalid parameters to PageLayout::from_size_align")
    }
}

/// Layout of a range of pages.
///
/// This is analogous to [`Layout`], but requires the size and alignment to refer to whole pages.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct PageLayout(Layout);

impl PageLayout {
    /// Constructs a `PageLayout` from a given `size` and `align`,
    /// or returns `PageLayoutError` if any of the following conditions
    /// are not met:
    ///
    /// * `align` must not be zero,
    ///
    /// * `align` must be a power of two,
    ///
    /// * `size`, when rounded up to the nearest multiple of `align`,
    ///   must not overflow isize (i.e., the rounded value must be
    ///   less than or equal to `isize::MAX`),
    ///
    /// * `size` and `align` must both be aligned to [`PAGE_SIZE`].
    #[inline]
    pub const fn from_size_align(size: usize, align: usize) -> Result<Self, PageLayoutError> {
        if !usize_is_aligned_to(size, PAGE_SIZE) {
            return Err(PageLayoutError);
        }

        if !usize_is_aligned_to(align, PAGE_SIZE) {
            return Err(PageLayoutError);
        }

        match Layout::from_size_align(size, align) {
            Ok(layout) => Ok(Self(layout)),
            Err(_) => Err(PageLayoutError),
        }
    }

    /// Creates a page layout, bypassing all checks.
    ///
    /// # Safety
    ///
    /// This function is unsafe as it does not verify the preconditions from [`PageLayout::from_size_align`].
    #[must_use]
    #[inline]
    pub const unsafe fn from_size_align_unchecked(size: usize, align: usize) -> Self {
        // SAFETY: the caller is required to uphold the preconditions.
        unsafe { Self(Layout::from_size_align_unchecked(size, align)) }
    }

    /// Creates a page layout with [`PAGE_SIZE`] alignment.
    #[inline]
    pub const fn from_size(size: usize) -> Result<Self, PageLayoutError> {
        Self::from_size_align(size, PAGE_SIZE)
    }

    /// The minimum size in bytes for a memory block of this page layout.
    #[must_use]
    #[inline]
    pub const fn size(&self) -> usize {
        self.0.size()
    }

    /// The minimum byte
    #[must_use]
    #[inline]
    pub const fn align(&self) -> usize {
        self.0.align()
    }
}

impl TryFrom<Layout> for PageLayout {
    type Error = PageLayoutError;

    #[inline]
    fn try_from(value: Layout) -> Result<Self, Self::Error> {
        Self::from_size_align(value.size(), value.align())
    }
}

impl From<PageLayout> for Layout {
    #[inline]
    fn from(value: PageLayout) -> Self {
        value.0
    }
}
