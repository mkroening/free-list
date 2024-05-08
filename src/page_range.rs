use core::cmp::Ordering;
use core::fmt;
use core::num::NonZeroUsize;
use core::ops::{Add, Range, Sub};

use align_address::{usize_align_up, usize_is_aligned_to};

use crate::{PageLayout, PAGE_SIZE};

/// Invalid parameters in [`PageRange`] construction.
#[non_exhaustive]
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct PageRangeError;

impl fmt::Display for PageRangeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("invalid parameters to PageLayout::new")
    }
}

/// A non-empty page-aligned memory range.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct PageRange {
    start: usize,
    end: NonZeroUsize,
}

impl PageRange {
    /// Constructs a new `PageRange` from a given `start` and `end`,
    /// or returns `PageRangeError` if any of the following conidtions
    /// are not met:
    ///
    /// * `start` must be smaller than `end`,
    ///
    /// * `start` and `end` must be aligned to [`PAGE_SIZE`].
    ///
    /// # Examples
    ///
    /// ```
    /// use free_list::PageRange;
    ///
    /// let range = PageRange::new(0x1000, 0x5000).unwrap();
    /// ```
    pub const fn new(start: usize, end: usize) -> Result<Self, PageRangeError> {
        if start >= end {
            return Err(PageRangeError);
        }

        if !usize_is_aligned_to(start, PAGE_SIZE) {
            return Err(PageRangeError);
        }

        if !usize_is_aligned_to(end, PAGE_SIZE) {
            return Err(PageRangeError);
        }

        let end = match NonZeroUsize::new(end) {
            Some(end) => end,
            None => unreachable!(),
        };

        Ok(Self { start, end })
    }

    /// Constructs a new `PageRange` from a given `start` and `end`,
    /// or returns `PageRangeError` if any of the following conidtions
    /// are not met:
    ///
    /// * `len` must not be zero,
    ///
    /// * `start` and `len` must be aligned to [`PAGE_SIZE`],
    ///
    /// * `start + len` must not overflow.
    ///
    /// # Examples
    ///
    /// ```
    /// use free_list::PageRange;
    ///
    /// let range = PageRange::from_start_len(0x1000, 0x4000).unwrap();
    /// ```
    pub const fn from_start_len(start: usize, len: usize) -> Result<Self, PageRangeError> {
        let end = match start.checked_add(len) {
            Some(end) => end,
            None => return Err(PageRangeError),
        };
        Self::new(start, end)
    }

    /// Returns the start address of this page range.
    ///
    /// # Examples
    ///
    /// ```
    /// use free_list::PageRange;
    ///
    /// let range = PageRange::new(0x1000, 0x5000).unwrap();
    /// assert_eq!(range.start(), 0x1000);
    /// ```
    pub const fn start(self) -> usize {
        self.start
    }

    /// Returns the end address of this page range.
    ///
    /// # Examples
    ///
    /// ```
    /// use free_list::PageRange;
    ///
    /// let range = PageRange::new(0x1000, 0x5000).unwrap();
    /// assert_eq!(range.end(), 0x5000);
    /// ```
    pub const fn end(self) -> usize {
        self.end.get()
    }

    /// Returns the length of this page range in bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use free_list::PageRange;
    ///
    /// let range = PageRange::new(0x1000, 0x5000).unwrap();
    /// assert_eq!(range.len().get(), 0x4000);
    /// ```
    pub const fn len(self) -> NonZeroUsize {
        match NonZeroUsize::new(self.end() - self.start) {
            Some(len) => len,
            None => unreachable!(),
        }
    }

    /// Returns the length of this page range in pages of size [`PAGE_SIZE`].
    ///
    /// # Examples
    ///
    /// ```
    /// use free_list::PageRange;
    ///
    /// let range = PageRange::new(0x1000, 0x5000).unwrap();
    /// assert_eq!(range.pages().get(), 4);
    /// ```
    pub const fn pages(self) -> NonZeroUsize {
        match NonZeroUsize::new(self.len().get() / PAGE_SIZE) {
            Some(pages) => pages,
            None => unreachable!(),
        }
    }

    /// Returns true if `self` overlaps with `other`.
    ///
    /// This property is exclusive with [`PageRange::touches`].
    ///
    /// # Examples
    ///
    /// ```
    /// use free_list::PageRange;
    ///
    /// let a = PageRange::new(0x1000, 0x5000).unwrap();
    /// let b = PageRange::new(0x3000, 0x7000).unwrap();
    /// assert!(a.overlaps(b));
    /// ```
    pub const fn overlaps(self, other: Self) -> bool {
        self.end() > other.start && self.start < other.end()
    }

    /// Returns true if `self` touches `other`.
    ///
    /// This is exclusive with [`PageRange::overlaps`].
    ///
    /// # Examples
    ///
    /// ```
    /// use free_list::PageRange;
    ///
    /// let a = PageRange::new(0x1000, 0x5000).unwrap();
    /// let b = PageRange::new(0x5000, 0x9000).unwrap();
    /// assert!(a.touches(b));
    /// ```
    pub const fn touches(self, other: Self) -> bool {
        self.end() == other.start || self.start == other.end()
    }

    /// Returns true if `self` contains `other`.
    ///
    /// # Examples
    ///
    /// ```
    /// use free_list::PageRange;
    ///
    /// let a = PageRange::new(0x1000, 0x5000).unwrap();
    /// let b = PageRange::new(0x1000, 0x3000).unwrap();
    /// assert!(a.contains(b));
    /// ```
    pub const fn contains(self, other: Self) -> bool {
        self.start <= other.start && self.end() >= other.end()
    }

    /// Returns the first page range that is contained in `self` and satisfies `layout`.
    ///
    /// # Examples
    ///
    /// ```
    /// use free_list::{PageLayout, PageRange};
    ///
    /// let range = PageRange::new(0x1000, 0x5000).unwrap();
    /// let layout = PageLayout::from_size_align(0x3000, 0x2000).unwrap();
    /// let expected = PageRange::new(0x2000, 0x5000).unwrap();
    /// assert_eq!(range.fit(layout), Some(expected));
    /// ```
    pub const fn fit(self, layout: PageLayout) -> Option<PageRange> {
        let start = usize_align_up(self.start, layout.align());
        let range = match Self::from_start_len(start, layout.size()) {
            Ok(range) => range,
            Err(_) => unreachable!(),
        };
        if self.contains(range) {
            Some(range)
        } else {
            None
        }
    }
}

impl TryFrom<Range<usize>> for PageRange {
    type Error = PageRangeError;

    fn try_from(value: Range<usize>) -> Result<Self, Self::Error> {
        Self::new(value.start, value.end)
    }
}

impl fmt::Debug for PageRange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.start.fmt(f)?;
        f.write_str("..")?;
        self.end.fmt(f)?;
        Ok(())
    }
}

impl fmt::Display for PageRange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { start, end } = self;
        let len = self.len();
        let pages = self.pages();
        if f.alternate() {
            write!(
                f,
                "{start:#18x}..{end:#18x} (len = {len:#18x}, pages = {pages:16})"
            )
        } else {
            write!(f, "{start:#x}..{end:#x} (len = {len:#x}, pages = {pages})")
        }
    }
}

impl PartialOrd for PageRange {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self.end() <= other.start {
            Some(Ordering::Less)
        } else if self.start >= other.end() {
            Some(Ordering::Greater)
        } else if self == other {
            Some(Ordering::Equal)
        } else {
            None
        }
    }
}

impl Add for PageRange {
    type Output = Option<Self>;

    fn add(self, rhs: Self) -> Self::Output {
        if !(self.touches(rhs) || self.overlaps(rhs)) {
            return None;
        }

        Some(PageRange::new(self.start.min(rhs.start), self.end().max(rhs.end())).unwrap())
    }
}

impl Sub for PageRange {
    type Output = PageRangeSub;

    fn sub(self, rhs: Self) -> Self::Output {
        if !self.overlaps(rhs) {
            return PageRangeSub::One(self);
        }

        let before = PageRange::new(self.start, rhs.start).ok();
        let after = PageRange::new(rhs.end(), self.end()).ok();

        match (before, after) {
            (None, None) => PageRangeSub::None,
            (None, Some(range)) | (Some(range), None) => PageRangeSub::One(range),
            (Some(a), Some(b)) => PageRangeSub::Two(a, b),
        }
    }
}

/// The output of [`PageRange::sub`].
pub enum PageRangeSub {
    /// The result is empty.
    None,

    /// The result contains one page range.
    One(PageRange),

    /// The result contains two page ranges.
    Two(PageRange, PageRange),
}

#[cfg(test)]
mod tests {
    use core::alloc::Layout;

    use super::*;

    #[test]
    fn niche() {
        assert_eq!(
            Layout::new::<Option<PageRange>>(),
            Layout::new::<PageRange>()
        );
    }

    #[test]
    fn overlaps() {
        let assert = |a, b, c: bool| {
            let a = PageRange::try_from(a).unwrap();
            let b = PageRange::try_from(b).unwrap();
            assert_eq!(c, a.overlaps(b), "{a}.overlaps({b})");
        };

        assert(0x2000..0x5000, 0x0000..0x1000, false);
        assert(0x2000..0x5000, 0x0000..0x2000, false);
        assert(0x2000..0x5000, 0x0000..0x3000, true);
        assert(0x2000..0x5000, 0x0000..0x4000, true);
        assert(0x2000..0x5000, 0x0000..0x5000, true);
        assert(0x2000..0x5000, 0x0000..0x6000, true);
        assert(0x2000..0x5000, 0x0000..0x7000, true);
        assert(0x2000..0x5000, 0x0000..0x7000, true);
        assert(0x2000..0x5000, 0x1000..0x7000, true);
        assert(0x2000..0x5000, 0x2000..0x7000, true);
        assert(0x2000..0x5000, 0x3000..0x7000, true);
        assert(0x2000..0x5000, 0x4000..0x7000, true);
        assert(0x2000..0x5000, 0x5000..0x7000, false);
        assert(0x2000..0x5000, 0x6000..0x7000, false);
    }

    #[test]
    fn add() {
        let assert = |a, b, c: Option<Range<usize>>| {
            let a = PageRange::try_from(a).unwrap();
            let b = PageRange::try_from(b).unwrap();
            let c = c.map(|range| PageRange::try_from(range).unwrap());
            assert_eq!(c, a + b, "{a} + {b}");
        };

        assert(0x2000..0x5000, 0x0000..0x1000, None);
        assert(0x2000..0x5000, 0x0000..0x2000, Some(0x0000..0x5000));
        assert(0x2000..0x5000, 0x0000..0x3000, Some(0x0000..0x5000));
        assert(0x2000..0x5000, 0x0000..0x4000, Some(0x0000..0x5000));
        assert(0x2000..0x5000, 0x0000..0x5000, Some(0x0000..0x5000));
        assert(0x2000..0x5000, 0x0000..0x6000, Some(0x0000..0x6000));
        assert(0x2000..0x5000, 0x0000..0x7000, Some(0x0000..0x7000));
        assert(0x2000..0x5000, 0x1000..0x7000, Some(0x1000..0x7000));
        assert(0x2000..0x5000, 0x2000..0x7000, Some(0x2000..0x7000));
        assert(0x2000..0x5000, 0x3000..0x7000, Some(0x2000..0x7000));
        assert(0x2000..0x5000, 0x4000..0x7000, Some(0x2000..0x7000));
        assert(0x2000..0x5000, 0x5000..0x7000, Some(0x2000..0x7000));
        assert(0x2000..0x5000, 0x6000..0x7000, None);

        assert(0x2000..0x5000, 0x2000..0x3000, Some(0x2000..0x5000));
        assert(0x2000..0x5000, 0x2000..0x4000, Some(0x2000..0x5000));
        assert(0x2000..0x5000, 0x2000..0x5000, Some(0x2000..0x5000));
        assert(0x2000..0x5000, 0x3000..0x5000, Some(0x2000..0x5000));
        assert(0x2000..0x5000, 0x4000..0x5000, Some(0x2000..0x5000));

        assert(0x2000..0x5000, 0x3000..0x4000, Some(0x2000..0x5000));
    }

    #[allow(clippy::single_range_in_vec_init)]
    #[test]
    fn sub() {
        let assert = |a, b, c: &[Range<usize>]| {
            let a = PageRange::try_from(a).unwrap();
            let b = PageRange::try_from(b).unwrap();
            let c = c
                .iter()
                .cloned()
                .map(|range| PageRange::try_from(range).unwrap())
                .collect::<Vec<_>>();
            let v = match a - b {
                PageRangeSub::None => vec![],
                PageRangeSub::One(a) => vec![a],
                PageRangeSub::Two(a, b) => vec![a, b],
            };
            assert_eq!(c, v, "{a} - {b}");
        };

        assert(0x2000..0x5000, 0x0000..0x1000, &[0x2000..0x5000]);
        assert(0x2000..0x5000, 0x0000..0x2000, &[0x2000..0x5000]);
        assert(0x2000..0x5000, 0x0000..0x3000, &[0x3000..0x5000]);
        assert(0x2000..0x5000, 0x0000..0x4000, &[0x4000..0x5000]);
        assert(0x2000..0x5000, 0x0000..0x5000, &[]);
        assert(0x2000..0x5000, 0x0000..0x6000, &[]);
        assert(0x2000..0x5000, 0x0000..0x7000, &[]);
        assert(0x2000..0x5000, 0x1000..0x7000, &[]);
        assert(0x2000..0x5000, 0x2000..0x7000, &[]);
        assert(0x2000..0x5000, 0x3000..0x7000, &[0x2000..0x3000]);
        assert(0x2000..0x5000, 0x4000..0x7000, &[0x2000..0x4000]);
        assert(0x2000..0x5000, 0x5000..0x7000, &[0x2000..0x5000]);
        assert(0x2000..0x5000, 0x6000..0x7000, &[0x2000..0x5000]);

        assert(0x2000..0x5000, 0x2000..0x3000, &[0x3000..0x5000]);
        assert(0x2000..0x5000, 0x2000..0x4000, &[0x4000..0x5000]);
        assert(0x2000..0x5000, 0x2000..0x5000, &[]);
        assert(0x2000..0x5000, 0x3000..0x5000, &[0x2000..0x3000]);
        assert(0x2000..0x5000, 0x4000..0x5000, &[0x2000..0x4000]);

        assert(
            0x2000..0x5000,
            0x3000..0x4000,
            &[0x2000..0x3000, 0x4000..0x5000],
        );
    }
}
