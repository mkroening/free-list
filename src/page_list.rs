use core::fmt::Write;
use core::{fmt, iter, slice};

use smallvec::SmallVec;

use crate::{PageRange, PageRangeSub};

#[derive(Clone, Debug)]
pub struct PageList<const N: usize> {
    list: SmallVec<[PageRange; N]>,
}

#[derive(Debug)]
pub struct PageListError;

impl<const N: usize> PageList<N> {
    pub const fn new() -> Self {
        Self {
            list: SmallVec::new_const(),
        }
    }

    pub fn iter(&self) -> iter::Copied<slice::Iter<'_, PageRange>> {
        self.list.iter().copied()
    }

    fn is_consistent(&self) -> bool {
        self.list
            .windows(2)
            .all(|window| window[0].end() < window[1].start())
    }

    pub(crate) fn add_at(&mut self, index: usize, range: PageRange) -> Result<(), PageListError> {
        let (prev, next) = self.list.split_at_mut(index);
        let prev = prev.last_mut();
        let next = next.first_mut();

        match (prev, next) {
            (Some(prev), Some(next)) => {
                let touches_prev = range.touches(*prev).then_some(prev);
                let touches_next = range.touches(*next).then_some(next);
                match (touches_prev, touches_next) {
                    (Some(prev), Some(next)) => {
                        *prev = ((*prev + range).unwrap() + *next).unwrap();
                        self.list.remove(index);
                    }
                    (Some(adj), None) | (None, Some(adj)) => *adj = (*adj + range).unwrap(),
                    (None, None) => self.list.insert(index, range),
                }
            }
            (Some(adj), None) | (None, Some(adj)) => {
                if let Some(sum) = *adj + range {
                    *adj = sum;
                } else {
                    self.list.insert(index, range);
                }
            }
            (None, None) => self.list.insert(index, range),
        }

        debug_assert!(self.is_consistent());

        Ok(())
    }

    pub fn add(&mut self, range: PageRange) -> Result<(), PageListError> {
        if self.list.iter().any(|entry| entry.overlaps(range)) {
            return Err(PageListError);
        }

        let index = self
            .list
            .iter()
            .enumerate()
            .find_map(|(i, entry)| (range < *entry).then_some(i))
            .unwrap_or_else(|| self.list.len());

        self.add_at(index, range)?;

        Ok(())
    }

    pub(crate) fn remove_at(
        &mut self,
        index: usize,
        range: PageRange,
    ) -> Result<(), PageListError> {
        let entry = &mut self.list[index];

        match *entry - range {
            PageRangeSub::None => {
                self.list.remove(index);
            }
            PageRangeSub::One(a) => {
                *entry = a;
            }
            PageRangeSub::Two(a, b) => {
                *entry = a;
                self.list.insert(index + 1, b);
            }
        }

        debug_assert!(self.is_consistent());

        Ok(())
    }

    pub fn remove(&mut self, range: PageRange) -> Result<(), PageListError> {
        let Some(index) = self
            .list
            .iter_mut()
            .enumerate()
            .find_map(|(index, entry)| entry.contains(range).then_some(index))
        else {
            return Err(PageListError);
        };

        self.remove_at(index, range)?;

        Ok(())
    }
}

impl<const N: usize> Default for PageList<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const N: usize> fmt::Display for PageList<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut has_fields = false;

        for entry in &self.list {
            if has_fields {
                f.write_char('\n')?;
            }
            write!(f, "{entry:#}")?;

            has_fields = true;
        }
        Ok(())
    }
}

impl<const N: usize> IntoIterator for PageList<N> {
    type Item = PageRange;

    type IntoIter = smallvec::IntoIter<[Self::Item; N]>;

    fn into_iter(self) -> Self::IntoIter {
        self.list.into_iter()
    }
}

impl<'a, const N: usize> IntoIterator for &'a PageList<N> {
    type Item = PageRange;

    type IntoIter = iter::Copied<slice::Iter<'a, PageRange>>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[allow(clippy::single_range_in_vec_init)]
#[rustfmt::skip]
#[cfg(test)]
mod tests {
    use std::ops::Range;

    use super::*;

    #[test]
    fn add() {
        let assert = |a: &[Range<usize>], b: Range<usize>, c: &[Range<usize>]| {
            let a = a
                .iter()
                .cloned()
                .map(|range| PageRange::try_from(range).unwrap())
                .collect::<Vec<_>>();
            let b = PageRange::try_from(b).unwrap();
            let c = c
                .iter()
                .cloned()
                .map(|range| PageRange::try_from(range).unwrap())
                .collect::<Vec<_>>();
            let mut page_list = PageList::<16> { list: a.into() };
            page_list.add(b).unwrap();
            assert_eq!(page_list.list.to_vec(), c);
        };

        assert(&[], 0x2000..0x5000, &[0x2000..0x5000]);

        assert(&[0x0000..0x1000], 0x2000..0x5000, &[0x0000..0x1000, 0x2000..0x5000]);
        assert(&[0x0000..0x2000], 0x2000..0x5000, &[0x0000..0x5000]);
        assert(&[0x5000..0x7000], 0x2000..0x5000, &[0x2000..0x7000]);
        assert(&[0x6000..0x7000], 0x2000..0x5000, &[0x2000..0x5000, 0x6000..0x7000]);

        assert(&[0x0000..0x1000, 0x6000..0x7000], 0x2000..0x5000, &[0x0000..0x1000, 0x2000..0x5000, 0x6000..0x7000]);
        assert(&[0x0000..0x2000, 0x6000..0x7000], 0x2000..0x5000, &[0x0000..0x5000, 0x6000..0x7000]);
        assert(&[0x0000..0x1000, 0x5000..0x7000], 0x2000..0x5000, &[0x0000..0x1000, 0x2000..0x7000]);
        assert(&[0x0000..0x2000, 0x5000..0x7000], 0x2000..0x5000, &[0x0000..0x7000]);

        assert(&[0x0000..0x1000, 0x2000..0x3000, 0x6000..0x7000, 0x8000..0x9000], 0x4000..0x5000, &[0x0000..0x1000, 0x2000..0x3000, 0x4000..0x5000, 0x6000..0x7000, 0x8000..0x9000]);
        assert(&[0x0000..0x1000, 0x2000..0x4000, 0x6000..0x7000, 0x8000..0x9000], 0x4000..0x5000, &[0x0000..0x1000, 0x2000..0x5000, 0x6000..0x7000, 0x8000..0x9000]);
        assert(&[0x0000..0x1000, 0x2000..0x3000, 0x5000..0x7000, 0x8000..0x9000], 0x4000..0x5000, &[0x0000..0x1000, 0x2000..0x3000, 0x4000..0x7000, 0x8000..0x9000]);
        assert(&[0x0000..0x1000, 0x2000..0x4000, 0x5000..0x7000, 0x8000..0x9000], 0x4000..0x5000, &[0x0000..0x1000, 0x2000..0x7000, 0x8000..0x9000]);
    }

    #[test]
    fn remove() {
        let assert = |a: &[Range<usize>], b: Range<usize>, c: &[Range<usize>]| {
            let a = a
                .iter()
                .cloned()
                .map(|range| PageRange::try_from(range).unwrap())
                .collect::<Vec<_>>();
            let b = PageRange::try_from(b).unwrap();
            let c = c
                .iter()
                .cloned()
                .map(|range| PageRange::try_from(range).unwrap())
                .collect::<Vec<_>>();
            let mut page_list = PageList::<16> { list: a.into() };
            page_list.remove(b).unwrap();
            assert_eq!(page_list.list.to_vec(), c);
        };


        assert(&[0x2000..0x5000], 0x2000..0x5000, &[]);

        assert(&[0x0000..0x1000, 0x2000..0x5000], 0x2000..0x5000, &[0x0000..0x1000]);
        assert(&[0x0000..0x5000], 0x2000..0x5000, &[0x0000..0x2000]);
        assert(&[0x2000..0x7000], 0x2000..0x5000, &[0x5000..0x7000]);
        assert(&[0x2000..0x5000, 0x6000..0x7000], 0x2000..0x5000, &[0x6000..0x7000]);

        assert(&[0x0000..0x1000, 0x2000..0x5000, 0x6000..0x7000], 0x2000..0x5000, &[0x0000..0x1000, 0x6000..0x7000]);
        assert(&[0x0000..0x5000, 0x6000..0x7000], 0x2000..0x5000, &[0x0000..0x2000, 0x6000..0x7000]);
        assert(&[0x0000..0x1000, 0x2000..0x7000], 0x2000..0x5000, &[0x0000..0x1000, 0x5000..0x7000]);
        assert(&[0x0000..0x7000], 0x2000..0x5000, &[0x0000..0x2000, 0x5000..0x7000]);

        assert(&[0x0000..0x1000, 0x2000..0x3000, 0x4000..0x5000, 0x6000..0x7000, 0x8000..0x9000], 0x4000..0x5000, &[0x0000..0x1000, 0x2000..0x3000, 0x6000..0x7000, 0x8000..0x9000]);
        assert(&[0x0000..0x1000, 0x2000..0x5000, 0x6000..0x7000, 0x8000..0x9000], 0x4000..0x5000, &[0x0000..0x1000, 0x2000..0x4000, 0x6000..0x7000, 0x8000..0x9000]);
        assert(&[0x0000..0x1000, 0x2000..0x3000, 0x4000..0x7000, 0x8000..0x9000], 0x4000..0x5000, &[0x0000..0x1000, 0x2000..0x3000, 0x5000..0x7000, 0x8000..0x9000]);
        assert(&[0x0000..0x1000, 0x2000..0x7000, 0x8000..0x9000], 0x4000..0x5000, &[0x0000..0x1000, 0x2000..0x4000, 0x5000..0x7000, 0x8000..0x9000]);
    }
}
