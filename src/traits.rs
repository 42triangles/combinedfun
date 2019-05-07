use std::marker::PhantomData;
use std::ops::{Bound, RangeBounds};

pub trait AltError {
    fn alt(self, other: Self) -> Self;
}

impl AltError for () {
    fn alt(self, _: ()) { }
}

pub trait Tag<I> {
    fn parse_tag(&self, inp: I) -> Option<(I, I)>;
}

impl<'a> Tag<&'a str> for str {
    fn parse_tag(&self, inp: &'a str) -> Option<(&'a str, &'a str)> {
        if inp.starts_with(self) {
            Some(inp.split_at(self.len()))
        } else {
            None
        }
    }
}

impl<'a, T> Tag<&'a [T]> for [T] where T: PartialEq {
    fn parse_tag(&self, inp: &'a [T]) -> Option<(&'a [T], &'a [T])> {
        if inp.starts_with(self) {
            Some(inp.split_at(self.len()))
        } else {
            None
        }
    }
}

impl<'a> Tag<&'a [u8]> for str {
    fn parse_tag(&self, inp: &'a [u8]) -> Option<(&'a [u8], &'a [u8])> {
        self.as_bytes().parse_tag(inp)
    }
}

pub trait TagError<'a, T> {
    fn tag(tag: &'a T) -> Self;
}

impl<'a, T> TagError<'a, T> for () {
    fn tag(_: &'a T) { }
}

pub trait RangeLike {
    fn can_continue(&self, n: usize) -> bool;
    fn has_to_continue(&self, n: usize) -> bool;
    fn capacity(&self) -> usize;
}

fn continue_from_bound(n: usize, bound: Bound<&usize>) -> bool {
    match bound {
        Bound::Included(&stop) => n <= stop,
        Bound::Excluded(&stop) => n < stop,
        Bound::Unbounded => true,
    }
}

fn bound_to_option(bound: Bound<&usize>) -> Option<usize> {
    match bound {
        Bound::Included(&stop) => Some(stop),
        Bound::Excluded(&stop) => Some(stop.saturating_sub(1)),
        Bound::Unbounded => None,
    }
}

impl<T> RangeLike for T where T: RangeBounds<usize> {
    fn can_continue(&self, n: usize) -> bool {
        continue_from_bound(n, self.end_bound())
    }

    fn has_to_continue(&self, n: usize) -> bool {
        continue_from_bound(n, self.start_bound())
    }

    fn capacity(&self) -> usize {
        bound_to_option(self.end_bound()).or_else(|| bound_to_option(self.start_bound())).unwrap_or(0)
    }
}

pub trait Collection {
    type Item;

    fn with_capacity(capacity: usize) -> Self;
    fn push(&mut self, index: usize, item: Self::Item);
}

impl<T> Collection for Vec<T> {
    type Item = T;

    fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity(capacity)
    }

    fn push(&mut self, _: usize, item: Self::Item) {
        self.push(item);
    }
}

impl<T> Collection for Option<T> {
    type Item = T;

    fn with_capacity(capacity: usize) -> Self {
        assert!(capacity <= 1);
        None
    }

    fn push(&mut self, _: usize, item: Self::Item) {
        *self = Some(item);
    }
}

macro_rules! collection_impl {
    ($($n:literal)*) => {
        $(
            impl<T> Collection for [T;$n] where T: Default {
                type Item = T;

                fn with_capacity(capacity: usize) -> Self {
                    assert!(capacity <= $n);
                    Self::default()
                }

                fn push(&mut self, index: usize, item: Self::Item) {
                    self[index] = item;
                }
            }
        )*
    };
}

collection_impl!(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32);

pub(crate) struct NoCollection<T>(PhantomData<T>);

impl<T> Collection for NoCollection<T> {
    type Item = T;

    fn with_capacity(_: usize) -> Self {
        NoCollection(PhantomData)
    }

    fn push(&mut self, _: usize, _: Self::Item) { }
}

pub trait HasEof {
    fn at_eof(&self) -> bool;
}

impl<'a> HasEof for &'a str {
    fn at_eof(&self) -> bool {
        self.is_empty()
    }
}

impl<'a, T> HasEof for &'a [T] {
    fn at_eof(&self) -> bool {
        self.is_empty()
    }
}

pub trait EofError {
    fn no_eof() -> Self;
}

impl EofError for () {
    fn no_eof() { }
}

pub trait NotError<O> {
    fn not(out: O) -> Self;
}

impl<O> NotError<O> for () {
    fn not(_: O) { }
}
