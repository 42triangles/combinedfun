use std::ops::{Bound, RangeBounds};

/// The kind of error that can happen with `Parser::or`(crate::Parser::or).
pub trait AltError<I> {
    fn alt(self, other: Self, at: I) -> Self;
}

impl<I> AltError<I> for () {
    fn alt(self, _: (), _: I) { }
}

/// Implemented for types that can be tags of the input `I`.
pub trait Tag<I> {
    type Output;

    /// The return type is reversed, since the tag is the beginning of the input.
    fn parse_tag(&self, inp: I) -> Option<(Self::Output, I)>;
}

impl<'a> Tag<&'a str> for str {
    type Output = &'a str;

    fn parse_tag(&self, inp: &'a str) -> Option<(&'a str, &'a str)> {
        if inp.starts_with(self) {
            Some(inp.split_at(self.len()))
        } else {
            None
        }
    }
}

impl<'a, T> Tag<&'a [T]> for [T] where T: PartialEq {
    type Output = &'a [T];

    fn parse_tag(&self, inp: &'a [T]) -> Option<(&'a [T], &'a [T])> {
        if inp.starts_with(self) {
            Some(inp.split_at(self.len()))
        } else {
            None
        }
    }
}

impl<'a> Tag<&'a [u8]> for str {
    type Output = &'a [u8];

    fn parse_tag(&self, inp: &'a [u8]) -> Option<(&'a [u8], &'a [u8])> {
        self.as_bytes().parse_tag(inp)
    }
}

/// The kind of error that can happen with `tag`(crate::tag).
pub trait TagError<'a, T: ?Sized, I> {
    fn tag(tag: &'a T, at: I) -> Self;
}

impl<'a, I, T: ?Sized> TagError<'a, T, I> for () {
    fn tag(_: &'a T, _: I) { }
}

/// This trait is implemented for all types that implement [`RangeBounds`](RangeBounds).
///
/// In most circumstances, you shouldn't implement it yourself, although there are certainly
/// applications.
pub trait RangeLike {
    fn can_continue(&self, n: usize) -> bool;
    fn has_to_continue(&self, n: usize) -> bool;

    /// The capacity the container should start with
    fn capacity(&self) -> usize {
        0
    }
}

fn continue_from_bound(n: usize, bound: Bound<&usize>, unbounded: bool) -> bool {
    match bound {
        Bound::Included(&stop) => n < stop,
        Bound::Excluded(&stop) => n + 1 < stop,
        Bound::Unbounded => unbounded,
    }
}

impl<T> RangeLike for T where T: RangeBounds<usize> {
    fn can_continue(&self, n: usize) -> bool {
        continue_from_bound(n, self.end_bound(), true)
    }

    fn has_to_continue(&self, n: usize) -> bool {
        continue_from_bound(n, self.start_bound(), false)
    }

    fn capacity(&self) -> usize {
        match self.end_bound() {
            Bound::Included(&n) => n,
            Bound::Excluded(&n) => n.saturating_sub(1),
            Bound::Unbounded => match self.start_bound() {
                Bound::Included(&n) => n,
                Bound::Excluded(&n) => n + 1,
                Bound::Unbounded => 0,
            }
        }
    }
}

/// This trait is implemented for collections you can push to.
pub trait Collection {
    type Item;

    fn reserve(&mut self, additional: usize);
    fn push(&mut self, index: usize, item: Self::Item);
}

impl<T> Collection for Vec<T> {
    type Item = T;

    fn reserve(&mut self, additional: usize) {
        self.reserve(additional);
    }

    fn push(&mut self, _: usize, item: Self::Item) {
        self.push(item);
    }
}

impl Collection for String {
    type Item = char;

    fn reserve(&mut self, additional: usize) {
        self.reserve(additional);
    }

    fn push(&mut self, _: usize, item: Self::Item) {
        self.push(item);
    }
}

impl<T> Collection for Option<T> {
    type Item = T;

    fn reserve(&mut self, additional: usize) {
        assert!(additional <= 1);
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

                fn reserve(&mut self, additional: usize) {
                    assert!(additional <= $n);
                }

                fn push(&mut self, index: usize, item: Self::Item) {
                    self[index] = item;
                }
            }
        )*
    };
}

collection_impl!(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32);

/// This trait allows checking if an input has reached its end.
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

/// The kind of error that can happen with `eof`(crate::eof).
pub trait EofError<I> {
    fn no_eof(at: I) -> Self;
}

impl<I> EofError<I> for () {
    fn no_eof(_: I) { }
}

/// The kind of error that can happen with `not`(crate::not).
pub trait NotError<O, I> {
    fn not(out: O, at: I) -> Self;
}

impl<O, I> NotError<O, I> for () {
    fn not(_: O, _: I) { }
}

/// This trait allows recording what part of an input was consumed by a parser.
pub trait Recordable {
    type Output;

    fn record(self, later: Self) -> Self::Output;
}

impl<'a> Recordable for &'a str {
    type Output = &'a str;

    fn record(self, later: &'a str) -> &'a str {
        &self[..(self.len() - later.len())]
    }
}

impl<'a, T> Recordable for &'a [T] {
    type Output = &'a [T];

    fn record(self, later: &'a [T]) -> &'a [T] {
        &self[..(self.len() - later.len())]
    }
}

/// This trait allows removing the first element from the input.
pub trait SplitFirst: Sized {
    type Element;

    fn split_first(self) -> Option<(Self::Element, Self)>;
}

impl<'a> SplitFirst for &'a str {
    type Element = char;

    fn split_first(self) -> Option<(char, &'a str)> {
        self.chars().next().map(|c| (c, &self[c.len_utf8()..]))
    }
}

impl<'a, T> SplitFirst for &'a [T] {
    type Element = &'a T;

    fn split_first(self) -> Option<(&'a T, &'a [T])> {
        self.iter().next().map(|x| (x, &self[1..]))
    }
}

/// The kind of error that can happen with `Parser::record_while`(crate::record_while).
pub trait ConsumeError<I: SplitFirst> {
    fn eof(at: I) -> Self;
    fn condition_failed(element: I::Element, at: I) -> Self;
}

impl<I: SplitFirst> ConsumeError<I> for () {
    fn eof(_: I) { }
    fn condition_failed(_: I::Element, _: I) { }
}

/// Used to track positions in a [`Span`](crate::types::Span).
pub trait Position<I>: Default {
    fn record_difference(&self, old: &I, new: &I) -> Self;
}
