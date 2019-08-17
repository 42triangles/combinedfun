use std::marker::PhantomData;

use super::{AltError, Collection, ConsumeError, EofError, HasEof, NotError, Position, Recordable, SplitFirst, Tag, TagError};

/// Used to not store the elements in repeating parsers.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct NoCollection<T>(PhantomData<T>);

impl<T> NoCollection<T> {
    pub fn new() -> Self {
        NoCollection(PhantomData)
    }
}

impl<T> Collection for NoCollection<T> {
    type Item = T;

    fn reserve(&mut self, _: usize) { }

    fn push(&mut self, _: usize, _: Self::Item) { }
}

/// Used as a wrapper to some container implementing [`Extend`](std::iter::Extend).
///
/// This is not recommended right now, since it always just pushes a single element, and can't
/// reserve items beforehand.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct ExtendCollection<T, I>(T, PhantomData<fn(I)>);

impl<T, I> ExtendCollection<T, I> {
    pub fn new(empty: T) -> Self {
        ExtendCollection(empty, PhantomData)
    }
}

impl<T, I> Collection for ExtendCollection<T, I>
where T: Extend<I> {
    type Item = I;

    fn reserve(&mut self, _: usize) { }

    fn push(&mut self, _: usize, item: Self::Item) {
        self.0.extend(std::iter::once(item))
    }
}

/// This input type keeps track of the position within the input it wraps.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Span<I, P>(pub I, pub P);

impl<I, P: Position<I>> Span<I, P> {
    pub fn new(input: I) -> Self {
        Span(input, P::default())
    }
}

impl<I: HasEof, P> HasEof for Span<I, P> {
    fn at_eof(&self) -> bool {
        self.0.at_eof()
    }
}

impl<I: Recordable, P> Recordable for Span<I, P> {
    type Output = I::Output;

    fn record(self, later: Self) -> Self::Output {
        self.0.record(later.0)
    }
}

impl<I: Clone + SplitFirst, P: Position<I>> SplitFirst for Span<I, P> {
    type Element = I::Element;

    fn split_first(self) -> Option<(Self::Element, Self)> {
        let Span(input, pos) = self;
        let old_input = input.clone();
        input.split_first().map(|(el, rest)| {
            let pos = pos.record_difference(&old_input, &rest);
            (el, Span(rest, pos))
        })
    }
}

impl<I: Clone, P: Position<I>, T: Tag<I> + ?Sized> Tag<Span<I, P>> for T {
    type Output = <T as Tag<I>>::Output;

    fn parse_tag(&self, inp: Span<I, P>) -> Option<(Self::Output, Span<I, P>)> {
        self.parse_tag(inp.0.clone()).map(|(out, rest)| {
            let pos = inp.1.record_difference(&inp.0, &rest);
            (out, Span(rest, pos))
        })
    }
}

/// This position type only keeps track of the index.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Index(pub usize);

impl Default for Index {
    fn default() -> Self {
        Index(0)
    }
}

impl<'a> Position<&'a str> for Index {
    fn record_difference(&self, old: &&'a str, new: &&'a str) -> Self {
        Index(self.0 + (old.len() - new.len()))
    }
}

impl<'a, T> Position<&'a [T]> for Index {
    fn record_difference(&self, old: &&'a [T], new: &&'a [T]) -> Self {
        Index(self.0 + (old.len() - new.len()))
    }
}

/// This position type keeps track of the line, column and index.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Pos {
    pub line: usize,
    pub column: usize,
    pub index: usize,
}

impl Default for Pos {
    fn default() -> Self {
        Pos {
            line: 0,
            column: 0,
            index: 0,
        }
    }
}

impl<'a> Position<&'a str> for Pos {
    fn record_difference(&self, old: &&'a str, new: &&'a str) -> Self {
        let mut out = Pos {
            index: self.index + (old.len() - new.len()),
            ..*self
        };
        for i in old[..(old.len() - new.len())].chars() {
            if i == '\n' {
                out.line += 1;
                out.column = 0;
            } else {
                out.column += 1;
            }
        }
        out
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum VerboseErrorKind<'a, I, O, T: ?Sized> {
    Alt(Box<[VerboseError<'a, I, O, T>;2]>),
    Tag(&'a T),
    NoEof,
    Not(O),
    Eof,
    ConditionFailed,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct VerboseError<'a, I, O, T: ?Sized> {
    pub kind: VerboseErrorKind<'a, I, O, T>,
    pub left: I,
}

impl<'a, I, O, T: ?Sized> VerboseError<'a, I, O, T> {
    fn new<OI>(kind: VerboseErrorKind<'a, I, O, T>, at: OI) -> Self where I: From<OI> {
        VerboseError {
            kind,
            left: at.into(),
        }
    }
}

impl<'a, OI, I, O, T: ?Sized> AltError<OI> for VerboseError<'a, I, O, T> where I: From<OI> {
    fn alt(self, other: Self, at: OI) -> Self {
        Self::new(VerboseErrorKind::Alt(Box::new([self, other])), at)
    }
}

impl<'a, OI, I, O, T: ?Sized> TagError<'a, T, OI> for VerboseError<'a, I, O, T> where I: From<OI> {
    fn tag(tag: &'a T, at: OI) -> Self {
        Self::new(VerboseErrorKind::Tag(tag), at)
    }
}

impl<'a, OI, I, O, T: ?Sized> EofError<OI> for VerboseError<'a, I, O, T> where I: From<OI> {
    fn no_eof(at: OI) -> Self {
        Self::new(VerboseErrorKind::NoEof, at)
    }
}

impl<'a, OO, OI, I, O, T: ?Sized> NotError<OO, OI> for VerboseError<'a, I, O, T> where I: From<OI>, O: From<OO> {
    fn not(out: OO, at: OI) -> Self {
        Self::new(VerboseErrorKind::Not(out.into()), at)
    }
}

impl<'a, OI: SplitFirst, I, O, T: ?Sized> ConsumeError<OI> for VerboseError<'a, I, O, T> where I: From<OI> {
    fn eof(at: OI) -> Self {
        Self::new(VerboseErrorKind::Eof, at)
    }

    fn condition_failed(_: OI::Element, at: OI) -> Self {
        Self::new(VerboseErrorKind::ConditionFailed, at)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct PositionedError<P, E> {
    pub position: P,
    pub error: E,
}

impl<P, E> PositionedError<P, E> {
    pub fn new(position: P, error: E) -> Self {
        PositionedError {
            position,
            error,
        }
    }
}

impl<I, P: Position<I>, E: AltError<I>> AltError<Span<I, P>> for PositionedError<P, E> {
    fn alt(self, other: Self, at: Span<I, P>) -> Self {
        Self::new(at.1, self.error.alt(other.error, at.0))
    }
}

impl<'a, I, P: Position<I>, E, T: ?Sized> TagError<'a, T, Span<I, P>> for PositionedError<P, E>
where E: TagError<'a, T, I> {
    fn tag(tag: &'a T, at: Span<I, P>) -> Self {
        Self::new(at.1, E::tag(tag, at.0))
    }
}

impl<I, P: Position<I>, E: EofError<I>> EofError<Span<I, P>> for PositionedError<P, E> {
    fn no_eof(at: Span<I, P>) -> Self {
        Self::new(at.1, E::no_eof(at.0))
    }
}

impl<I, P: Position<I>, E: NotError<O, I>, O> NotError<O, Span<I, P>> for PositionedError<P, E> {
    fn not(out: O, at: Span<I, P>) -> Self {
        Self::new(at.1, E::not(out, at.0))
    }
}

impl<I: SplitFirst + Clone, P: Position<I>, E> ConsumeError<Span<I, P>> for PositionedError<P, E>
where E: ConsumeError<I> {
    fn eof(at: Span<I, P>) -> Self {
        Self::new(at.1, E::eof(at.0))
    }

    fn condition_failed(element: I::Element, at: Span<I, P>) -> Self {
        Self::new(at.1, E::condition_failed(element, at.0))
    }
}
