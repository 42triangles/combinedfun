use std::marker::PhantomData;

use super::{AltError, Collection, ConsumeError, EofError, HasEof, NotError, Position, Recordable, SplitFirst, Tag, TagError};

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct NoCollection<T>(PhantomData<T>);

impl<T> Collection for NoCollection<T> {
    type Item = T;

    fn with_capacity(_: usize) -> Self {
        NoCollection(PhantomData)
    }

    fn push(&mut self, _: usize, _: Self::Item) { }
}

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

impl<I: Clone, P: Position<I>, T: Tag<I>> Tag<Span<I, P>> for T {
    type Output = <T as Tag<I>>::Output;

    fn parse_tag(&self, inp: Span<I, P>) -> Option<(Self::Output, Span<I, P>)> {
        self.parse_tag(inp.0.clone()).map(|(out, rest)| {
            let pos = inp.1.record_difference(&inp.0, &rest);
            (out, Span(rest, pos))
        })
    }
}

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

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Pos {
    pub line: usize,
    pub chars_in_line: usize,
    pub index: usize,
}

impl Default for Pos {
    fn default() -> Self {
        Pos {
            line: 0,
            chars_in_line: 0,
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
                out.chars_in_line = 0;
            } else {
                out.chars_in_line += 1;
            }
        }
        out
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum VerboseErrorKind<'a, I, O, T=I> {
    Alt(Box<[VerboseError<'a, I, O, T>;2]>),
    Tag(&'a T),
    NoEof,
    Not(O),
    Eof,
    ConditionFailed,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct VerboseError<'a, I, O, T=I> {
    pub kind: VerboseErrorKind<'a, I, O, T>,
    pub left: I,
}

impl<'a, I, O, T> VerboseError<'a, I, O, T> {
    fn new<OI>(kind: VerboseErrorKind<'a, I, O, T>, at: OI) -> Self where I: From<OI> {
        VerboseError {
            kind,
            left: at.into(),
        }
    }
}

impl<'a, OI, I, O, T> AltError<OI> for VerboseError<'a, I, O, T> where I: From<OI> {
    fn alt(self, other: Self, at: OI) -> Self {
        Self::new(VerboseErrorKind::Alt(Box::new([self, other])), at)
    }
}

impl<'a, OI, I, O, T> TagError<'a, T, OI> for VerboseError<'a, I, O, T> where I: From<OI> {
    fn tag(tag: &'a T, at: OI) -> Self {
        Self::new(VerboseErrorKind::Tag(tag), at)
    }
}

impl<'a, OI, I, O, T> EofError<OI> for VerboseError<'a, I, O, T> where I: From<OI> {
    fn no_eof(at: OI) -> Self {
        Self::new(VerboseErrorKind::NoEof, at)
    }
}

impl<'a, OO, OI, I, O, T> NotError<OO, OI> for VerboseError<'a, I, O, T> where I: From<OI>, O: From<OO> {
    fn not(out: OO, at: OI) -> Self {
        Self::new(VerboseErrorKind::Not(out.into()), at)
    }
}

impl<'a, OI: SplitFirst, I, O, T> ConsumeError<OI> for VerboseError<'a, I, O, T> where I: From<OI> {
    fn eof(at: OI) -> Self {
        Self::new(VerboseErrorKind::Eof, at)
    }

    fn condition_failed(_: OI::Element, at: OI) -> Self {
        Self::new(VerboseErrorKind::ConditionFailed, at)
    }
}
