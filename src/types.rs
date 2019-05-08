use super::{HasEof, Position, Recordable, SplitFirst, Tag};

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
