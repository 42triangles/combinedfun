//! These combinators all correspond to one function (with some extra argument sometimes)

use std::marker::PhantomData;

use super::{AltError, Collection, MapResult as MapResultMarker, Parser, ParserImpl, RangeLike};

macro_rules! to_parser {
    ($e:expr) => { Parser::new(|inp| $e.apply(inp)) };
}

macro_rules! combine {
    ($inp:expr, |($($name:ident @ $e:expr),*)| $o:expr) => {
        {
            $(
                let $name = to_parser!($e);
            )*
            $o.parse_partial($inp)
        }
    };
}

pub struct Then<A, B>(pub(crate) A, pub(crate) B);

impl<I, A, B> ParserImpl<I> for Then<A, B> where A: ParserImpl<I>, B: ParserImpl<I, Error = A::Error> {
    type Output = (A::Output, B::Output);
    type Error = A::Error;

    fn apply(&self, inp: I) -> Result<(I, Self::Output), Self::Error> {
        self.0
            .apply(inp)
            .and_then(
                |(left, out1)| self.1
                                   .apply(left)
                                   .map(|(left, out2)| (left, (out1, out2)))
            )
    }
}

pub struct Or<A, B>(pub(crate) A, pub(crate) B);

impl<I, A, B> ParserImpl<I> for Or<A, B> where I: Clone, A: ParserImpl<I>, B: ParserImpl<I, Output = A::Output, Error = A::Error>, A::Error: AltError<I> {
    type Output = A::Output;
    type Error = A::Error;

    fn apply(&self, inp: I) -> Result<(I, Self::Output), Self::Error> {
        self.0.apply(inp.clone()).or_else(|e1| self.1.apply(inp.clone()).map_err(|e2| e1.alt(e2, inp)))
    }
}

pub struct CountedSeparated<C, R, F1, F2>(pub(crate) F1, pub(crate) F2, pub(crate) R, pub(crate) PhantomData<fn() -> C>);

impl<I, C, R, F1, F2> ParserImpl<I> for CountedSeparated<C, R, F1, F2> where I: Clone, C: Collection<Item = F1::Output>, R: RangeLike, F1: ParserImpl<I>, F2: ParserImpl<I, Error = F1::Error> {
    type Output = (C, usize);
    type Error = F1::Error;

    fn apply(&self, inp: I) -> Result<(I, Self::Output), Self::Error> {
        let element = to_parser!(self.0);
        let separator = to_parser!(self.1);
        let range = &self.2;

        let with_separator = separator.before(element.borrowed());

        let mut out = C::with_capacity(range.capacity());

        let mut count = 0;
        let mut left = inp;
        let mut first = true;

        macro_rules! parts {
            {$(while $cond:ident { $out:ident => $inner:expr })*} => {
                $(
                    while range.$cond(count) {
                        let (new_left, item) = {
                            let $out = if first {
                                first = false;
                                element.parse_partial(left.clone())
                            } else {
                                with_separator.parse_partial(left.clone())
                            };
                            $inner
                        };
                        left = new_left;
                        out.push(count, item);
                        count += 1;
                    }
                )*
            }
        }

        parts!{
            while has_to_continue {
                out => out?
            }

            while can_continue {
                out => match out {
                    Ok(next) => next,
                    Err(_) => break,
                }
            }
        }

        Ok((left, (out, count)))
    }
}

pub struct MapLeft<F>(pub(crate) F);

impl<I, O1, O2, F> ParserImpl<I> for MapLeft<F> where F: ParserImpl<I, Output = (O1, O2)> {
    type Output = O1;
    type Error = F::Error;

    fn apply(&self, inp: I) -> Result<(I, Self::Output), Self::Error> {
        combine!(inp, |(inner @ self.0)| inner.map(|(left, _)| left))
    }
}

pub struct MapRight<F>(pub(crate) F);

impl<I, O1, O2, F> ParserImpl<I> for MapRight<F> where F: ParserImpl<I, Output = (O1, O2)> {
    type Output = O2;
    type Error = F::Error;

    fn apply(&self, inp: I) -> Result<(I, Self::Output), Self::Error> {
        combine!(inp, |(inner @ self.0)| inner.map(|(_, right)| right))
    }
}

pub struct Epsilon<E>(pub(crate) PhantomData<fn() -> E>);

impl<I, E> ParserImpl<I> for Epsilon<E> {
    type Output = ();
    type Error = E;

    fn apply(&self, inp: I) -> Result<(I, ()), E> {
        Ok((inp, ()))
    }
}

pub struct Map<F1, F2>(pub(crate) F1, pub(crate) F2);

impl<I, F1, F2, O> ParserImpl<I> for Map<F1, F2> where F1: ParserImpl<I>, F2: Fn(F1::Output) -> O {
    type Output = O;
    type Error = F1::Error;

    fn apply(&self, inp: I) -> Result<(I, O), Self::Error> {
        combine!(inp, |(inner @ self.0)| inner >> MapResultMarker(|out| Ok(self.1(out))))
    }
}

pub struct MapResult<F1, F2>(pub(crate) F1, pub(crate) F2);

impl<I, F1, F2, O> ParserImpl<I> for MapResult<F1, F2> where F1: ParserImpl<I>, F2: Fn(F1::Output) -> Result<O, F1::Error> {
    type Output = O;
    type Error = F1::Error;

    fn apply(&self, inp: I) -> Result<(I, O), Self::Error> {
        self.0.apply(inp).and_then(|(left, out)| self.1(out).map(|new_out| (left, new_out)))
    }
}
