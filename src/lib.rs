#![type_length_limit="1209804"]
use std::marker::PhantomData;

pub mod traits;
pub use traits::{AltError, Collection, ConsumeError, EofError, HasEof, NotError, Position, RangeLike, Recordable, SplitFirst, Tag, TagError};

pub mod types;
pub use types::{Index, NoCollection, Pos, Span};

#[cfg(test)]
mod tests;

pub trait ParserImpl<I> {
    type Output;
    type Error;

    fn apply(&self, inp: I) -> Result<(I, Self::Output), Self::Error>;
}

impl<F, I, O, E> ParserImpl<I> for F where F: Fn(I) -> Result<(I, O), E> {
    type Output = O;
    type Error = E;

    fn apply(&self, inp: I) -> Result<(I, O), E> {
        self(inp)
    }
}

pub struct Parser<F, I>(F, PhantomData<fn(I)>);

#[macro_export]
macro_rules! parser {
    (<$i:ty, $o:ty, $e:ty> + $lt:tt) => {
        Parser<impl ParserImpl<$i, Output = $o, Error = $e> + $lt, $i>
    };
    (<$i:ty, $o:ty, $e:ty>) => {
        Parser<impl ParserImpl<$i, Output = $o, Error = $e>, $i>
    };
}

#[macro_export]
macro_rules! parser_dbg {
    ($parser:expr) => {
        $parser.map_full(|rest, x| dbg!((rest, x)).1).map_err(|err| dbg!(err))
    }
}

// To appease the type inference
impl<F, I, O, E> Parser<F, I> where F: Fn(I) -> Result<(I, O), E> {
    pub fn new(func: F) -> Self {
        Self::new_generic(func)
    }
}

impl<F, I, O, E> Parser<F, I> where F: ParserImpl<I, Output = O, Error = E> {
    pub fn new_generic(implementation: F) -> Self {
        Parser(implementation, PhantomData)
    }

    pub fn then<O2, F2>(self, next: Parser<F2, I>) -> parser!(<I, (O, O2), E>)
    where F2: ParserImpl<I, Output = O2, Error = E> {
        Parser::new(move |input| self.0.apply(input).and_then(|(left, out1)| next.0.apply(left).map(|out2| (out2.0, (out1, out2.1)))))
    }

    pub fn before<O2, F2>(self, main: Parser<F2, I>) -> parser!(<I, O2, E>)
    where F2: ParserImpl<I, Output = O2, Error = E> {
        self.then(main).map(|(_, main_out)| main_out)
    }

    pub fn followed_by<F2>(self, next: Parser<F2, I>) -> parser!(<I, O, E>)
    where F2: ParserImpl<I, Error = E> {
        self.then(next).map(|(main_out, _)| main_out)
    }

    pub fn or<F2>(self, alt: Parser<F2, I>) -> parser!(<I, O, E>)
    where F2: ParserImpl<I, Output = O, Error = E>, I: Clone, E: AltError<I> {
        Parser::new(move |inp: I| self.0.apply(inp.clone()).or_else(|e1| alt.0.apply(inp.clone()).map_err(|e2| e1.alt(e2, inp))))
    }

    pub fn map_result<O2, F2>(self, f: F2) -> parser!(<I, O2, E>)
    where F2: Fn(O) -> Result<O2, E> {
        Parser::new(move |input| self.0.apply(input).and_then(|(l, o)| f(o).map(|new_o| (l, new_o))))
    }

    pub fn map<O2, F2>(self, f: F2) -> parser!(<I, O2, E>)
    where F2: Fn(O) -> O2 {
        self.map_result(move |o| Ok(f(o)))
    }

    pub fn map_err<E2, F2>(self, f: F2) -> parser!(<I, O, E2>)
    where F2: Fn(E) -> E2 {
        Parser::new(move |input| self.0.apply(input).map_err(|e| f(e)))
    }

    pub fn counted_separated<C, F2, R: RangeLike>(self, range: R, by: Parser<F2, I>) -> parser!(<I, (C, usize), E>)
    where F2: ParserImpl<I, Error = E>, C: Collection<Item = O>, I: Clone {
        Parser::new(move |input: I| {
            let with_by = by.borrowed().before(self.borrowed());

            let mut out = C::with_capacity(range.capacity());

            let mut count = 0;
            let mut left = input;
            let mut first = true;

            macro_rules! parts {
                {$(while $cond:ident { $out:ident => $inner:expr })*} => {
                    $(
                        while range.$cond(count) {
                            let (new_left, item) = {
                                let $out = if first {
                                    first = false;
                                    self.0.apply(left.clone())
                                } else {
                                    with_by.0.apply(left.clone())
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
        })
    }

    pub fn separated<C, F2, R: RangeLike>(self, range: R, by: Parser<F2, I>) -> parser!(<I, C, E>)
    where F2: ParserImpl<I, Error = E>, C: Collection<Item = O>, I: Clone {
        self.counted_separated(range, by).map(|(c, _)| c)
    }

    pub fn const_separated<C, F2>(self, n: usize, by: Parser<F2, I>) -> parser!(<I, C, E>)
    where F2: ParserImpl<I, Error = E>, C: Collection<Item = O>, I: Clone {
        self.separated(n..=n, by)
    }

    pub fn count_separated_within<R: RangeLike, F2>(self, range: R, by: Parser<F2, I>) -> parser!(<I, usize, E>)
    where F2: ParserImpl<I, Error = E>, I: Clone {
        self.counted_separated::<NoCollection<O>, _, _>(range, by).map(|(_, count)| count)
    }

    pub fn count_separated<F2>(self, by: Parser<F2, I>) -> parser!(<I, usize, E>)
    where F2: ParserImpl<I, Error = E>, I: Clone {
        self.count_separated_within(.., by)
    }

    pub fn counted_repeat<C, R: RangeLike>(self, range: R) -> parser!(<I, (C, usize), E>)
    where C: Collection<Item = O>, I: Clone {
        self.counted_separated(range, epsilon())
    }

    pub fn repeat<C, R: RangeLike>(self, range: R) -> parser!(<I, C, E>)
    where C: Collection<Item = O>, I: Clone {
        self.counted_repeat(range).map(|(c, _)| c)
    }

    pub fn const_repeat<C>(self, n: usize) -> parser!(<I, C, E>)
    where C: Collection<Item = O>, I: Clone {
        self.repeat(n..=n)
    }

    pub fn count_within<R: RangeLike>(self, range: R) -> parser!(<I, usize, E>)
    where I: Clone {
        self.counted_repeat::<NoCollection<O>, _>(range).map(|(_, count)| count)
    }

    pub fn count(self) -> parser!(<I, usize, E>)
    where I: Clone {
        self.count_within(..)
    }

    pub fn maybe(self) -> parser!(<I, Option<O>, E>)
    where I: Clone {
        self.repeat(0..=1)
    }

    pub fn ignore(self) -> parser!(<I, (), E>) {
        self.map(|_| ())
    }

    pub fn record(self) -> parser!(<I, I::Output, E>)
    where I: Clone + Recordable {
        Parser::new(move |inp: I| {
            let old = inp.clone();
            self.0.apply(inp).map(|(left, _)| (left.clone(), old.record(left)))
        })
    }

    pub fn convert_err<E2>(self) -> parser!(<I, O, E2>)
    where E2: From<E> {
        self.map_err(E2::from)
    }

    pub fn map_full<O2, F2>(self, f: F2) -> parser!(<I, O2, E>)
    where F2: Fn((&I, &I), O) -> O2, I: Clone {
        Parser::new(move |inp: I| {
            let inp_clone = inp.clone();
            self.0.apply(inp).map(|(left, out)| {
                let out = f((&inp_clone, &left), out);
                (left, out)
            })
        })
    }

    pub fn borrowed<'a>(&'a self) -> parser!(<I, O, E> + 'a) {
        Parser::new(move |inp| self.0.apply(inp))
    }

    pub fn parse_partial(&self, input: I) -> Result<(I, O), E> {
        self.0.apply(input)
    }

    pub fn parse(&self, input: I) -> Result<O, E>
    where I: HasEof, E: EofError<I> {
        self.borrowed().followed_by(eof()).parse_partial(input).map(|(_, o)| o)
    }

    pub fn get_inner(&self) -> &F {
        &self.0
    }

    pub fn move_inner(self) -> F {
        self.0
    }
}

pub type FnParser<I, O, E> = Parser<fn(I) -> Result<(I, O), E>, I>;

pub fn f<I, O, E>(func: fn(I) -> Result<(I, O), E>) -> FnParser<I, O, E> {
    Parser::new(func)
}

pub fn epsilon<I, E>() -> parser!(<I, (), E>) {
    Parser::new(|inp| Ok((inp, ())))
}

pub fn tag<'a, I, E, T: ?Sized>(tag: &'a T) -> parser!(<I, T::Output, E> + 'a)
where T: Tag<I>, E: TagError<'a, T, I>, I: Clone {
    Parser::new(move |inp: I| tag.parse_tag(inp.clone()).map(|(tag, rest)| (rest, tag)).ok_or_else(|| E::tag(tag, inp)))
}

pub fn fail_with<I, O, E, F>(f: F) -> parser!(<I, O, E>)
where F: Fn() -> E {
    Parser::new(move |_| Err(f()))
}

pub fn fail_with_const<I, O, E>(e: E) -> parser!(<I, O, E>)
where E: Clone {
    fail_with(move || e.clone())
}

pub fn eof<I, E>() -> parser!(<I, (), E>)
where I: HasEof, E: EofError<I> {
    Parser::new(move |inp: I| if inp.at_eof() {
        Ok((inp, ()))
    } else {
        Err(E::no_eof(inp))
    })
}

pub fn not<I, O, EO, E, F>(p: Parser<F, I>) -> parser!(<I, EO, E>)
where F: ParserImpl<I, Output = O, Error = EO>, E: NotError<O, I>, I: Clone {
    Parser::new(move |inp: I| match p.0.apply(inp.clone()) {
        Ok((_, out)) => Err(E::not(out, inp)),
        Err(err) => Ok((inp, err)),
    })
}

pub fn consume_one_where<I, E, F>(f: F) -> parser!(<I, I::Element, E>)
where I: SplitFirst + Clone, F: Fn(&I::Element) -> bool, E: ConsumeError<I> {
    Parser::new(move |inp: I| {
        match inp.clone().split_first() {
            Some((element, rest)) => if f(&element) {
                Ok((rest, element))
            } else {
                Err(E::condition_failed(element, inp))
            },
            None => Err(E::eof(inp))
        }
    })
}

pub fn consume_while<I, E, F, R: RangeLike>(f: F, r: R) -> parser!(<I, (), E>)
where I: SplitFirst, F: Fn(&I::Element) -> bool, E: ConsumeError<I>, I: Clone {
    consume_one_where(f).repeat::<NoCollection<_>, _>(r).ignore()
}

pub fn record_while<I, E, F, R: RangeLike>(f: F, r: R) -> parser!(<I, I::Output, E>)
where I: SplitFirst, F: Fn(&I::Element) -> bool, E: ConsumeError<I>, I: Clone + Recordable {
    consume_while(f, r).record()
}

pub fn take<I, E, R: RangeLike>(r: R) -> parser!(<I, I::Output, E>)
where I: SplitFirst, E: ConsumeError<I>, I: Clone + Recordable {
    record_while(|_| true, r)
}
