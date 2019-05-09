use std::marker::PhantomData;
use std::ops;

pub mod traits;
pub use traits::{AltError, Collection, ConsumeError, EofError, HasEof, NotError, Position, RangeLike, Recordable, SplitFirst, Tag, TagError};

pub mod types;
pub use types::{Index, NoCollection, Pos, Span};

pub mod combinators;

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
        $parser.map_range_and_out(|rest, x| dbg!((rest, x)).1).map_err(|err| dbg!(err))
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
        self >> next
    }

    pub fn before<O2, F2>(self, main: Parser<F2, I>) -> parser!(<I, O2, E>)
    where F2: ParserImpl<I, Output = O2, Error = E> {
        -self >> main
    }

    pub fn followed_by<F2>(self, next: Parser<F2, I>) -> parser!(<I, O, E>)
    where F2: ParserImpl<I, Error = E> {
        self >> -next
    }

    pub fn or<F2>(self, alt: Parser<F2, I>) -> parser!(<I, O, E>)
    where F2: ParserImpl<I, Output = O, Error = E>, I: Clone, E: AltError<I> {
        self | alt
    }

    pub fn map_result<O2, F2>(self, f: F2) -> parser!(<I, O2, E>)
    where F2: Fn(O) -> Result<O2, E> {
        self >> MapResult(f)
    }

    pub fn map<O2, F2>(self, f: F2) -> parser!(<I, O2, E>)
    where F2: Fn(O) -> O2 {
        self >> f
    }

    pub fn map_err<E2, F2>(self, f: F2) -> parser!(<I, O, E2>)
    where F2: Fn(E) -> E2 {
        Parser::new(move |input| self.0.apply(input).map_err(|e| f(e)))
    }

    pub fn counted_separated<C, F2, R: RangeLike>(self, range: R, by: Parser<F2, I>) -> parser!(<I, (C, usize), E>)
    where F2: ParserImpl<I, Error = E>, C: Collection<Item = O>, I: Clone {
        Parser::new_generic(combinators::CountedSeparated(self.0, by.0, range, PhantomData))
    }

    pub fn separated<C, F2, R: RangeLike>(self, range: R, by: Parser<F2, I>) -> parser!(<I, C, E>)
    where F2: ParserImpl<I, Error = E>, C: Collection<Item = O>, I: Clone {
        Parser::new_generic(combinators::MapLeft(combinators::CountedSeparated(self.0, by.0, range, PhantomData)))
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
        Parser::new_generic(combinators::MapLeft(combinators::CountedSeparated(self.0, combinators::Epsilon(PhantomData), range, PhantomData)))
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
        self | ()
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

    pub fn map_range_and_out<O2, F2>(self, f: F2) -> parser!(<I, O2, E>)
    where F2: Fn((&I, &I), O) -> O2, I: Clone {
        Parser::new(move |inp: I| {
            let inp_clone = inp.clone();
            self.0.apply(inp).map(|(left, out)| {
                let out = f((&inp_clone, &left), out);
                (left, out)
            })
        })
    }

    pub fn map_parser<O2, F2, F3>(self, f: F2) -> parser!(<I, O2, E>)
    where F2: Fn(O) -> Parser<F3, I>, F3: ParserImpl<I, Output = O2, Error = E> {
        Parser::new(move |inp: I| {
            let (left, first_out) = self.0.apply(inp)?;
            f(first_out).0.apply(left)
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

pub struct Ignored<F, I>(Parser<F, I>);

impl<F, I> ops::Neg for Parser<F, I> {
    type Output = Ignored<F, I>;

    fn neg(self) -> Ignored<F, I> {
        Ignored(self)
    }
}

impl<F1, F2, I> ops::Shr<Parser<F2, I>> for Parser<F1, I> where F1: ParserImpl<I>, F2: ParserImpl<I, Error = F1::Error> {
    type Output = Parser<combinators::Then<F1, F2>, I>;

    fn shr(self, next: Parser<F2, I>) -> Self::Output {
        Parser::new_generic(combinators::Then(self.0, next.0))
    }
}

impl<F1, F2, I> ops::Shr<Ignored<F2, I>> for Parser<F1, I> where F1: ParserImpl<I>, F2: ParserImpl<I, Error = F1::Error> {
    type Output = Parser<combinators::MapLeft<combinators::Then<F1, F2>>, I>;

    fn shr(self, next: Ignored<F2, I>) -> Self::Output {
        Parser::new_generic(combinators::MapLeft(combinators::Then(self.0, (next.0).0)))
    }
}

impl<F1, F2, I> ops::Shr<Parser<F2, I>> for Ignored<F1, I> where F1: ParserImpl<I>, F2: ParserImpl<I, Error = F1::Error> {
    type Output = Parser<combinators::MapRight<combinators::Then<F1, F2>>, I>;

    fn shr(self, next: Parser<F2, I>) -> Self::Output {
        Parser::new_generic(combinators::MapRight(combinators::Then((self.0).0, next.0)))
    }
}

impl<F1, F2, I> ops::Shr<Ignored<F2, I>> for Ignored<F1, I> where F1: ParserImpl<I>, F2: ParserImpl<I, Error = F1::Error> {
    type Output = Ignored<combinators::MapRight<combinators::Then<F1, F2>>, I>;

    fn shr(self, next: Ignored<F2, I>) -> Self::Output {
        Ignored(self >> next.0)
    }
}

impl<F1, F2, I, O> ops::Shr<F2> for Parser<F1, I> where F1: ParserImpl<I>, F2: (Fn(F1::Output) -> O) {
    type Output = Parser<combinators::Map<F1, F2>, I>;

    fn shr(self, map: F2) -> Self::Output {
        Parser::new_generic(combinators::Map(self.0, map))
    }
}

pub struct MapResult<F>(pub F);

impl<F1, F2, I, O> ops::Shr<MapResult<F2>> for Parser<F1, I> where F1: ParserImpl<I>, F2: Fn(F1::Output) -> Result<O, F1::Error> {
    type Output = Parser<combinators::MapResult<F1, F2>, I>;

    fn shr(self, map: MapResult<F2>) -> Self::Output {
        Parser::new_generic(combinators::MapResult(self.0, map.0))
    }
}

impl<F1, F2, I> ops::BitOr<Parser<F2, I>> for Parser<F1, I> where F1: ParserImpl<I>, F2: ParserImpl<I, Output = F1::Output, Error = F1::Error>, I: Clone, F1::Error: AltError<I> {
    type Output = Parser<combinators::Or<F1, F2>, I>;

    fn bitor(self, or: Parser<F2, I>) -> Self::Output {
        Parser::new_generic(combinators::Or(self.0, or.0))
    }
}

impl<F, I> ops::BitOr<()> for Parser<F, I> where F: ParserImpl<I>, I: Clone {
    type Output = Parser<combinators::MapLeft<combinators::CountedSeparated<Option<F::Output>, ops::RangeInclusive<usize>, F, combinators::Epsilon<F::Error>>>, I>;

    fn bitor(self, _: ()) -> Self::Output {
        Parser::new_generic(combinators::MapLeft(combinators::CountedSeparated(self.0, combinators::Epsilon(PhantomData), 0..=1, PhantomData)))
    }
}

pub struct ElementSeparator<E, S, I>(Parser<E, I>, Parser<S, I>);

impl<F1, F2, I> ops::Div<Parser<F2, I>> for Parser<F1, I> {
    type Output = ElementSeparator<F1, F2, I>;

    fn div(self, separator: Parser<F2, I>) -> Self::Output {
        ElementSeparator(self, separator)
    }
}

impl<F1, F2, I, R> ops::Mul<R> for ElementSeparator<F1, F2, I> where F1: ParserImpl<I>, F2: ParserImpl<I, Error = F1::Error>, R: RangeLike, I: Clone {
    type Output = Parser<combinators::MapLeft<combinators::CountedSeparated<Vec<F1::Output>, R, F1, F2>>, I>;

    fn mul(self, range: R) -> Self::Output {
        Parser::new_generic(combinators::MapLeft(combinators::CountedSeparated((self.0).0, (self.1).0, range, PhantomData)))
    }
}

impl<F1, I, R> ops::Mul<R> for Parser<F1, I> where F1: ParserImpl<I>, R: RangeLike, I: Clone {
    type Output = Parser<combinators::MapLeft<combinators::CountedSeparated<Vec<F1::Output>, R, F1, combinators::Epsilon<F1::Error>>>, I>;

    fn mul(self, range: R) -> Self::Output {
        self / Parser::new_generic(combinators::Epsilon(PhantomData)) * range
    }
}

pub fn epsilon<I, E>() -> parser!(<I, (), E>) {
    Parser::new_generic(combinators::Epsilon(PhantomData))
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
    consume_one_where(f).repeat::<NoCollection<_>, _>(r).map(|_| ())
}

pub fn record_while<I, E, F, R: RangeLike>(f: F, r: R) -> parser!(<I, I::Output, E>)
where I: SplitFirst, F: Fn(&I::Element) -> bool, E: ConsumeError<I>, I: Clone + Recordable {
    consume_while(f, r).record()
}

pub fn take<I, E, R: RangeLike>(r: R) -> parser!(<I, I::Output, E>)
where I: SplitFirst, E: ConsumeError<I>, I: Clone + Recordable {
    record_while(|_| true, r)
}
