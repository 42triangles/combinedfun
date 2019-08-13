//! This is a parser combinator library that aims to provide short and consise, but easily readable
//! parser combinators.
//!
//! If you don't know how parser combinators work, I suggest looking at
//! [`nom`](https://github.com/geal/nom) first.
//!
//! This library doesn't use macros, so it is a bit limited for some applications (specifically
//! places where you can use [`map_parser`](Parser::map_parser) are rather limited).
//!
//! It also uses operator overloading for writing parsers that are easy to read and write.
//!
//! Here is one example (I have no clue why almost every closure needs its arguments specified):
//!
//! ```
//! use std::iter;
//! use combinedfun as cf;
//!
//! enum End {
//!     Repeat(String),
//!     Add(usize),
//! }
//!
//! let parser = (
//!     cf::record_while(|c: &char| c.is_digit(10), 1..)
//!     >> (|s: &str| s.parse::<usize>().unwrap())
//!     >> (
//!         -cf::tag(" ")
//!         >> cf::take(..)
//!         >> (|s: &str| End::Repeat(s.to_owned()))
//!         |
//!         -cf::tag("+")
//!         >> cf::record_while(|c: &char| c.is_digit(10), 1..)
//!         >> (|s: &str| End::Add(s.parse::<usize>().unwrap()))
//!     )
//!     >> (|(i, end)| match end {
//!         End::Repeat(s) => (0..i).fold("".to_owned(), |acc, _| acc + &s),
//!         End::Add(j) => (i + j).to_string()
//!     })
//! );
//!
//! assert_eq!(parser.parse("3 abc"), Ok("abcabcabc".to_owned()));
//! assert_eq!(parser.parse("10 x"), Ok("xxxxxxxxxx".to_owned()));
//! assert_eq!(parser.parse("42+123"), Ok("165".to_owned()));
//! assert_eq!(parser.parse("42+abc"), Err(()));
//! assert_eq!(parser.parse("+123"), Err(()));
//! ```

use std::marker::PhantomData;
use std::ops;

pub mod traits;
pub use traits::{AltError, Collection, ConsumeError, EofError, HasEof, NotError, Position, RangeLike, Recordable, SplitFirst, Tag, TagError};

pub mod types;
pub use types::{Index, NoCollection, Pos, Span};

pub mod combinators;

pub mod str_parsers;

#[cfg(test)]
mod tests;

/// This trait has to be implemented for the combinators in [`combinators`](combinators) to provide
/// the basic functionality required for [`Parser`](Parser).
pub trait ParserImpl<I> {
    /// The output type of the parser
    type Output;

    /// The error type of the parser
    type Error;

    /// This runs the parser. It receives an input, returns the input that hasn't been read yet and
    /// the output attached to what was read until that point. If it fails, it returns its error
    /// type.
    fn apply(&self, inp: I) -> Result<(I, Self::Output), Self::Error>;
}

impl<F, I, O, E> ParserImpl<I> for F where F: Fn(I) -> Result<(I, O), E> {
    type Output = O;
    type Error = E;

    fn apply(&self, inp: I) -> Result<(I, O), E> {
        self(inp)
    }
}

/// This type is the one all functionality is built on.
/// 
/// The `F` type argument is the parser implementation, which is usually a function or a combinator
/// from [`combinators`](combinators).
///
/// The `I` type argument is the expected input. If you write parsers, it is advised to make your
/// parser generic over the input, to allow different levels of tracking it, unless the parser
/// makes use of the type directly.
///
/// # Notes
///
/// All repeating combinators simply stop consuming the input if the given range is exceeded
/// (should one be given). The behaviour, should that range be empty or from high to low, is, while
/// not undefined, implementation defined and should not be relied upon.
///
/// Those repeating combinators are (note that the syntactic sugar variant *always* uses
/// [`Vec`](Vec):
///
/// | combinator                                                 | has separator | has range | returns outputs | returns count | syntactic sugar |
/// |------------------------------------------------------------|-----|------------|-----|-----|------|
/// | [`counted_separated`](Parser::counted_separated)           | yes | yes        | yes | yes | none |
/// | [`separated`](Parser::separated)                           | yes | yes        | yes | no  | [`/ sep`](#impl-Div<Parser<F2%2C%20I>>) [`* new_collection`](struct.ElementSeparator.html#impl-Mul<CG>) [`* range`](struct.WithCollectionGenerator.html#impl-Mul<R>) |
/// | [`const_separated`](Parser::const_separated)               | yes | one number | yes | no  | none |
/// | [`count_separated_within`](Parser::count_separated_within) | yes | yes        | no  | yes | none |
/// | [`count_separated`](Parser::count_separated)               | yes | no         | no  | yes | none |
/// | [`counted_repeat`](Parser::counted_repeat)                 | no  | yes        | yes | yes | none |
/// | [`repeat`](Parser::repeat)                                 | no  | yes        | yes | no  | [`* new_collection`](#impl-Mul<CG>) [`* range`](struct.WithCollectionGenerator.html#impl-Mul<R>) |
/// | [`const_repeat`](Parser::const_repeat)                     | no  | one number | yes | no  | none |
/// | [`count_within`](Parser::count_within)                     | no  | yes        | no  | yes | none |
/// | [`count`](Parser::count)                                   | no  | no         | no  | yes | none |
///
/// Combinators not found as methods:
/// * [`epsilon` or ε](epsilon). Matches nothing, always succeeds.
/// * [`tag`](tag). Requires the input to start with the given subsequence/substring.
/// * [`fail_with`](fail_with). Always fails, generating the error using a closure.
/// * [`fail_with_const`](fail_with_const). Always fails, generating the error using [`Clone`](Clone) on the given argument.
/// * [`eof`](eof). Fails if the input isn't empty.
/// * [`not`](not). Fails if the given parser succeeds, and succeeds if the given parser fails.
/// * [`consume_one_where`](consume_one_where). Consumes the first element/character of the input, if it matches a given condition.
/// * [`consume_while`](consume_while). Consumes elements/characters of the input that match the given condition. Its given a range, which acts like the range given to other repeating combinators.
/// * [`record_while`](record_while). Like [`consume_while`](consume_while), but returns the matched substring.
/// * [`take`](take). Consumes the rest of the input, and returns the matched string.
/// * [`lookahead`](lookahead). Outputs the result of the given parser without consuming it.
/// * [`output`](output). Outputs the output of the given function, or fails if the function returns [`Err`](Err).
pub struct Parser<F, I>(F, PhantomData<fn(I)>);

/// The parser macro allows you to easily write the type of a parser in a return position, using
/// `impl Trait`.
///
/// There are two ways to use it (`I` being the input, `O` the output and `E` the error type):
/// * `parser!(<I, O, E>)` yields `Parser<impl ParserImpl<I, Output = O, Error = E>>`
/// * `parser!(<I, O, E> + 'a)` yields `Parser<impl ParserImpl<I, Output = O, Error = E> + 'a>`
#[macro_export]
macro_rules! parser {
    (<$i:ty, $o:ty, $e:ty> + $lt:tt) => {
        $crate::Parser<impl $crate::ParserImpl<$i, Output = $o, Error = $e> + $lt, $i>
    };
    (<$i:ty, $o:ty, $e:ty>) => {
        $crate::Parser<impl $crate::ParserImpl<$i, Output = $o, Error = $e>, $i>
    };
}

/// Allows debugging a parser. It uses the `dbg!` macro internally, and prints what the parser
/// returned (be it successful or an error). If it was successful, it prints the input before and
/// after the parser was applied.
#[macro_export]
macro_rules! parser_dbg {
    ($parser:expr) => {
        $crate::Parser::map_err(
            $crate::Parser::map_range_and_out(
                $parser,
                |rest, x| dbg!((rest, x)).1
            ),
            |err| dbg!(err)
        )
    }
}

/// Allows helping Rusts type inference by returning an [ε](epsilon) parser with the given type
/// parameters. This is intended to be used with the overloaded operators.
#[macro_export]
macro_rules! parser_hint {
    (<Input = $I:ty, Error = $E:ty>) => {
        -$crate::epsilon::<$I, $E>()
    };
    (<Error = $E:ty, Input = $I:ty>) => {
        parser_hint!(<Input = $I, Error = $E>)
    };
    (<Input = $I:ty>) => {
        parser_hint!(<Input = $I, Error = _>)
    };
    (<Error = $E:ty>) => {
        parser_hint!(<Input = _, Error = $E>)
    };
}

impl<F, I, O, E> Parser<F, I> where F: Fn(I) -> Result<(I, O), E> {
    /// This function allows you to create a new parser. If you wrote your own type which
    /// implements [`ParserImpl`](ParserImpl), use [`Parser::new_generic`](Parser::new_generic).
    pub fn new(func: F) -> Self {
        Self::new_generic(func)
    }
}

impl<F, I, O, E> Parser<F, I> where F: ParserImpl<I, Output = O, Error = E> {
    /// This function allows you to create a new parser. It will not work with type inference for
    /// closures though, so use [`Parser::new`](Parser::new) for those.
    ///
    /// This function only exists to make the type inference for closures work in
    /// [`new`](Parser::new).
    pub fn new_generic(implementation: F) -> Self {
        Parser(implementation, PhantomData)
    }

    /// This returns a new parser, which applies this parser and the given one on the input in that
    /// order, returning a pair of outputs. The syntactic sugar is
    /// [`>>`](#impl-Shr<Parser<F2%2C%20I>>).
    pub fn then<O2, F2>(self, next: Parser<F2, I>) -> parser!(<I, (O, O2), E>)
    where F2: ParserImpl<I, Output = O2, Error = E> {
        self >> next
    }

    /// See [`Parser::then`](Parser::then), this parser returns only the result of the parser which
    /// was given as an argument. The syntactic sugar is
    /// [`>>`](struct.Ignored.html#impl-Shr<Parser<F2%2C%20I>>) together with [`-`](#impl-Neg), see
    /// the [top level documentation](crate).
    pub fn before<O2, F2>(self, main: Parser<F2, I>) -> parser!(<I, O2, E>)
    where F2: ParserImpl<I, Output = O2, Error = E> {
        -self >> main
    }

    /// See [`Parser::then`](Parser::then), this parser returns only the result of this parser. The
    /// syntactic sugar is [`>>`](#impl-Shr<Ignored<F2%2C%20I>>) together with [`-`](#impl-Neg),
    /// see the [top level documentation](crate).
    pub fn followed_by<F2>(self, next: Parser<F2, I>) -> parser!(<I, O, E>)
    where F2: ParserImpl<I, Error = E> {
        self >> -next
    }

    /// This returns a new parser, which tries to apply this parser, and, should this fail,
    /// attempts to apply the one given as an argument. Should that also fail, it'll return an
    /// error. The syntactic sugar is [`|`](#impl-BitOr<Parser<F2%2C%20I>>).
    pub fn or<F2>(self, alt: Parser<F2, I>) -> parser!(<I, O, E>)
    where F2: ParserImpl<I, Output = O, Error = E>, I: Clone, E: AltError<I> {
        self | alt
    }

    /// This returns a new parser, which maps the given function to the result of this parser. This
    /// function returns a [`Result`](Result), so it can lead to the returned parser failing even
    /// if this one didn't. The syntactic sugar is [`>>`](#impl-Shr<MapResult<F2>>) together with
    /// the wrapper type [`MapResult`](MapResult).
    ///
    /// If your function never fails, use [`map`](Parser::map).
    pub fn map_result<O2, F2>(self, f: F2) -> parser!(<I, O2, E>)
    where F2: Fn(O) -> Result<O2, E> {
        self >> MapResult(f)
    }

    /// This returns a new parser, which maps the given funciton to the result of this parser. This
    /// function returns a [`Result`](Result), so it can lead to the returned parser failing even
    /// if this one didn't. The given function also receives the input from before this parser was
    /// applied, in case your error type requires that information.
    pub fn map_result_with_input_before<O2, F2>(self, f: F2) -> parser!(<I, O2, E>)
    where F2: Fn(I, O) -> Result<O2, E>, I: Clone {
        Parser::new(move |input: I| {
            self.0.apply(input.clone()).and_then(|(left, o)| Ok((left, f(input, o)?)))
        })
    }

    /// This returns a new parser, which maps the given function to the result of this parser. The
    /// returned parser fails if this one does, and doesn't fail if this one doesn't. The syntactic
    /// sugar is [`>>`](#impl-Shr<F2>).
    ///
    /// If you want to be able to induce failure, use [`map_result`](Parser::map).
    pub fn map<O2, F2>(self, f: F2) -> parser!(<I, O2, E>)
    where F2: Fn(O) -> O2 {
        self >> f
    }

    /// This returns a new parser, which maps the given function to the error of this parser,
    /// should it fail.
    pub fn map_err<E2, F2>(self, f: F2) -> parser!(<I, O, E2>)
    where F2: Fn(E) -> E2 {
        Parser::new(move |input| self.0.apply(input).map_err(|e| f(e)))
    }

    /// This returns a new parser, which collects a number of occurences which is in the given
    /// range in the [`Collection`](Collection) `C`, and returns this collection and the number of
    /// seen occurences in a pair.
    ///
    /// Should this be impossible, it fails.
    ///
    /// Please read the notes in the documentation for [this type](Parser).
    pub fn counted_separated<C, F2, R: RangeLike, CG>(self, range: R, by: Parser<F2, I>, collection_generator: CG) -> parser!(<I, (C, usize), E>)
    where F2: ParserImpl<I, Error = E>, C: Collection<Item = O>, I: Clone, CG: Fn() -> C {
        Parser::new_generic(combinators::CountedSeparated {
            main_parser: self.0,
            separator: by.0,
            range,
            collection_generator,
        })
    }

    /// This returns a new parser, which collects a number of occurences which is in the given
    /// range in the [`Collection`](Collection) `C`, and returns this collection.
    ///
    /// Should this be impossible, it fails.
    ///
    /// Please read the notes in the documentation for [this type](Parser).
    pub fn separated<C, F2, R: RangeLike, CG>(self, range: R, by: Parser<F2, I>, collection_generator: CG) -> parser!(<I, C, E>)
    where F2: ParserImpl<I, Error = E>, C: Collection<Item = O>, I: Clone, CG: Fn() -> C {
        self / by * collection_generator * range
    }

    /// This returns a new parser, which collects a number of occurences which is equal to the
    /// given argument in the [`Collection`](Collection) `C`, and returns this collection.
    ///
    /// Should this be impossible, it fails.
    ///
    /// Please read the notes in the documentation for [this type](Parser).
    pub fn const_separated<C, F2, CG>(self, n: usize, by: Parser<F2, I>, collection_generator: CG) -> parser!(<I, C, E>)
    where F2: ParserImpl<I, Error = E>, C: Collection<Item = O>, I: Clone, CG: Fn() -> C {
        self / by * collection_generator * (n..=n)
    }

    /// This returns a new parser, which counts the number of occurences which has to be within the
    /// given range, and returns that number.
    ///
    /// It only consumes the minimum of the amount of occurences there are and the upper bound, if
    /// there are less occurences than the lower bound, the returned parser fails.
    ///
    /// Please read the notes in the documentation for [this type](Parser).
    pub fn count_separated_within<R: RangeLike, F2>(self, range: R, by: Parser<F2, I>) -> parser!(<I, usize, E>)
    where F2: ParserImpl<I, Error = E>, I: Clone {
        self.counted_separated(range, by, NoCollection::new).map(|(_, count)| count)
    }

    /// This returns a new parser, which counts the number of occurences, and returns that number.
    ///
    /// Please read the notes in the documentation for [this type](Parser).
    pub fn count_separated<F2>(self, by: Parser<F2, I>) -> parser!(<I, usize, E>)
    where F2: ParserImpl<I, Error = E>, I: Clone {
        self.count_separated_within(.., by)
    }

    /// [`counted_separated`](Parser::counted_separated) without a separator.
    ///
    /// Please read the notes in the documentation for [this type](Parser).
    pub fn counted_repeat<C, R: RangeLike, CG>(self, range: R, collection_generator: CG) -> parser!(<I, (C, usize), E>)
    where C: Collection<Item = O>, I: Clone, CG: Fn() -> C {
        self.counted_separated(range, epsilon(), collection_generator)
    }

    /// [`separated`](Parser::separated) without a separator.
    ///
    /// Please read the notes in the documentation for [this type](Parser).
    pub fn repeat<C, R: RangeLike, CG>(self, range: R, collection_generator: CG) -> parser!(<I, C, E>)
    where C: Collection<Item = O>, I: Clone, CG: Fn() -> C {
        self * collection_generator * range
    }

    /// [`const_separated`](Parser::const_separated) without a separator.
    ///
    /// Please read the notes in the documentation for [this type](Parser).
    pub fn const_repeat<C, CG>(self, n: usize, collection_generator: CG) -> parser!(<I, C, E>)
    where C: Collection<Item = O>, I: Clone, CG: Fn() -> C {
        self * collection_generator * (n..=n)
    }

    /// [`count_separated_within`](Parser::count_separated_within) without a separator.
    ///
    /// Please read the notes in the documentation for [this type](Parser).
    pub fn count_within<R: RangeLike>(self, range: R) -> parser!(<I, usize, E>)
    where I: Clone {
        self.counted_repeat(range, NoCollection::new).map(|(_, count)| count)
    }

    /// [`count_separated`](Parser::counted_separated) without a separator.
    ///
    /// Please read the notes in the documentation for [this type](Parser).
    pub fn count(self) -> parser!(<I, usize, E>)
    where I: Clone {
        self.count_within(..)
    }

    /// This returns a parser which attempts using this parser, wrapping the result in
    /// [`Some`](Some). If this parser fails, [`None`](None) is returned and no input is consumed.
    pub fn maybe(self) -> parser!(<I, Option<O>, E>)
    where I: Clone {
        self | ()
    }

    /// This returns a parser which runs this parser, yielding the range of input that this parser
    /// consumed. It returns error should the inner parser fail.
    pub fn record(self) -> parser!(<I, I::Output, E>)
    where I: Clone + Recordable {
        Parser::new(move |inp: I| {
            let old = inp.clone();
            self.0.apply(inp).map(|(left, _)| (left.clone(), old.record(left)))
        })
    }

    /// This converts the error to another one using [`.into`](Into::into), should this parser
    /// fail.
    pub fn convert_err<E2>(self) -> parser!(<I, O, E2>)
    where E2: From<E> {
        self.map_err(E2::from)
    }

    /// This calls the given function with the input left before and after this parser was run,
    /// together with the result of running it. The output of the resulting parser is the output of
    /// that function.
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

    /// This runs a parser based on the output of this parser.
    ///
    /// Note that the returned parser has to have a *one* type, you can achieve this (if your
    /// parser doesn't just use the output for ranges or in closures) by defining those parsers as
    /// standalone functions.
    pub fn map_parser<O2, F2, F3>(self, f: F2) -> parser!(<I, O2, E>)
    where F2: Fn(O) -> Parser<F3, I>, F3: ParserImpl<I, Output = O2, Error = E> {
        Parser::new(move |inp: I| {
            let (left, first_out) = self.0.apply(inp)?;
            f(first_out).0.apply(left)
        })
    }

    /// Borrows this parser, allowing it to be combined with other parsers without being moved.
    pub fn borrowed<'a>(&'a self) -> parser!(<I, O, E> + 'a) {
        Parser::new(move |inp| self.0.apply(inp))
    }

    /// Parses as far as it can parse. This is just a wrapper around
    /// [`ParserImpl::apply`](ParserImpl::apply).
    ///
    /// See that function for more documentation.
    pub fn parse_partial(&self, input: I) -> Result<(I, O), E> {
        self.0.apply(input)
    }

    /// Parses the whole input. Should this parser not consume it, an approriate error is returned.
    pub fn parse(&self, input: I) -> Result<O, E>
    where I: HasEof, E: EofError<I> {
        self.borrowed().followed_by(eof()).parse_partial(input).map(|(_, o)| o)
    }
}

/// A shortcut for parsers that are defined by functions.
pub type FnParser<I, O, E> = Parser<fn(input: I) -> Result<(I, O), E>, I>;

/// Creates an [`FnParser`](FnParser) from a function.
pub fn f<I, O, E>(func: fn(I) -> Result<(I, O), E>) -> FnParser<I, O, E> {
    Parser::new(func)
}

/// This type is used to make the syntactic sugar work. It's observed if you put a minus in front
/// of a [`Parser`](Parser) (see [`-`](struct.Parser.html#impl-Neg)).
///
/// If this is prepended (using [`>>`](#impl-Shr<Parser<F2%2C%20I>>) to a parser, it's the
/// equivalent to calling [`Parser::before`](Parser::before).
///
/// If this is appended (using [`>>`](struct.Parser.html#impl-Shr<Ignored<F2%2C%20I>>) to a parser,
/// it's the equivalent to calling [`Parser::followed_by`](Parser::followed_by).
///
/// If this is appended (using [`>>`](#impl-Shr<Ignored<F2%2C%20I>>) to another `Ignored`, a new
/// `Ignored` is returned.
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

/// This wrapper can be used to map to a [`Result`](Result) instead of mapping to the output
/// without being able to fail the parser.
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
    type Output = WithManyCombinator<I, fn() -> Option<F::Output>, InclusiveUsizeRange, F, combinators::Epsilon<F::Error>>;

    fn bitor(self, _: ()) -> Self::Output {
        fn return_none<T>() -> Option<T> {
            None
        }

        self * (return_none as fn() -> Option<F::Output>) * (0..=1)
    }
}

/// This type is used to make the syntactic sugar work. It's observed if you "divide" one
/// [`Parser`](Parser) by another (see [`/`](struct.Parser.html#impl-Div<Parser<F2%2C%20I>>)).
/// Specifically, it allows to use operators for [`Parser::separated`](Parser::separated).
pub struct ElementSeparator<E, S, I>(Parser<E, I>, Parser<S, I>);

impl<F1, F2, I> ops::Div<Parser<F2, I>> for Parser<F1, I> {
    type Output = ElementSeparator<F1, F2, I>;

    fn div(self, separator: Parser<F2, I>) -> Self::Output {
        ElementSeparator(self, separator)
    }
}

/// This type is used to make the syntactic sugar work. It's observed if you multiply a parser or
/// an [`ElementSeparator`]ElementSeparator] by a function (see
/// [`*` for `ElementSeparator`](struct.ElementSeparator.html#impl-Mul<CG>), or
/// [`*` for `Parser`](struct.Parser.html#impl-Mul<CG>)).
/// Specifically, it allows to use operators for [`Parser::separated`](Parser::separated) and
/// [`Parser::repeat`](Parser::repeat).
pub struct WithCollectionGenerator<A, CG>(A, CG);

impl<F, I, CG> ops::Mul<CG> for Parser<F, I> {
    type Output = WithCollectionGenerator<Parser<F, I>, CG>;

    fn mul(self, cg: CG) -> Self::Output {
        WithCollectionGenerator(self, cg)
    }
}

impl<E, S, I, CG> ops::Mul<CG> for ElementSeparator<E, S, I> {
    type Output = WithCollectionGenerator<ElementSeparator<E, S, I>, CG>;

    fn mul(self, cg: CG) -> Self::Output {
        WithCollectionGenerator(self, cg)
    }
}

type InclusiveUsizeRange = ops::RangeInclusive<usize>;

type WithManyCombinator<I, G, R, F, S> = Parser<combinators::MapLeft<combinators::CountedSeparated<G, R, F, S>>, I>;

impl<C, F1, I, CG, R> ops::Mul<R> for WithCollectionGenerator<Parser<F1, I>, CG> where F1: ParserImpl<I>, R: RangeLike, I: Clone, CG: Fn() -> C, C: Collection<Item = F1::Output> {
    type Output = WithManyCombinator<I, CG, R, F1, combinators::Epsilon<F1::Error>>;

    fn mul(self, range: R) -> Self::Output {
        let WithCollectionGenerator(parser, cg) = self;
        parser / Parser::new_generic(combinators::Epsilon(PhantomData)) * cg * range
    }
}

impl<C,F1, F2, I, CG, R> ops::Mul<R> for WithCollectionGenerator<ElementSeparator<F1, F2, I>, CG> where F1: ParserImpl<I>, F2: ParserImpl<I, Error = F1::Error>, R: RangeLike, I: Clone, CG: Fn() -> C, C: Collection<Item = F1::Output> {
    type Output = WithManyCombinator<I, CG, R, F1, F2>;

    fn mul(self, range: R) -> Self::Output {
        Parser::new_generic(combinators::MapLeft(combinators::CountedSeparated {
            main_parser: ((self.0).0).0,
            separator: ((self.0).1).0,
            range,
            collection_generator: self.1
        }))
    }
}

/// Matches nothing, always succeeds.
pub fn epsilon<I, E>() -> parser!(<I, (), E>) {
    Parser::new_generic(combinators::Epsilon(PhantomData))
}

/// Requires the input to start with the given subsequence/substring.
pub fn tag<'a, I, E, T: ?Sized>(tag: &'a T) -> parser!(<I, T::Output, E> + 'a)
where T: Tag<I>, E: TagError<'a, T, I>, I: Clone {
    Parser::new(move |inp: I| tag.parse_tag(inp.clone()).map(|(tag, rest)| (rest, tag)).ok_or_else(|| E::tag(tag, inp)))
}

/// Always fails, generating the error using a closure.
///
/// If your error is [`Clone`](Clone), consider using [`fail_with_const`](fail_with_const).
pub fn fail_with<I, O, E, F>(f: F) -> parser!(<I, O, E>)
where F: Fn() -> E {
    Parser::new(move |_| Err(f()))
}

/// Always fails, generating the error using [`Clone::clone`](Clone::clone).
///
/// If your error isn't [`Clone`](Clone), consider using [`fail_with`](fail_with).
pub fn fail_with_const<I, O, E>(e: E) -> parser!(<I, O, E>)
where E: Clone {
    fail_with(move || e.clone())
}

/// Fails if the input isn't empty.
pub fn eof<I, E>() -> parser!(<I, (), E>)
where I: HasEof, E: EofError<I> {
    Parser::new(move |inp: I| if inp.at_eof() {
        Ok((inp, ()))
    } else {
        Err(E::no_eof(inp))
    })
}

/// Fails if the given parser succeeds, and succeeds if the given parser fails.
pub fn not<I, O, EO, E, F>(p: Parser<F, I>) -> parser!(<I, EO, E>)
where F: ParserImpl<I, Output = O, Error = EO>, E: NotError<O, I>, I: Clone {
    Parser::new(move |inp: I| match p.0.apply(inp.clone()) {
        Ok((_, out)) => Err(E::not(out, inp)),
        Err(err) => Ok((inp, err)),
    })
}

/// Consumes the first element/character of the input, if it matches the given condition.
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

/// Consumes elements/characters of the input that match the given condition.
///
/// The range acts like the range given to other repeating combinators, see the
/// [documentation for `Parser`](Parser)
pub fn consume_while<I, E, F, R: RangeLike>(f: F, r: R) -> parser!(<I, (), E>)
where I: SplitFirst, F: Fn(&I::Element) -> bool, E: ConsumeError<I>, I: Clone {
    consume_one_where(f).repeat(r, NoCollection::new).map(|_| ())
}

/// Like [`consume_while`](consume_while), but returns the matched substring.
///
/// The range acts like the range given to other repeating combinators, see the
/// [documentation for `Parser`](Parser)
pub fn record_while<I, E, F, R: RangeLike>(f: F, r: R) -> parser!(<I, I::Output, E>)
where I: SplitFirst, F: Fn(&I::Element) -> bool, E: ConsumeError<I>, I: Clone + Recordable {
    consume_while(f, r).record()
}

/// Consumes the rest of the input, and returns the matched string.
pub fn take<I, E, R: RangeLike>(r: R) -> parser!(<I, I::Output, E>)
where I: SplitFirst, E: ConsumeError<I>, I: Clone + Recordable {
    record_while(|_| true, r)
}

/// Outputs the result of the given parser without consuming it.
pub fn lookahead<I, F>(f: Parser<F, I>) -> parser!(<I, F::Output, F::Error>)
where F: ParserImpl<I>, I: Clone {
    Parser::new(move |inp: I| {
        let left = inp.clone();
        f.0.apply(inp).map(|(_, out)| (left, out))
    })
}

/// Outputs the output of the given function, or fails if the function returns [`Err`](Err).
pub fn output<I, O, E, F>(f: F) -> parser!(<I, O, E>)
where F: Fn() -> Result<O, E> {
    Parser::new(move |inp: I| f().map(|out| (inp, out)))
}
