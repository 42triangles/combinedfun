//! Defines helpful parsers for parsing [`&str`](str)s.

use super::*;

/// Consumes and returns one character that is in `s`.
pub fn one_of<'a, I: 'a, E: 'a>(s: &'a str) -> parser!(<I, char, E> + 'a)
where E: ConsumeError<I>, I: SplitFirst<Element = char> + Clone {
    consume_one_where(move |&c: &char| s.contains(c))
}

/// Consumes and returns one character that is not in `s`.
pub fn not_one_of<'a, I: 'a, E: 'a>(s: &'a str) -> parser!(<I, char, E> + 'a)
where E: ConsumeError<I>, I: SplitFirst<Element = char> + Clone {
    consume_one_where(move |&c: &char| !s.contains(c))
}

/// Records characters that are in `s`.
pub fn while_one_of<'a, I: 'a, E: 'a, R: RangeLike + 'a>(s: &'a str, r: R) -> parser!(<I, I::Output, E> + 'a)
where E: ConsumeError<I>, I: SplitFirst<Element = char> + Recordable + Clone {
    one_of(s).repeat::<NoCollection<_>, _>(r).record()
}

/// Records characters that are not in `s`.
pub fn while_not_one_of<'a, I: 'a, E: 'a, R: RangeLike + 'a>(s: &'a str, r: R) -> parser!(<I, I::Output, E> + 'a)
where E: ConsumeError<I>, I: SplitFirst<Element = char> + Recordable + Clone {
    not_one_of(s).repeat::<NoCollection<_>, _>(r).record()
}

/// Records whitespace, *including newlines*.
pub fn ws<'a, I: 'a, E: 'a, R: RangeLike + 'a>(r: R) -> parser!(<I, I::Output, E> + 'a)
where E: ConsumeError<I>, I: SplitFirst<Element = char> + Recordable + Clone {
    record_while(|c: &char| c.is_whitespace(), r)
}
