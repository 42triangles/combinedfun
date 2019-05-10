//! Defines helpful parsers for parsing [`&str`](str)s.

use super::*;

/// Consumes and returns one character that is in `s`.
pub fn one_of<'a, E: 'a>(s: &'a str) -> parser!(<&'a str, char, E>)
where E: ConsumeError<&'a str> {
    consume_one_where(move |&c: &char| s.contains(c))
}

/// Consumes and returns one character that is not in `s`.
pub fn not_one_of<'a, E: 'a>(s: &'a str) -> parser!(<&'a str, char, E>)
where E: ConsumeError<&'a str> {
    consume_one_where(move |&c: &char| !s.contains(c))
}

/// Records characters that are in `s`.
pub fn while_one_of<'a, E: 'a, R: RangeLike + 'a>(s: &'a str, r: R) -> parser!(<&'a str, &'a str, E>)
where E: ConsumeError<&'a str> {
    one_of(s).repeat::<NoCollection<_>, _>(r).record()
}

/// Records characters that are not in `s`.
pub fn while_not_one_of<'a, E: 'a, R: RangeLike + 'a>(s: &'a str, r: R) -> parser!(<&'a str, &'a str, E>)
where E: ConsumeError<&'a str> {
    not_one_of(s).repeat::<NoCollection<_>, _>(r).record()
}

/// Records whitespace, *including newlines*.
pub fn ws<'a, E: 'a, R: RangeLike + 'a>(r: R) -> parser!(<&'a str, &'a str, E>)
where E: ConsumeError<&'a str> {
    record_while(|c: &char| c.is_whitespace(), r)
}
