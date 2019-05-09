use super::*;

#[test]
fn test_parse_simple() {
    assert_eq!(Parser::new(|_| Err(()) as Result<(_, ()), _>).parse("test"), Err(()));
    assert_eq!(Parser::new(|_| Ok(("", ())) as Result<_, ()>).parse("test"), Ok(()));
    assert_eq!(Parser::new(|i| Ok((i, ()))).parse("test"), Err(()));
    assert_eq!(Parser::new(|i| Ok((i, ())) as Result<_, ()>).parse(""), Ok(()));
}

#[test]
fn test_tag() {
    let parser = tag("test");
    assert_eq!(parser.parse("test"), Ok("test"));
    assert_eq!(parser.parse("text"), Err(()));
}

#[test]
fn test_then() {
    let parser = tag("te").then(tag("st"));
    assert_eq!(parser.parse("test"), Ok(("te", "st")));
    assert_eq!(parser.parse("text"), Err(()));
    assert_eq!(parser.parse("rest"), Err(()));
    assert_eq!(parser.parse("rext"), Err(()));

    let parser = tag("test").then(epsilon());
    assert_eq!(parser.parse("test"), Ok(("test", ())));
    assert_eq!(parser.parse("text"), Err(()));

    let parser = epsilon::<_, ()>().then(tag("test"));
    assert_eq!(parser.parse("test"), Ok(((), "test")));
    assert_eq!(parser.parse("text"), Err(()));
}

#[test]
fn test_before() {
    let parser = tag("te").before(tag("st"));
    assert_eq!(parser.parse("test"), Ok("st"));
    assert_eq!(parser.parse("text"), Err(()));
}

#[test]
fn test_followed_by() {
    let parser = tag("te").followed_by(tag("st"));
    assert_eq!(parser.parse("test"), Ok("te"));
    assert_eq!(parser.parse("text"), Err(()));
}

#[test]
fn test_or() {
    let parser = tag("test").map(|_| 0).or(tag("text").map(|_| 1));
    assert_eq!(parser.parse("test"), Ok(0));
    assert_eq!(parser.parse("text"), Ok(1));
    assert_eq!(parser.parse("nope"), Err(()));

    let parser = tag("test").map(|_| 0).or(tag("test").map(|_| 1));
    assert_eq!(parser.parse("test"), Ok(0));
    assert_eq!(parser.parse("text"), Err(()));
    assert_eq!(parser.parse("nope"), Err(()));
}

#[test]
fn test_map_result() {
    assert_eq!(epsilon().map(|()| 1).map_result(|i| Ok(i) as Result<_, ()>).parse(""), Ok(1));
    assert_eq!(fail_with_const(()).map(|()| 1).map_result(|i| Ok(i)).parse(""), Err(()));
    assert_eq!(epsilon().map_result(|_| Err(()) as Result<i32, _>).parse(""), Err(()));
    assert_eq!(epsilon().map_result(|_| Err(()) as Result<i32, _>).parse(""), Err(()));
}

#[test]
fn test_map() {
    assert_eq!(epsilon::<_, ()>().map(|()| 1).parse(""), Ok(1));
    assert_eq!(fail_with_const(()).map(|()| 1).parse(""), Err(()));
    
    let parser = tag(" test ").map(|s: &str| s.trim());
    assert_eq!(parser.parse(" test "), Ok("test"));
    assert_eq!(parser.parse(" text "), Err(()));
}

#[test]
fn test_map_err() {
    assert_eq!(epsilon().map_err(|()| 1).parse_partial(""), Ok(("", ())));
    assert_eq!(fail_with_const::<_, (), _>(()).map_err(|()| 1).parse_partial(""), Err(1));
}

#[test]
fn test_counted_separated() {
    macro_rules! subtest {
        (__impl () ($n:expr) Ok $($x:tt)*) => {
            Ok((std::iter::repeat("test").take($n).collect(), $n))
        };
        (__impl () ($n:expr) Err $($x:tt)*) => {
            Err(())
        };
        (__impl (+ $($left:tt)*) ($n:expr) $c:tt $($x:tt)*) => {
            subtest!(__impl ($($left)*) ($n + 1) $($x)*)
        };
        ($(($range:expr) => [$($x:tt),+]),*) => {
            $(
                let parser = tag::<_, (), _>("test").counted_separated::<Vec<_>, _, _>($range, tag(","));
                let second_parser = parser.borrowed().followed_by(tag("!"));
                let third_parser = parser.borrowed().followed_by(tag(",!"));
                print!("Currently at {:?} 0.", $range);
                assert_eq!(parser.parse(""), subtest!(__impl () (0) $($x)*));
                print!("0p!");
                assert_eq!(second_parser.parse("!"), subtest!(__impl () (0) $($x)*));
                print!("1.");
                assert_eq!(parser.parse("test"), subtest!(__impl (+) (0) $($x)*));
                print!("1,!");
                assert_eq!(second_parser.parse("test!"), subtest!(__impl (+) (0) $($x)*));
                print!("1p!");
                assert_eq!(third_parser.parse("test,!"), subtest!(__impl (+) (0) $($x)*));
                print!("2.");
                assert_eq!(parser.parse("test,test"), subtest!(__impl (++) (0) $($x)*));
                print!("3.");
                assert_eq!(parser.parse("test,test,test"), subtest!(__impl (+++) (0) $($x)*));
                print!("4.");
                assert_eq!(parser.parse("test,test,test,test"), subtest!(__impl (++++) (0) $($x)*));
            )*
        };
    }

    subtest!(
        (..) => [Ok, Ok, Ok, Ok, Ok],
        (0..) => [Ok, Ok, Ok, Ok, Ok],
        (1..) => [Err, Ok, Ok, Ok, Ok],
        (2..) => [Err, Err, Ok, Ok, Ok],
        (..=0) => [Ok, Err, Err, Err, Err],
        (..=1) => [Ok, Ok, Err, Err, Err],
        (..=2) => [Ok, Ok, Ok, Err, Err],
        (..1) => [Ok, Err, Err, Err, Err],
        (..2) => [Ok, Ok, Err, Err, Err],
        (..3) => [Ok, Ok, Ok, Err, Err],
        (0..=2) => [Ok, Ok, Ok, Err, Err],
        (1..=1) => [Err, Ok, Err, Err, Err],
        (1..=3) => [Err, Ok, Ok, Ok, Err],
        (2..=2) => [Err, Err, Ok, Err, Err],
        (2..=3) => [Err, Err, Ok, Ok, Err],
        (0..3) => [Ok, Ok, Ok, Err, Err],
        (1..2) => [Err, Ok, Err, Err, Err],
        (1..4) => [Err, Ok, Ok, Ok, Err],
        (2..3) => [Err, Err, Ok, Err, Err],
        (2..4) => [Err, Err, Ok, Ok, Err]
    );
}

#[test]
fn test_maybe() {
    let parser = tag::<_, (), _>("test").maybe();
    assert_eq!(parser.parse("test"), Ok(Some("test")));
    assert_eq!(parser.parse(""), Ok(None));
}

#[test]
fn test_record() {
    let parser = tag("te").then(tag("st")).record();
    assert_eq!(parser.parse("test"), Ok("test"));
    assert_eq!(parser.parse(""), Err(()));
}

#[test]
fn test_epsilon() {
    let parser = epsilon();
    assert_eq!(parser.parse(""), Ok(()));
    assert_eq!(parser.parse("test"), Err(()));
}

#[test]
fn test_fail_with() {
    let parser = fail_with_const::<_, (), _>(());
    assert_eq!(parser.parse(""), Err(()));
    assert_eq!(parser.parse("test"), Err(()));
}

#[test]
fn test_eof() {
    let parser = eof().followed_by(tag("!").repeat::<NoCollection<_>, _>(..));
    assert_eq!(parser.parse(""), Ok(()));
    assert_eq!(parser.parse("!"), Err(()));
}

#[test]
fn test_not() {
    let parser = not(eof()).followed_by(tag("!").repeat::<NoCollection<_>, _>(..));
    assert_eq!(parser.parse(""), Err(()));
    assert_eq!(parser.parse("!"), Ok(()));
}

#[test]
fn test_record_while() {
    let parser = record_while(|c: &char| c.is_alphabetic(), 1..=2).then(take(..));
    assert_eq!(parser.parse(""), Err(()));
    assert_eq!(parser.parse("1def"), Err(()));
    assert_eq!(parser.parse("abcdef"), Ok(("ab", "cdef")));
    assert_eq!(parser.parse("a1bcdef"), Ok(("a", "1bcdef")));
}

#[test]
fn test_take() {
    let parser = take(1..=1);
    assert_eq!(parser.parse(""), Err(()));
    assert_eq!(parser.parse("x"), Ok("x"));
    assert_eq!(parser.parse("xx"), Err(()));
}
