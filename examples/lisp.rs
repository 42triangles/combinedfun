use std::fmt;
use std::io::prelude::*;
use std::convert::{TryFrom, TryInto};

use combinedfun as cf;
use cf::types::VerboseError;
use cf::str_parsers as sp;

#[derive(Clone, Debug)]
pub enum Value {
    Str(String),
    Int(i32),
    Float(f32),
    List(Vec<Value>),
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Value::Str(ref s) => write!(f, "{:?}", s),
            Value::Int(ref i) => write!(f, "{:?}", i),
            Value::Float(ref fl) => write!(f, "{:?}", fl),
            Value::List(ref l) => {
                write!(f, "(")?;
                let mut first = true;
                for i in l {
                    if first {
                        first = false;
                    } else {
                        write!(f, " ")?;
                    }
                    write!(f, "{}", i)?;
                }
                write!(f, ")")?;
                Ok(())
            },
        }
    }
}

type ParserInput<'a> = cf::Span<&'a str, cf::Pos>;
pub type ParserError<'a> = VerboseError<'a, ParserInput<'a>, (), str>;

type ParserResult<'a, Out> = Result<(ParserInput<'a>, Out), ParserError<'a>>;

fn parse_partial(i: ParserInput) -> ParserResult<Value> {
    fn string(i: ParserInput) -> ParserResult<String> {
        (
            -cf::tag("\"")
            >> cf::record_while(|&c: &char| c != '"', ..)
            >> -cf::tag("\"")
            >> ToOwned::to_owned
        ).parse_partial(i)
    }

    fn consume_digits<'a, R: cf::RangeLike>(range: R) -> cf::parser!(<ParserInput<'a>, (), ParserError<'a>>) {
        cf::consume_while(|&c: &char| c.is_digit(10), range)
    }

    fn float_e(i: ParserInput) -> ParserResult<()> {
        (
            -cf::tag("e")
            >> -(cf::tag("-") | ())
            >> -consume_digits(1..)
            >> cf::epsilon()
        ).parse_partial(i)
    }

    // NOTE: You could combine `float` and `int` to one parser that may return either, by capturing
    // wether or not an "e" or a dot occured, and choosing the right method based on that.
    // Actually, we already have the handy `Number` type below anyways.

    fn float(i: ParserInput) -> ParserResult<f32> {
        (
            (
                -(cf::tag("-") | ())
                >> (
                    -cf::tag(".") >> -consume_digits(1..) >> cf::epsilon()
                    |
                    -consume_digits(1..) >> (
                        -cf::tag(".") >> -consume_digits(0..) >> -(cf::f(float_e) | ()) >> cf::epsilon()
                        |
                        -cf::f(float_e) >> cf::epsilon()
                    )
                )
            ).record()
            >> (|s: &str| s.parse::<f32>().unwrap())
        ).parse_partial(i)
    }

    fn int(i: ParserInput) -> ParserResult<i32> {
        (
            (
                -(cf::tag("-") | ())
                >> cf::consume_while(|&c: &char| c.is_digit(10), 1..)
            ).record()
            >> (|s: &str| s.parse::<i32>().unwrap())
        ).parse_partial(i)
    }

    fn list(i: ParserInput) -> ParserResult<Vec<Value>> {
        (
            -cf::tag("(")
            >> cf::f(parse_partial) / sp::ws(1..) * Vec::new * ..
            >> -sp::ws(..)
            >> -cf::tag(")")
        ).parse_partial(i)
    }

    (
        -sp::ws(..)
        >> (
            cf::f(string) >> Value::Str
            | cf::f(float) >> Value::Float
            | cf::f(int) >> Value::Int
            | cf::f(list) >> Value::List
        )
    ).parse_partial(i)
}

pub fn parse(i: &str) -> Result<Value, ParserError> {
    (cf::f(parse_partial) >> -sp::ws(..)).parse(ParserInput::new(i))
}

#[derive(Clone, Debug)]
pub enum LispError {
    EmptyCommand,
    ExpectedCommand(Value),
    ExpectedCommandWithArgs(Value),
    ExpectedNumber(Value),
    WrongArgCountDivision(Vec<Value>),
    WrongArgCountQuote(Vec<Value>),
    UndefinedFunction(String),
}

enum Number {
    Int(i32),
    Float(f32),
}

impl From<Number> for Value {
    fn from(number: Number) -> Self {
        match number {
            Number::Int(i) => Value::Int(i),
            Number::Float(f) => Value::Float(f),
        }
    }
}

impl<'a> TryFrom<&'a Value> for Number {
    type Error = LispError;

    fn try_from(value: &'a Value) -> Result<Number, LispError> {
        match *value {
            Value::Int(i) => Ok(Number::Int(i)),
            Value::Float(f) => Ok(Number::Float(f)),
            ref inp @ Value::List(_) => match evaluate(inp)? {
                Value::Int(i) => Ok(Number::Int(i)),
                Value::Float(f) => Ok(Number::Float(f)),
                ref val => Err(LispError::ExpectedNumber(val.clone())),
            },
            ref val => Err(LispError::ExpectedNumber(val.clone())),
        }
    }
}

impl<'a> TryFrom<&'a Value> for f32 {
    type Error = LispError;

    fn try_from(value: &'a Value) -> Result<f32, LispError> {
        match value.try_into()? {
            Number::Float(f) => Ok(f),
            Number::Int(i) => Ok(i as f32),
        }
    }
}

pub fn evaluate(v: &Value) -> Result<Value, LispError> {
    macro_rules! cmd {
        ($elements:expr, neutral = $neutral:expr, $op:tt) => {
                $elements.iter().skip(1).fold(Ok(Number::Int($neutral)), |acc, next| match acc? {  // there's probably a way to stop early but I'm just too lazy to look it up
                    Number::Int(i) => match next.try_into()? {
                        Number::Int(i2) => Ok(Number::Int(i $op i2)),
                        Number::Float(f) => Ok(Number::Float(i as f32 $op f)),
                    },
                    Number::Float(f) => Ok(Number::Float(f $op f32::try_from(next)?)),
                }).map(Into::into)
        };
    }

    match *v {
        Value::List(ref elements) => {
            if let Some(first) = elements.first() {
                match *first {
                    Value::Str(ref s) => match &**s {
                        "+" => cmd!(elements, neutral = 0, +),
                        "-" => cmd!(elements, neutral = 0, +),
                        "*" => cmd!(elements, neutral = 0, +),
                        "/" => if elements.len() == 3 {
                            Ok(Value::Float(f32::try_from(&elements[1])? / f32::try_from(&elements[2])?))
                        } else {
                            Err(LispError::WrongArgCountDivision(elements.clone()))
                        },
                        "quote" => if elements.len() == 2 {
                            Ok(elements[1].clone())
                        } else {
                            Err(LispError::WrongArgCountQuote(elements.clone()))
                        },
                        s => Err(LispError::UndefinedFunction(s.to_owned())),
                    },
                    ref x => Err(LispError::ExpectedCommand(x.clone())),
                }
            } else {
                Err(LispError::EmptyCommand)
            }
        },
        ref v => Err(LispError::ExpectedCommandWithArgs(v.clone())),
    }
}

fn main() {
    let mut input = String::new();
    std::io::stdin().read_to_string(&mut input).unwrap();

    let expression = match parse(&input) {
        Ok(expression) => expression,
        Err(error) => {
            eprintln!("Encountered an error while parsing:\n{:#?}", error);
            return;
        },
    };
    let result = evaluate(&expression);
    match result {
        Ok(value) => println!("{}", value),
        Err(error) => eprintln!("Encountered an error while evaluating:\n{:#?}", error),
    }
}
