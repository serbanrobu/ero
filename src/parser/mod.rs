mod string;

use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{alpha1, alphanumeric1, char, digit1, multispace0, multispace1, u8},
    combinator::{map, opt, recognize, value},
    multi::{many0, separated_list0, separated_list1},
    sequence::{delimited, pair, preceded, separated_pair, tuple},
    IResult,
};

use crate::{Command, Expr};

use string::parse_string;

use self::string::parse_char;

fn parse_name(input: &str) -> IResult<&str, String> {
    map(
        recognize(pair(
            alt((alpha1, tag("_"))),
            many0(alt((alphanumeric1, tag("_"), tag("\'")))),
        )),
        |s: &str| s.to_owned(),
    )(input)
}

fn parse_atom(input: &str) -> IResult<&str, Expr> {
    alt((
        map(
            parens(separated_list0(char(','), ws(parse_expr))),
            |mut es| {
                let Some(e) = es.pop() else {
                    return Expr::Sole;
                };

                es.into_iter()
                    .rev()
                    .fold(e, |acc, e| Expr::Pair(box e, box acc))
            },
        ),
        map(brackets(separated_list0(char(','), ws(parse_expr))), |es| {
            es.into_iter()
                .rev()
                .fold(Expr::Nil, |acc, e| Expr::Cons(box e, box acc))
        }),
        map(parse_string, Expr::StringLit),
        map(parse_char, Expr::CharLit),
        alt((
            value(Expr::Bool, tag("Bool")),
            value(Expr::Char, tag("Char")),
            value(Expr::False, tag("false")),
            value(Expr::Nat, tag("Nat")),
            value(Expr::Nil, tag("nil")),
            value(Expr::Sole, tag("sole")),
            value(Expr::String, tag("String")),
            value(Expr::Trivial, tag("Trivial")),
            value(Expr::True, tag("true")),
        )),
        map(digit1, |s: &str| Expr::NatLit(s.parse().unwrap())),
        map(
            preceded(
                pair(tag("cons"), multispace0),
                parens(separated_pair(ws(parse_expr), char(','), ws(parse_expr))),
            ),
            |(e_1, e_2)| Expr::Cons(box e_1, box e_2),
        ),
        map(
            preceded(pair(tag("fst"), multispace0), parens(ws(parse_expr))),
            |e| Expr::Fst(box e),
        ),
        map(
            preceded(pair(tag("List"), multispace0), parens(ws(parse_expr))),
            |e| Expr::List(box e),
        ),
        map(
            preceded(
                pair(tag("natRec"), multispace0),
                parens(tuple((
                    ws(parse_expr),
                    preceded(char(','), ws(parse_expr)),
                    preceded(char(','), ws(parse_expr)),
                    preceded(char(','), ws(parse_expr)),
                ))),
            ),
            |(e_1, e_2, e_3, e_4)| Expr::NatRec(box e_1, box e_2, box e_3, box e_4),
        ),
        map(
            preceded(
                pair(tag("pair"), multispace0),
                parens(separated_pair(ws(parse_expr), char(','), ws(parse_expr))),
            ),
            |(e_1, e_2)| Expr::Pair(box e_1, box e_2),
        ),
        map(
            preceded(
                pair(tag("Prod"), multispace0),
                parens(separated_pair(ws(parse_expr), char(','), ws(parse_expr))),
            ),
            |(e_1, e_2)| Expr::Prod(box e_1, box e_2),
        ),
        map(
            preceded(pair(tag("snd"), multispace0), parens(ws(parse_expr))),
            |e| Expr::Snd(box e),
        ),
        map(
            preceded(pair(tag("succ"), multispace0), parens(ws(parse_expr))),
            |e| Expr::Succ(box e),
        ),
        map(
            preceded(pair(char('U'), multispace0), parens(ws(u8))),
            Expr::U,
        ),
        map(
            preceded(
                pair(tag("Vec"), multispace0),
                parens(separated_pair(ws(parse_expr), char(','), ws(parse_expr))),
            ),
            |(e_1, e_2)| Expr::Vec(box e_1, box e_2),
        ),
        map(parse_name, Expr::Var),
    ))(input)
}

fn parse_app(input: &str) -> IResult<&str, Expr> {
    map(
        pair(
            parse_atom,
            many0(parens(separated_list1(char(','), ws(parse_expr)))),
        ),
        |(e, es)| {
            es.into_iter()
                .flatten()
                .fold(e, |acc, e| Expr::App(box acc, box e))
        },
    )(input)
}

fn parse_prod(input: &str) -> IResult<&str, Expr> {
    map(separated_list1(ws(char('×')), parse_app), |es| {
        es.into_iter()
            .rev()
            .reduce(|acc, e| Expr::Prod(box e, box acc))
            .unwrap()
    })(input)
}

fn parse_mul(input: &str) -> IResult<&str, Expr> {
    map(separated_list1(ws(char('*')), parse_prod), |es| {
        es.into_iter()
            .reduce(|acc, e| Expr::Mul(box acc, box e))
            .unwrap()
    })(input)
}

fn parse_add(input: &str) -> IResult<&str, Expr> {
    map(separated_list1(ws(char('+')), parse_mul), |es| {
        es.into_iter()
            .reduce(|acc, e| Expr::Add(box acc, box e))
            .unwrap()
    })(input)
}

fn parse_append(input: &str) -> IResult<&str, Expr> {
    map(separated_list1(ws(tag("++")), parse_add), |es| {
        es.into_iter()
            .reduce(|acc, e| Expr::Append(box acc, box e))
            .unwrap()
    })(input)
}

fn parse_fun(input: &str) -> IResult<&str, Expr> {
    map(separated_list1(ws(char('→')), parse_append), |es| {
        es.into_iter()
            .rev()
            .reduce(|acc, e| Expr::Fun(box e, box acc))
            .unwrap()
    })(input)
}

fn parse_lam(input: &str) -> IResult<&str, Expr> {
    alt((
        map(
            preceded(
                pair(char('λ'), multispace1),
                separated_pair(parse_name, ws(char('.')), parse_lam),
            ),
            |(x, e)| Expr::Lam(x, box e),
        ),
        parse_fun,
    ))(input)
}

fn parse_ann(input: &str) -> IResult<&str, Expr> {
    map(
        pair(parse_lam, opt(preceded(ws(char(':')), parse_lam))),
        |(e_1, e_2)| match e_2 {
            Some(e_2) => Expr::Ann(box e_1, box e_2),
            None => e_1,
        },
    )(input)
}

fn parse_expr(input: &str) -> IResult<&str, Expr> {
    parse_ann(input)
}

pub fn parse_command(input: &str) -> IResult<&str, Command> {
    alt((
        value(Command::List, tag(":list")),
        value(Command::Quit, pair(tag(":q"), opt(tag("uit")))),
        map(
            tuple((
                preceded(
                    pair(tag(":let"), multispace1),
                    map(opt(pair(tag("mut"), multispace1)), |o| o.is_some()),
                ),
                parse_name,
                preceded(ws(tag(":=")), parse_expr),
            )),
            |(mutable, x, e)| Command::Let(mutable, x, e),
        ),
        map(parse_expr, Command::Eval),
    ))(input)
}

pub fn parens<'a, F, O>(inner: F) -> impl FnMut(&'a str) -> IResult<&'a str, O>
where
    F: FnMut(&'a str) -> IResult<&'a str, O>,
{
    delimited(char('('), inner, char(')'))
}

pub fn brackets<'a, F, O>(inner: F) -> impl FnMut(&'a str) -> IResult<&'a str, O>
where
    F: FnMut(&'a str) -> IResult<&'a str, O>,
{
    delimited(char('['), inner, char(']'))
}

pub fn ws<'a, F: 'a, O>(inner: F) -> impl FnMut(&'a str) -> IResult<&'a str, O>
where
    F: FnMut(&'a str) -> IResult<&'a str, O>,
{
    delimited(multispace0, inner, multispace0)
}
