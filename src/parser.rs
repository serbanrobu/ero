use nom::{
    branch::alt,
    bytes::complete::{tag, tag_no_case},
    character::complete::{multispace1, u8},
    combinator::{map, value},
    sequence::{pair, preceded},
    IResult,
};

use crate::Expr;

pub fn parse_expr(input: &str) -> IResult<&str, Expr> {
    alt((
        value(Expr::Bool, tag("Bool")),
        value(Expr::False, tag("false")),
        value(Expr::True, tag("true")),
        map(preceded(pair(tag("U"), multispace1), u8), Expr::U),
        value(Expr::Unit, tag_no_case("unit")),
    ))(input)
}
