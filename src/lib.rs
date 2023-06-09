#![feature(box_syntax, box_patterns)]

pub mod parser;

use std::{
    collections::{HashMap, HashSet},
    fmt,
    str::FromStr,
};

use color_eyre::{
    eyre::{eyre, ContextCompat},
    Result,
};
use nom::{combinator::eof, error::Error, sequence::terminated, Finish};
use num_bigint::BigUint;
use num_traits::{One, Zero};
use serde::{Deserialize, Serialize};
use sqlx::types::Json;

pub type Name = String;

#[derive(sqlx::FromRow)]
pub struct Var {
    pub name: Name,
    pub r#type: Json<Type>,
    pub value: Json<Value>,
    pub mutable: bool,
}

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} : {} := {}",
            self.name,
            self.r#type.quote(&HashSet::new()),
            self.value.quote(&HashSet::new()),
        )
    }
}

pub type Level = u8;

pub type Nat = BigUint;

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
pub enum Expr {
    Add(Box<Expr>, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
    Append(Box<Expr>, Box<Expr>),
    Ann(Box<Expr>, Box<Expr>),
    Bool,
    Char,
    CharLit(char),
    Cons(Box<Expr>, Box<Expr>),
    False,
    Fst(Box<Expr>),
    Fun(Box<Expr>, Box<Expr>),
    Lam(Name, Box<Expr>),
    List(Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Nat,
    NatLit(Nat),
    NatRec(Box<Expr>, Box<Expr>, Box<Expr>, Box<Expr>),
    Nil,
    Pair(Box<Expr>, Box<Expr>),
    Prod(Box<Expr>, Box<Expr>),
    Snd(Box<Expr>),
    Sole,
    String,
    StringLit(String),
    Succ(Box<Expr>),
    Trivial,
    True,
    U(Level),
    Var(Name),
    Vec(Box<Expr>, Box<Expr>),
    Zero,
}

pub type Ctx = HashMap<Name, Type>;

pub type Env = HashMap<Name, Value>;

#[derive(Eq, Ord, PartialEq, PartialOrd)]
enum Prec {
    Ann,
    Lam,
    Fun,
    Append,
    Add,
    Mul,
    Prod,
    App,
    Atom,
}

impl Expr {
    fn prec(&self) -> Prec {
        match self {
            Self::Ann(_, _) => Prec::Ann,
            Self::Lam(_, _) => Prec::Lam,
            Self::Fun(_, _) => Prec::Fun,
            Self::Append(_, _) => Prec::Append,
            Self::Add(_, _) => Prec::Add,
            Self::Mul(_, _) => Prec::Mul,
            Self::Prod(_, _) => Prec::Prod,
            Self::App(_, _) => Prec::App,
            _ => Prec::Atom,
        }
    }

    pub fn alpha_eq(&self, other: &Self) -> bool {
        let names = HashMap::new();
        self.alpha_eq_(other, 0, &names, &names)
    }

    pub fn alpha_eq_(
        &self,
        other: &Self,
        i: usize,
        xs: &HashMap<Name, usize>,
        ys: &HashMap<Name, usize>,
    ) -> bool {
        match (self, other) {
            (Self::App(e_1, e_2), Self::App(e_3, e_4)) => {
                e_1.alpha_eq_(e_3, i, xs, ys) && e_2.alpha_eq_(e_4, i, xs, ys)
            }
            (Self::Add(e_1, e_2), Self::Add(e_3, e_4)) => {
                e_1.alpha_eq_(e_3, i, xs, ys) && e_2.alpha_eq_(e_4, i, xs, ys)
            }
            (Self::Append(e_1, e_2), Self::Append(e_3, e_4)) => {
                e_1.alpha_eq_(e_3, i, xs, ys) && e_2.alpha_eq_(e_4, i, xs, ys)
            }
            (Self::Ann(e_1, e_2), Self::Ann(e_3, e_4)) => {
                e_1.alpha_eq_(e_3, i, xs, ys) && e_2.alpha_eq_(e_4, i, xs, ys)
            }
            (Self::Cons(e_1, e_2), Self::Cons(e_3, e_4)) => {
                e_1.alpha_eq_(e_3, i, xs, ys) && e_2.alpha_eq_(e_4, i, xs, ys)
            }
            (Self::Fst(e_1), Self::Fst(e_2)) => e_1.alpha_eq_(e_2, i, xs, ys),
            (Self::Fun(e_1, e_2), Self::Fun(e_3, e_4)) => {
                e_1.alpha_eq_(e_3, i, xs, ys) && e_2.alpha_eq_(e_4, i, xs, ys)
            }
            (Self::Lam(x, e_1), Self::Lam(y, e_2)) => e_1.alpha_eq_(
                e_2,
                i + 1,
                &{
                    let mut names = xs.to_owned();
                    names.insert(x.to_owned(), i);
                    names
                },
                &{
                    let mut other_names = ys.to_owned();
                    other_names.insert(y.to_owned(), i);
                    other_names
                },
            ),
            (Self::List(e_1), Self::List(e_2)) => e_1.alpha_eq_(e_2, i, xs, ys),
            (Self::Mul(e_1, e_2), Self::Mul(e_3, e_4)) => {
                e_1.alpha_eq_(e_3, i, xs, ys) && e_2.alpha_eq_(e_4, i, xs, ys)
            }
            (Self::NatRec(e_1, e_2, e_3, e_4), Self::NatRec(e_5, e_6, e_7, e_8)) => {
                e_1.alpha_eq_(e_5, i, xs, ys)
                    && e_2.alpha_eq_(e_6, i, xs, ys)
                    && e_3.alpha_eq_(e_7, i, xs, ys)
                    && e_4.alpha_eq_(e_8, i, xs, ys)
            }
            (Self::Pair(e_1, e_2), Self::Pair(e_3, e_4)) => {
                e_1.alpha_eq_(e_3, i, xs, ys) && e_2.alpha_eq_(e_4, i, xs, ys)
            }
            (Self::Prod(e_1, e_2), Self::Prod(e_3, e_4)) => {
                e_1.alpha_eq_(e_3, i, xs, ys) && e_2.alpha_eq_(e_4, i, xs, ys)
            }
            (Self::Snd(e_1), Self::Snd(e_2)) => e_1.alpha_eq_(e_2, i, xs, ys),
            (Self::Succ(e_1), Self::Succ(e_2)) => e_1.alpha_eq_(e_2, i, xs, ys),
            (Self::Var(x), Self::Var(y)) => match (xs.get(x), ys.get(y)) {
                (None, None) => x == y,
                (Some(j), Some(k)) => j == k,
                _ => false,
            },
            (Self::Vec(e_1, e_2), Self::Vec(e_3, e_4)) => {
                e_1.alpha_eq_(e_3, i, xs, ys) && e_2.alpha_eq_(e_4, i, xs, ys)
            }
            _ => self == other,
        }
    }

    pub fn check(&self, t: &Type, ctx: &Ctx, env: &Env) -> Result<()> {
        match (self, t) {
            (Self::Bool, Type::U(_i)) => Ok(()),
            (Self::Char, Type::U(_)) => Ok(()),
            (Self::CharLit(_), Type::Char) => Ok(()),
            (Self::Cons(e_1, e_2), Type::List(t_1)) => {
                e_1.check(t_1, ctx, env)?;
                e_2.check(t, ctx, env)
            }
            (Self::Cons(e_1, e_2), Type::Vec(t_1, box v)) => {
                e_1.check(t_1, ctx, env)?;

                let v = match v {
                    Value::NatLit(n) => {
                        if n.is_zero() {
                            return Err(eyre!("TODO"));
                        }

                        Value::NatLit(n - Nat::one())
                    }
                    Value::Neutral(Neutral::Succ(box n)) => Value::Neutral(n.to_owned()),
                    _ => unreachable!(),
                };

                e_2.check(&Type::Vec(t_1.to_owned(), box v), ctx, env)
            }
            (Self::False, Type::Bool) => Ok(()),
            (Self::Fun(e_1, e_2), Type::U(_)) => {
                e_1.check(t, ctx, env)?;
                e_2.check(t, ctx, env)
            }
            (Self::Lam(x, e), Type::Fun(box t_1, t_2)) => {
                let mut ctx = ctx.to_owned();
                ctx.insert(x.to_owned(), t_1.to_owned());
                e.check(t_2, &ctx, env)
            }
            (Self::List(e), Type::U(_)) => e.check(t, ctx, env),
            (Self::Nat, Type::U(_)) => Ok(()),
            (Self::NatLit(_), Type::Nat) => Ok(()),
            (Self::Nil, Type::List(_)) => Ok(()),
            (Self::Nil, Type::Vec(_, box Value::NatLit(n))) => {
                if !n.is_zero() {
                    dbg!(self, t.quote(&HashSet::new()));
                    return Err(eyre!("Type mismatch"));
                }

                Ok(())
            }
            (Self::Pair(e_1, e_2), Type::Prod(t_1, t_2)) => {
                e_1.check(t_1, ctx, env)?;
                e_2.check(t_2, ctx, env)
            }
            (Self::Prod(e_1, e_2), Type::U(_)) => {
                e_1.check(t, ctx, env)?;
                e_2.check(t, ctx, env)
            }
            (Self::Sole, Type::Trivial) => Ok(()),
            (Self::String, Type::U(_)) => Ok(()),
            (Self::StringLit(_), Type::String) => Ok(()),
            (Self::Succ(e), Type::Nat) => e.check(t, ctx, env),
            (Self::Trivial, Type::U(_i)) => Ok(()),
            (Self::True, Type::Bool) => Ok(()),
            (Self::U(i), Type::U(j)) if i < j => Ok(()),
            (Self::Vec(e_1, e_2), Type::U(_)) => {
                e_1.check(t, ctx, env)?;
                e_2.check(&Type::Nat, ctx, env)
            }
            (Self::Zero, Type::Nat) => Ok(()),
            _ => {
                let t_ = self.synth(ctx, env)?;
                let xs = HashSet::new();

                if !t_.quote(&xs).alpha_eq(&t.quote(&xs)) {
                    return Err(eyre!("Type mismatch"));
                }

                Ok(())
            }
        }
    }

    pub fn eval(&self, env: &Env) -> Value {
        match self {
            Self::Add(e_1, e_2) => {
                let v_1 = e_1.eval(env);
                let v_2 = e_2.eval(env);

                match (v_1, v_2) {
                    (Value::NatLit(m), Value::NatLit(n)) => Value::NatLit(m + n),
                    (Value::Neutral(n), v) => Value::add(n, v),
                    (v, Value::Neutral(n)) => Value::add(n, v),
                    _ => unreachable!(),
                }
            }
            Self::Ann(e, _) => e.eval(env),
            Self::App(e_1, e_2) => {
                let v_1 = e_1.eval(env);
                let v_2 = e_2.eval(env);

                v_1.app(v_2)
            }
            Self::Append(e_1, e_2) => {
                let v_1 = e_1.eval(env);
                let v_2 = e_2.eval(env);

                match (v_1, v_2) {
                    (Value::StringLit(s_1), Value::StringLit(s_2)) => Value::StringLit(s_1 + &s_2),
                    (Value::Neutral(n), v) => Value::append_0(n, v),
                    (v, Value::Neutral(n)) => Value::append_1(v, n),
                    _ => unreachable!(),
                }
            }
            Self::Bool => Value::Bool,
            Self::Char => Value::Char,
            &Self::CharLit(c) => Value::CharLit(c),
            Self::Cons(e_1, e_2) => Value::Cons(box e_1.eval(env), box e_2.eval(env)),
            Self::False => Value::False,
            Self::Fst(e) => match e.eval(env) {
                Value::Pair(box v, _) => v,
                Value::Neutral(n) => Value::fst(n),
                _ => unreachable!(),
            },
            Self::Fun(e_1, e_2) => Value::Fun(box e_1.eval(env), box e_2.eval(env)),
            Self::Lam(x, box e) => {
                let mut xs = HashSet::new();
                e.free_vars(&mut xs);

                let env_: Env = env
                    .iter()
                    .filter(|&(x, _)| xs.contains(x))
                    .map(|(x, v)| (x.to_owned(), v.to_owned()))
                    .collect();

                Value::Lam(env_, x.to_owned(), e.to_owned())
            }
            Self::List(e) => Value::List(box e.eval(env)),
            Self::Mul(e_1, e_2) => {
                let v_1 = e_1.eval(env);
                let v_2 = e_2.eval(env);

                match (v_1, v_2) {
                    (Value::NatLit(m), Value::NatLit(n)) => Value::NatLit(m * n),
                    (Value::Neutral(n), v) => Value::mul(n, v),
                    (v, Value::Neutral(n)) => Value::mul(n, v),
                    _ => unreachable!(),
                }
            }
            Self::Nat => Value::Nat,
            Self::NatLit(n) => Value::NatLit(n.to_owned()),
            Self::NatRec(e_1, e_2, e_3, e_4) => {
                e_1.eval(env)
                    .nat_rec(e_2.eval(env), e_3.eval(env), e_4.eval(env))
            }
            Self::Nil => Value::Nil,
            Self::Pair(e_1, e_2) => Value::Pair(box e_1.eval(env), box e_2.eval(env)),
            Self::Prod(e_1, e_2) => Value::Prod(box e_1.eval(env), box e_2.eval(env)),
            Self::Snd(e) => match e.eval(env) {
                Value::Pair(_, box v) => v,
                Value::Neutral(n) => Value::snd(n),
                _ => unreachable!(),
            },
            Self::Sole => Value::Sole,
            Self::String => Value::String,
            Self::StringLit(s) => Value::StringLit(s.to_owned()),
            Self::Succ(e) => {
                let v = e.eval(env);

                match v {
                    Value::NatLit(n) => Value::NatLit(n + Nat::one()),
                    Value::Neutral(n) => Value::succ(n),
                    _ => unreachable!(),
                }
            }
            Self::Trivial => Value::Trivial,
            Self::True => Value::True,
            &Self::U(i) => Value::U(i),
            Self::Var(x) => env
                .get(x)
                .cloned()
                .unwrap_or_else(|| Value::var(x.to_owned())),
            Self::Vec(e_1, e_2) => Value::Vec(box e_1.eval(env), box e_2.eval(env)),
            Self::Zero => Value::NatLit(Nat::zero()),
        }
    }

    pub fn free_vars(&self, xs: &mut HashSet<Name>) {
        match self {
            Self::Add(e_1, e_2) => {
                e_1.free_vars(xs);
                e_2.free_vars(xs);
            }
            Self::App(e_1, e_2) => {
                e_1.free_vars(xs);
                e_2.free_vars(xs);
            }
            Self::Append(e_1, e_2) => {
                e_1.free_vars(xs);
                e_2.free_vars(xs);
            }
            Self::Ann(e_1, e_2) => {
                e_1.free_vars(xs);
                e_2.free_vars(xs);
            }
            Self::Bool => {}
            Self::Char => {}
            Self::CharLit(_) => {}
            Self::Cons(e_1, e_2) => {
                e_1.free_vars(xs);
                e_2.free_vars(xs);
            }
            Self::False => {}
            Self::Fst(e) => e.free_vars(xs),
            Self::Fun(e_1, e_2) => {
                e_1.free_vars(xs);
                e_2.free_vars(xs);
            }
            Self::Lam(x, e) => {
                e.free_vars(xs);
                xs.remove(x);
            }
            Self::List(e) => e.free_vars(xs),
            Self::Mul(e_1, e_2) => {
                e_1.free_vars(xs);
                e_2.free_vars(xs);
            }
            Self::Nat => {}
            Self::NatLit(_) => {}
            Self::NatRec(e_1, e_2, e_3, e_4) => {
                e_1.free_vars(xs);
                e_2.free_vars(xs);
                e_3.free_vars(xs);
                e_4.free_vars(xs);
            }
            Self::Nil => {}
            Self::Pair(e_1, e_2) => {
                e_1.free_vars(xs);
                e_2.free_vars(xs);
            }
            Self::Prod(e_1, e_2) => {
                e_1.free_vars(xs);
                e_2.free_vars(xs);
            }
            Self::Snd(e) => e.free_vars(xs),
            Self::Sole => {}
            Self::String => {}
            Self::StringLit(_) => {}
            Self::Succ(e) => e.free_vars(xs),
            Self::Trivial => {}
            Self::True => {}
            Self::U(_) => {}
            Self::Var(x) => {
                xs.insert(x.to_owned());
            }
            Self::Vec(e_1, e_2) => {
                e_1.free_vars(xs);
                e_2.free_vars(xs);
            }
            Self::Zero => {}
        }
    }

    pub fn synth(&self, ctx: &Ctx, env: &Env) -> Result<Type> {
        match self {
            Self::Add(e_1, e_2) => {
                let t = Type::Nat;
                e_1.check(&t, ctx, env)?;
                e_2.check(&t, ctx, env)?;
                Ok(t)
            }
            Self::Ann(e_1, e_2) => {
                e_2.check(&Type::U(Level::MAX), ctx, env)?;
                let t = e_2.eval(env);
                e_1.check(&t, ctx, env)?;
                Ok(t)
            }
            Self::App(e_1, e_2) => {
                let t = e_1.synth(ctx, env)?;

                let Type::Fun(t_1, box t_2) = t else {
                    return Err(eyre!("Not a Fun"));
                };

                e_2.check(&t_1, ctx, env)?;

                Ok(t_2)
            }
            Self::Append(e_1, e_2) => {
                let t = Type::String;
                e_1.check(&t, ctx, env)?;
                e_2.check(&t, ctx, env)?;
                Ok(t)
            }
            Self::Bool => Ok(Type::U(0)),
            Self::Char => Ok(Type::U(0)),
            Self::CharLit(_) => Ok(Type::Char),
            Self::Cons(e_1, box e_2) => {
                if let Self::Nil = e_2 {
                    let t = e_1.synth(ctx, env)?;
                    return Ok(Type::Vec(box t, box Value::NatLit(Nat::one())));
                }

                let t = e_2.synth(ctx, env)?;

                let Type::Vec(box t, box v) = t else {
                    return Err(eyre!("Not a Vec"));
                };

                let v = match v {
                    Value::NatLit(n) => Value::NatLit(n + Nat::one()),
                    Value::Neutral(n) => Value::succ(n),
                    _ => unreachable!(),
                };

                e_1.check(&t, ctx, env)?;

                Ok(Type::Vec(box t, box v))
            }
            Self::False => Ok(Type::Bool),
            Self::Fst(e) => {
                let t = e.synth(ctx, env)?;

                let Type::Prod(box t, _) = t else {
                    return Err(eyre!("Not a Prod"));
                };

                Ok(t)
            }
            Self::Fun(e_1, e_2) => {
                let t = Type::U(Level::MAX);
                e_1.check(&t, ctx, env)?;
                e_2.check(&t, ctx, env)?;

                let i = if let Type::U(i) = e_1.eval(env) {
                    i.checked_add(1).wrap_err("TODO")?
                } else {
                    0
                };

                let j = if let Type::U(j) = e_2.eval(env) {
                    j.checked_add(1).wrap_err("TODO")?
                } else {
                    0
                };

                Ok(Type::U(i.max(j)))
            }
            Self::List(e) => {
                e.check(&Type::U(Level::MAX), ctx, env)?;

                let t = e.eval(env);

                let i = if let Type::U(i) = t {
                    i.checked_add(1).wrap_err("TODO")?
                } else {
                    0
                };

                Ok(Type::U(i))
            }
            Self::Mul(e_1, e_2) => {
                let t = Type::Nat;
                e_1.check(&t, ctx, env)?;
                e_2.check(&t, ctx, env)?;
                Ok(t)
            }
            Self::Nat => Ok(Type::U(0)),
            Self::NatLit(_) => Ok(Type::Nat),
            Self::NatRec(e_1, e_2, e_3, e_4) => {
                e_1.check(&Type::Nat, ctx, env)?;
                e_2.check(&Type::U(Level::MAX), ctx, env)?;
                let t = e_2.eval(env);
                e_3.check(&t, ctx, env)?;

                e_4.check(
                    &Type::Fun(box Type::Nat, box Type::Fun(box t.clone(), box t.clone())),
                    ctx,
                    env,
                )?;

                Ok(t)
            }
            Self::Pair(e_1, e_2) => {
                let t_1 = e_1.synth(ctx, env)?;
                let t_2 = e_2.synth(ctx, env)?;

                Ok(Type::Prod(box t_1, box t_2))
            }
            Self::Prod(e_1, e_2) => {
                let t = Type::U(Level::MAX);
                e_1.check(&t, ctx, env)?;
                e_2.check(&t, ctx, env)?;

                let i = if let Type::U(i) = e_1.eval(env) {
                    i.checked_add(1).wrap_err("TODO")?
                } else {
                    0
                };

                let j = if let Type::U(j) = e_2.eval(env) {
                    j.checked_add(1).wrap_err("TODO")?
                } else {
                    0
                };

                Ok(Type::U(i.max(j)))
            }
            Self::Snd(e) => {
                let t = e.synth(ctx, env)?;

                let Type::Prod(box t, _) = t else {
                    return Err(eyre!("Not a Prod"));
                };

                Ok(t)
            }
            Self::Sole => Ok(Type::Trivial),
            Self::String => Ok(Type::U(0)),
            Self::StringLit(_) => Ok(Type::String),
            Self::Succ(e) => {
                let t = Type::Nat;
                e.check(&t, ctx, env)?;
                Ok(t)
            }
            Self::Trivial => Ok(Type::U(0)),
            Self::True => Ok(Type::Bool),
            &Self::U(i) if i != Level::MAX => Ok(Type::U(i + 1)),
            Self::Var(x) => ctx.get(x).cloned().wrap_err("Not found"),
            Self::Vec(e_1, e_2) => {
                e_1.check(&Type::U(Level::MAX), ctx, env)?;
                e_2.check(&Type::Nat, ctx, env)?;

                let t = e_1.eval(env);

                let i = if let Type::U(i) = t {
                    i.checked_add(1).wrap_err("TODO")?
                } else {
                    0
                };

                Ok(Type::U(i))
            }
            Self::Zero => Ok(Type::Nat),
            _ => {
                dbg!(self);
                Err(eyre!("Failed to synthesize a type"))
            }
        }
    }
}

fn fmt_parens(cond: bool, d: impl fmt::Display, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    if cond {
        write!(f, "({d})")
    } else {
        d.fmt(f)
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Add(e_1, e_2) => {
                fmt_parens(self.prec() > e_1.prec(), e_1, f)?;
                write!(f, " + ")?;
                fmt_parens(self.prec() > e_2.prec(), e_2, f)
            }
            Self::App(box e_1, e_2) => {
                let mut e = e_1;
                let mut es = vec![];

                loop {
                    match e {
                        Self::App(e_1, box e_2) => {
                            es.push(e_2);
                            e = e_1;
                        }
                        Self::Var(x) => {
                            write!(f, "{x}(")?;
                            break;
                        }
                        _ => {
                            write!(f, "({e})(")?;
                            break;
                        }
                    }
                }

                for e in es.into_iter().rev() {
                    write!(f, "{e}, ")?;
                }

                write!(f, "{e_2})")
            }
            Self::Append(e_1, e_2) => {
                fmt_parens(self.prec() > e_1.prec(), e_1, f)?;
                write!(f, " ++ ")?;
                fmt_parens(self.prec() > e_2.prec(), e_2, f)
            }
            Self::Ann(e_1, e_2) => write!(f, "{e_1} : {e_2}"),
            Self::Bool => "Bool".fmt(f),
            Self::Char => "Char".fmt(f),
            Self::CharLit(c) => write!(f, "{c:?}"),
            Self::Cons(e_1, box e_2) => {
                write!(f, "[{e_1}")?;

                let mut e = e_2;

                loop {
                    match e {
                        Self::Cons(e_1, e_2) => {
                            write!(f, ", {e_1}")?;
                            e = e_2;
                        }
                        Self::Nil => break,
                        _ => {
                            write!(f, ", {e}")?;
                            break;
                        }
                    }
                }

                ']'.fmt(f)
            }
            Self::False => "false".fmt(f),
            Self::Fst(e) => write!(f, "fst({e})"),
            Self::Fun(e_1, e_2) => {
                fmt_parens(self.prec() >= e_1.prec(), e_1, f)?;
                write!(f, " → ")?;
                fmt_parens(self.prec() > e_2.prec(), e_2, f)
            }
            Self::Lam(x, e) => write!(f, "λ {x}. {e}"),
            Self::List(e) => write!(f, "List({e})"),
            Self::Mul(e_1, e_2) => {
                fmt_parens(self.prec() > e_1.prec(), e_1, f)?;
                write!(f, " * ")?;
                fmt_parens(self.prec() > e_2.prec(), e_2, f)
            }
            Self::Nil => "[]".fmt(f),
            Self::Nat => "Nat".fmt(f),
            Self::NatLit(n) => n.fmt(f),
            Self::NatRec(e_1, e_2, e_3, e_4) => write!(f, "natRec({e_1}, {e_2}, {e_3}, {e_4})"),
            Self::Pair(e_1, box e_2) => {
                write!(f, "({e_1}")?;

                let mut e = e_2;

                loop {
                    ", ".fmt(f)?;

                    let Self::Pair(e_1, e_2) = e else {
                        e.fmt(f)?;
                        break;
                    };

                    e_1.fmt(f)?;
                    e = e_2;
                }

                ')'.fmt(f)
            }
            Self::Prod(e_1, e_2) => {
                fmt_parens(self.prec() >= e_1.prec(), e_1, f)?;
                write!(f, " × ")?;
                fmt_parens(self.prec() > e_2.prec(), e_2, f)
            }
            Self::Snd(e) => write!(f, "snd({e})"),
            Self::Sole => "()".fmt(f),
            Self::String => "String".fmt(f),
            Self::StringLit(s) => write!(f, "{s:?}"),
            Self::Succ(e) => write!(f, "succ({e})"),
            Self::Trivial => "Trivial".fmt(f),
            Self::True => "true".fmt(f),
            Self::U(i) => write!(f, "U({i})"),
            Self::Var(x) => x.fmt(f),
            Self::Vec(e_1, e_2) => write!(f, "Vec({e_1}, {e_2})"),
            Self::Zero => "zero".fmt(f),
        }
    }
}

pub type Type = Value;

#[derive(Clone, Debug, Deserialize, Serialize)]
pub enum Neutral {
    Add(Box<Neutral>, Box<Value>),
    Append0(Box<Neutral>, Box<Value>),
    Append1(Box<Value>, Box<Neutral>),
    Fst(Box<Neutral>),
    Mul(Box<Neutral>, Box<Value>),
    NatRec(Box<Neutral>, Box<Value>, Box<Value>, Box<Value>),
    Snd(Box<Neutral>),
    Succ(Box<Neutral>),
    Var(Name),
}

impl Neutral {
    pub fn quote(&self, xs: &HashSet<Name>) -> Expr {
        match self {
            Self::Add(n, v) => Expr::Add(box n.quote(xs), box v.quote(xs)),
            Self::Append0(n, v) => Expr::Append(box n.quote(xs), box v.quote(xs)),
            Self::Append1(v, n) => Expr::Append(box v.quote(xs), box n.quote(xs)),
            Self::Fst(n) => Expr::Fst(box n.quote(xs)),
            Self::Mul(n, v) => Expr::Mul(box n.quote(xs), box v.quote(xs)),
            Self::NatRec(n, v_1, v_2, v_3) => Expr::NatRec(
                box n.quote(xs),
                box v_1.quote(xs),
                box v_2.quote(xs),
                box v_3.quote(xs),
            ),
            Self::Snd(n) => Expr::Snd(box n.quote(xs)),
            Self::Succ(n) => Expr::Succ(box n.quote(xs)),
            Self::Var(x) => Expr::Var(x.to_owned()),
        }
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub enum Value {
    Bool,
    Char,
    CharLit(char),
    Cons(Box<Value>, Box<Value>),
    False,
    Fun(Box<Value>, Box<Value>),
    Lam(Env, Name, Expr),
    List(Box<Value>),
    Nat,
    NatLit(Nat),
    Neutral(Neutral),
    Nil,
    Pair(Box<Value>, Box<Value>),
    Prod(Box<Value>, Box<Value>),
    Sole,
    String,
    StringLit(String),
    Trivial,
    True,
    U(Level),
    Vec(Box<Value>, Box<Value>),
}

fn freshen(mut x: Name, xs: &HashSet<Name>) -> Name {
    if xs.contains(&x) {
        x.push('\'');
        return freshen(x, xs);
    }

    x
}

impl Value {
    fn add(n: Neutral, v: Self) -> Self {
        Self::Neutral(Neutral::Add(box n, box v))
    }

    fn app(self, v: Self) -> Self {
        let Value::Lam(mut env, x, e) = self else {
            unreachable!();
        };

        env.insert(x, v);

        e.eval(&env)
    }

    fn append_0(n: Neutral, v: Self) -> Self {
        Self::Neutral(Neutral::Append0(box n, box v))
    }

    fn append_1(v: Self, n: Neutral) -> Self {
        Self::Neutral(Neutral::Append1(box v, box n))
    }

    fn fst(n: Neutral) -> Self {
        Self::Neutral(Neutral::Snd(box n))
    }

    pub fn quote(&self, xs: &HashSet<Name>) -> Expr {
        match self {
            Self::Bool => Expr::Bool,
            Self::Char => Expr::Char,
            &Self::CharLit(c) => Expr::CharLit(c),
            Self::Cons(v_1, v_2) => Expr::Cons(box v_1.quote(xs), box v_2.quote(xs)),
            Self::False => Expr::False,
            Self::Fun(v_1, v_2) => Expr::Fun(box v_1.quote(xs), box v_2.quote(xs)),
            Self::List(v) => Expr::List(box v.quote(xs)),
            Self::Lam(env, x, e) => {
                let y = freshen(x.to_owned(), xs);
                let mut ys = xs.to_owned();
                ys.insert(y.clone());

                let mut env = env.to_owned();
                env.insert(y.clone(), Value::var(y.clone()));

                Expr::Lam(y, box e.eval(&env).quote(&ys))
            }
            Self::Neutral(n) => n.quote(xs),
            Self::Nat => Expr::Nat,
            Self::NatLit(n) => Expr::NatLit(n.to_owned()),
            Self::Nil => Expr::Nil,
            Self::Pair(v_1, v_2) => Expr::Pair(box v_1.quote(xs), box v_2.quote(xs)),
            Self::Prod(v_1, v_2) => Expr::Prod(box v_1.quote(xs), box v_2.quote(xs)),
            Self::Sole => Expr::Sole,
            Self::String => Expr::String,
            Self::StringLit(s) => Expr::StringLit(s.to_owned()),
            Self::Trivial => Expr::Trivial,
            Self::True => Expr::True,
            &Self::U(i) => Expr::U(i),
            Self::Vec(v_1, v_2) => Expr::Vec(box v_1.quote(xs), box v_2.quote(xs)),
        }
    }

    fn mul(n: Neutral, v: Self) -> Self {
        Self::Neutral(Neutral::Mul(box n, box v))
    }

    fn nat_rec(self, v_1: Self, v_2: Self, v_3: Self) -> Self {
        match self {
            Value::NatLit(n) if n.is_zero() => v_2,
            Value::NatLit(n) => {
                let v = Value::NatLit(n - Nat::one());
                v_3.clone().app(v.clone()).app(v.nat_rec(v_1, v_2, v_3))
            }
            Value::Neutral(Neutral::Succ(box n)) => {
                let v = Value::Neutral(n);
                v_3.clone().app(v.clone()).app(v.nat_rec(v_1, v_2, v_3))
            }
            Value::Neutral(n) => Value::Neutral(Neutral::NatRec(box n, box v_1, box v_2, box v_3)),
            _ => unreachable!(),
        }
    }

    fn snd(n: Neutral) -> Self {
        Self::Neutral(Neutral::Snd(box n))
    }

    fn succ(n: Neutral) -> Self {
        Self::Neutral(Neutral::Succ(box n))
    }

    fn var(name: Name) -> Self {
        Self::Neutral(Neutral::Var(name))
    }
}

#[derive(Clone)]
pub enum Command {
    Eval(Expr),
    Let(bool, Name, Expr),
    List,
    Quit,
}

impl FromStr for Command {
    type Err = Error<String>;

    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        let (_remaining, expr) = terminated(parser::parse_command, eof)(s.trim())
            .finish()
            .map_err(|e| Error {
                input: e.input.to_string(),
                code: e.code,
            })?;

        Ok(expr)
    }
}
