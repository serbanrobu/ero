use color_eyre::{eyre::eyre, Result};
use serde::Deserialize;
use sqlx::types::Json;

pub mod parser;

#[derive(Debug, sqlx::FromRow)]
pub struct Entity {
    pub name: String,
    pub r#type: Json<Type>,
    pub value: Json<Value>,
}

#[derive(Clone)]
pub enum Expr {
    Bool,
    False,
    True,
    U(u8),
    Unit,
}

impl Expr {
    pub fn check(&self, r#type: &Type) -> Result<()> {
        match (self, r#type) {
            (Self::Bool, Type::U(_i)) => Ok(()),
            (Self::False | Self::True, Type::Bool) => Ok(()),
            (Self::U(i), Type::U(j)) if i < j => Ok(()),
            (Self::Unit, Type::U(_i)) => Ok(()),
            (Self::Unit, Type::Unit) => Ok(()),
            _ => Err(eyre!("Type mismatch")),
        }
    }

    pub fn eval(&self) -> Value {
        match self {
            Self::Bool => Value::Bool,
            Self::False => Value::False,
            Self::True => Value::True,
            &Self::U(i) => Value::U(i),
            Self::Unit => Value::Unit,
        }
    }
}

pub type Type = Value;

#[derive(Debug, Deserialize)]
pub enum Value {
    Bool,
    False,
    True,
    U(u8),
    Unit,
}
