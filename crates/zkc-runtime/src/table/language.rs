use crate::{
    Error, Library, Sort,
    format::{list, natural, string},
};
use num_bigint::BigUint;
use serde_json::{Value, json};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Domain {
    Two,
    Seven,
}
impl Domain {
    pub fn modulus(self) -> u8 {
        match self {
            Self::Two => 2,
            Self::Seven => 7,
        }
    }
    pub fn name(self) -> &'static str {
        match self {
            Self::Two => "f2",
            Self::Seven => "f7",
        }
    }
    pub fn decode(value: &Value) -> Result<Self, Error> {
        match string(value)? {
            "f2" => Ok(Self::Two),
            "f7" => Ok(Self::Seven),
            _ => Err(Error("unknown-domain")),
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Boolean,
    Digest,
    Summary,
    Scalar(Domain),
    Point(Domain),
    Table(Domain, BigUint),
    Residual(Domain, BigUint),
}
impl Type {
    pub fn decode(value: &Value) -> Result<Self, Error> {
        let a = list(value)?;
        match a {
            [tag] => match string(tag)? {
                "bool" => Ok(Self::Boolean),
                "digest" => Ok(Self::Digest),
                "summary" => Ok(Self::Summary),
                _ => Err(Error("unknown-type")),
            },
            [tag, domain] => match string(tag)? {
                "scalar" => Ok(Self::Scalar(Domain::decode(domain)?)),
                "point" => Ok(Self::Point(Domain::decode(domain)?)),
                _ => Err(Error("unknown-type")),
            },
            [tag, domain, rank] => match string(tag)? {
                "table" => Ok(Self::Table(Domain::decode(domain)?, natural(rank)?)),
                "residual" => Ok(Self::Residual(Domain::decode(domain)?, natural(rank)?)),
                _ => Err(Error("unknown-type")),
            },
            _ => Err(Error("unknown-type")),
        }
    }
    pub fn sort(&self) -> Sort {
        use Type::*;
        Sort(match self {
            Boolean => json!(["bool"]),
            Digest => json!(["digest"]),
            Summary => json!(["summary"]),
            Scalar(d) => json!(["scalar", d.name()]),
            Point(d) => json!(["point", d.name()]),
            Table(d, n) => json!(["table", d.name(), crate::format::number(n)]),
            Residual(d, n) => json!(["residual", d.name(), crate::format::number(n)]),
        })
    }
}
#[derive(Clone, Debug)]
pub enum Operation {
    View(Domain, BigUint),
    Restrict(Domain, BigUint),
    Evaluate(Domain, BigUint),
    Add(Domain),
    Record(Domain),
    AbortWrite(Domain),
    OrderedPair,
    Pack,
    Send,
    Draw,
    Linear,
    Point,
    EndpointPoint(bool),
    Equal,
    Parent(bool),
    DigestEqual,
}
#[derive(Clone, Copy, Debug)]
pub struct TableLibrary;
impl Library for TableLibrary {
    type Operation = Operation;
    fn condition_sort(&self) -> Sort {
        Type::Boolean.sort()
    }
    fn sort(&self, value: &Value) -> Result<Sort, Error> {
        Ok(Type::decode(value)?.sort())
    }
    fn dependencies(&self) -> Value {
        json!([["table-protocol", "1"]])
    }
    fn operation(&self, value: &Value) -> Result<Operation, Error> {
        use Operation::*;
        let a = list(value)?;
        match a {
            [tag, d, n] => {
                let d = Domain::decode(d)?;
                let n = natural(n)?;
                match string(tag)? {
                    "view" => Ok(View(d, n)),
                    "restrict" => Ok(Restrict(d, n)),
                    "evaluate" => Ok(Evaluate(d, n)),
                    _ => Err(Error("unknown-operation")),
                }
            }
            [tag, value] => match string(tag)? {
                "parent" => Ok(Parent(value.as_bool().ok_or(Error("expected-boolean"))?)),
                "endpoint_point" => Ok(EndpointPoint(
                    value.as_bool().ok_or(Error("expected-boolean"))?,
                )),
                "add" => Ok(Add(Domain::decode(value)?)),
                "record" => Ok(Record(Domain::decode(value)?)),
                "abort_write" => Ok(AbortWrite(Domain::decode(value)?)),
                _ => Err(Error("unknown-operation")),
            },
            [tag] => match string(tag)? {
                "ordered_pair" => Ok(OrderedPair),
                "pack" => Ok(Pack),
                "send" => Ok(Send),
                "draw" => Ok(Draw),
                "linear" => Ok(Linear),
                "point" => Ok(Point),
                "equal" => Ok(Equal),
                "digest_equal" => Ok(DigestEqual),
                _ => Err(Error("unknown-operation")),
            },
            _ => Err(Error("unknown-operation")),
        }
    }
    fn signature(&self, op: &Operation) -> (Vec<Sort>, Sort) {
        use Operation::*;
        use Type as T;
        let f = T::Scalar(Domain::Seven);
        let (a, r) = match op {
            View(d, n) => (vec![T::Table(*d, n.clone())], T::Residual(*d, n.clone())),
            Restrict(d, n) => (
                vec![T::Residual(*d, n.clone()), T::Scalar(*d)],
                T::Residual(*d, n.clone()),
            ),
            Evaluate(d, n) => (
                vec![T::Residual(*d, n.clone()), T::Point(*d)],
                T::Scalar(*d),
            ),
            Add(d) => (vec![T::Scalar(*d), T::Scalar(*d)], T::Scalar(*d)),
            Record(d) | AbortWrite(d) => (vec![T::Scalar(*d)], T::Boolean),
            OrderedPair | Parent(_) => (vec![T::Digest, T::Digest], T::Digest),
            Pack => (
                vec![T::Scalar(Domain::Two), f.clone(), T::Digest],
                T::Summary,
            ),
            Send | Equal => (vec![f.clone(), f.clone()], T::Boolean),
            Draw => (vec![], f.clone()),
            Linear => (vec![f.clone(), f.clone(), f], T::Scalar(Domain::Seven)),
            Point => (vec![f], T::Point(Domain::Seven)),
            EndpointPoint(_) => (vec![], T::Point(Domain::Seven)),
            DigestEqual => (vec![T::Digest, T::Digest], T::Boolean),
        };
        (a.iter().map(T::sort).collect(), r.sort())
    }
}
