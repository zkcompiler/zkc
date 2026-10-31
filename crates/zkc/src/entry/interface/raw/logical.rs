//! Typed conditional carrier fields. Absence and explicit null are distinct.
use serde::{
    Deserialize, Deserializer,
    de::{Error, SeqAccess, Visitor},
};
use std::fmt;

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub enum Present<T> {
    #[default]
    Absent,
    Value(T),
}
impl<T> Present<T> {
    pub fn get(&self) -> Option<&T> {
        match self {
            Self::Absent => None,
            Self::Value(value) => Some(value),
        }
    }
}
impl<'de, T: Deserialize<'de>> Deserialize<'de> for Present<T> {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        T::deserialize(d).map(Self::Value)
    }
}
/// Canonical decimal strings preserve the full unsigned shape/capacity range.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Unsigned(pub u64);
impl<'de> Deserialize<'de> for Unsigned {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let text = String::deserialize(d)?;
        if text.is_empty()
            || text.len() > 20
            || (text.len() > 1 && text.starts_with('0'))
            || !text.bytes().all(|b| b.is_ascii_digit())
        {
            return Err(D::Error::custom("expected canonical u64 decimal string"));
        }
        text.parse().map(Self).map_err(D::Error::custom)
    }
}
#[derive(Clone, Debug, PartialEq, Eq, Deserialize)]
#[serde(remote = "Self", deny_unknown_fields)]
pub struct Oracle {
    pub kind: String,
    pub arguments: Vec<OracleArgument>,
}
crate::entry::decode::objects!(Oracle);

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OracleArgument {
    Type(String),
    Nat(Unsigned),
}
impl<'de> Deserialize<'de> for OracleArgument {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        struct Pair;
        impl<'de> Visitor<'de> for Pair {
            type Value = OracleArgument;
            fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str("a typed oracle argument pair")
            }
            fn visit_seq<A: SeqAccess<'de>>(self, mut a: A) -> Result<Self::Value, A::Error> {
                let sort: String = a
                    .next_element()?
                    .ok_or_else(|| A::Error::custom("missing sort"))?;
                let value = match sort.as_str() {
                    "type" => OracleArgument::Type(
                        a.next_element()?
                            .ok_or_else(|| A::Error::custom("missing type"))?,
                    ),
                    "nat" => OracleArgument::Nat(
                        a.next_element()?
                            .ok_or_else(|| A::Error::custom("missing natural"))?,
                    ),
                    _ => return Err(A::Error::custom("unknown oracle argument sort")),
                };
                if a.next_element::<String>()?.is_some() {
                    return Err(A::Error::custom("extra oracle argument component"));
                }
                Ok(value)
            }
        }
        d.deserialize_seq(Pair)
    }
}
