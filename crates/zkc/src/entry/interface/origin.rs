//! Closed typed static trees from the public protocol origin grammar.
//! Match Contracts/SourceTerms, not display types or local binding spellings.
use serde::{
    Deserialize, Deserializer,
    de::{DeserializeSeed, Error, SeqAccess, Visitor},
};
use std::fmt;

#[derive(Debug, PartialEq, Eq)]
pub(in crate::entry) enum OriginTerm {
    Natural(String),
    Field(String),
    Group(String),
    Domain(String, String),
    Asset(String, String),
    Boolean,
    Index,
    Unit,
    Tuple(Vec<Self>),
    Array(Box<Self>, String),
    DescriptorProduct(Vec<Self>),
    DescriptorSequence(Box<Self>, Option<String>),
    Nominal(NominalKind, String, Vec<Self>),
    Builtin(String, Vec<Self>),
    Formal(String, Vec<Self>),
}

#[derive(Debug, PartialEq, Eq)]
pub(in crate::entry) enum NominalKind {
    Record,
    LogicalRecord,
    Variant,
    Associated,
    Module,
}

fn item<'de, A: SeqAccess<'de>, T: Deserialize<'de>>(seq: &mut A) -> Result<T, A::Error> {
    seq.next_element()?
        .ok_or_else(|| A::Error::custom("missing static term member"))
}
fn text<'de, A: SeqAccess<'de>>(seq: &mut A) -> Result<String, A::Error> {
    let value: String = item(seq)?;
    if value.is_empty() || value.len() > 512 || value.contains('\0') {
        return Err(A::Error::custom("invalid static term text"));
    }
    Ok(value)
}
fn decimal<'de, A: SeqAccess<'de>>(seq: &mut A) -> Result<String, A::Error> {
    let value = text(seq)?;
    if !value.bytes().all(|b| b.is_ascii_digit()) || value.len() > 1 && value.starts_with('0') {
        return Err(A::Error::custom("noncanonical static natural"));
    }
    Ok(value)
}
fn path(value: &str) -> bool {
    crate::source_names::is_source_nfc(value)
        && value.split("::").all(|part| {
            !part.is_empty()
                && !part.as_bytes()[0].is_ascii_digit()
                && part
                    .bytes()
                    .all(|b| b >= 128 || b.is_ascii_alphanumeric() || b == b'_')
        })
}

struct Excess;
impl<'de> Deserialize<'de> for Excess {
    fn deserialize<D: Deserializer<'de>>(_: D) -> Result<Self, D::Error> {
        Err(D::Error::custom("excess static term member"))
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Category {
    Term,
    Descriptor,
    Natural,
}

struct Term<'a> {
    remaining: &'a mut usize,
    depth: usize,
    category: Category,
}
impl<'de> DeserializeSeed<'de> for Term<'_> {
    type Value = OriginTerm;
    fn deserialize<D: Deserializer<'de>>(self, decoder: D) -> Result<Self::Value, D::Error> {
        if self.depth >= 64 || *self.remaining == 0 {
            return Err(D::Error::custom("static term depth or node limit"));
        }
        *self.remaining -= 1;
        decoder.deserialize_seq(self)
    }
}
impl<'de> Visitor<'de> for Term<'_> {
    type Value = OriginTerm;
    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("a closed typed static term array")
    }
    fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<Self::Value, A::Error> {
        use OriginTerm::*;
        let tag = text(&mut seq)?;
        if self.category == Category::Natural && tag != "nat"
            || self.category == Category::Descriptor
                && !matches!(
                    tag.as_str(),
                    "descriptor-product" | "descriptor-sequence" | "builtin"
                )
        {
            return Err(A::Error::custom("wrong static term category"));
        }
        let result = match tag.as_str() {
            "nat" => Natural(decimal(&mut seq)?),
            "field" => Field(text(&mut seq)?),
            "group" => Group(text(&mut seq)?),
            "domain" => Domain(text(&mut seq)?, text(&mut seq)?),
            "asset" => Asset(text(&mut seq)?, text(&mut seq)?),
            "bool" => Boolean,
            "index" => Index,
            "unit" => Unit,
            "tuple" => Tuple(children(
                &mut seq,
                self.remaining,
                self.depth,
                Category::Term,
                512,
            )?),
            "descriptor-product" => DescriptorProduct(children(
                &mut seq,
                self.remaining,
                self.depth,
                Category::Descriptor,
                512,
            )?),
            "descriptor-sequence" => {
                let child = seq
                    .next_element_seed(Term {
                        remaining: self.remaining,
                        depth: self.depth + 1,
                        category: Category::Descriptor,
                    })?
                    .ok_or_else(|| A::Error::custom("missing descriptor element"))?;
                let extent = seq
                    .next_element_seed(Extent {
                        remaining: self.remaining,
                        depth: self.depth + 1,
                    })?
                    .ok_or_else(|| A::Error::custom("missing descriptor extent"))?;
                DescriptorSequence(Box::new(child), extent)
            }
            "array" => {
                let child = seq
                    .next_element_seed(Term {
                        remaining: self.remaining,
                        depth: self.depth + 1,
                        category: Category::Term,
                    })?
                    .ok_or_else(|| A::Error::custom("missing array element"))?;
                Array(Box::new(child), decimal(&mut seq)?)
            }
            "nominal" => {
                let kind = match text(&mut seq)?.as_str() {
                    "record" => NominalKind::Record,
                    "logical_record" => NominalKind::LogicalRecord,
                    "variant" => NominalKind::Variant,
                    "associated" => NominalKind::Associated,
                    "module" => NominalKind::Module,
                    _ => return Err(A::Error::custom("unknown nominal kind")),
                };
                let name = text(&mut seq)?;
                if !path(&name) {
                    return Err(A::Error::custom("invalid nominal path"));
                }
                Nominal(
                    kind,
                    name,
                    children(&mut seq, self.remaining, self.depth, Category::Term, 512)?,
                )
            }
            "builtin" | "formal" => {
                let name = text(&mut seq)?;
                // Exact existing leaf syntax only. Formation and native authority
                // remain separate from recognizing a closed descriptor child.
                if self.category == Category::Descriptor && name != "finite" {
                    return Err(A::Error::custom("unknown descriptor leaf schema"));
                }
                let arguments = children(
                    &mut seq,
                    self.remaining,
                    self.depth,
                    Category::Term,
                    if self.category == Category::Descriptor {
                        1
                    } else {
                        512
                    },
                )?;
                if self.category == Category::Descriptor && arguments.len() != 1 {
                    return Err(A::Error::custom("invalid Finite leaf arity"));
                }
                if tag == "builtin" {
                    Builtin(name, arguments)
                } else {
                    Formal(name, arguments)
                }
            }
            _ => return Err(A::Error::custom("unknown static term tag")),
        };
        // Inspect an excess member without accepting an untyped JSON subtree.
        if seq.next_element::<Excess>()?.is_some() {
            return Err(A::Error::custom("extra static term member"));
        }
        Ok(result)
    }
}

struct Extent<'a> {
    remaining: &'a mut usize,
    depth: usize,
}
impl<'de> DeserializeSeed<'de> for Extent<'_> {
    type Value = Option<String>;
    fn deserialize<D: Deserializer<'de>>(self, decoder: D) -> Result<Self::Value, D::Error> {
        decoder.deserialize_option(self)
    }
}
impl<'de> Visitor<'de> for Extent<'_> {
    type Value = Option<String>;
    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("null or a closed Natural term")
    }
    fn visit_none<E: Error>(self) -> Result<Self::Value, E> {
        Ok(None)
    }
    fn visit_unit<E: Error>(self) -> Result<Self::Value, E> {
        Ok(None)
    }
    fn visit_some<D: Deserializer<'de>>(self, decoder: D) -> Result<Self::Value, D::Error> {
        let term = Term {
            remaining: self.remaining,
            depth: self.depth,
            category: Category::Natural,
        }
        .deserialize(decoder)?;
        let OriginTerm::Natural(value) = term else {
            return Err(D::Error::custom("invalid descriptor extent"));
        };
        Ok(Some(value))
    }
}

struct Terms<'a> {
    remaining: &'a mut usize,
    depth: usize,
    limit: usize,
    category: Category,
}
impl<'de> DeserializeSeed<'de> for Terms<'_> {
    type Value = Vec<OriginTerm>;
    fn deserialize<D: Deserializer<'de>>(self, decoder: D) -> Result<Self::Value, D::Error> {
        decoder.deserialize_seq(self)
    }
}
impl<'de> Visitor<'de> for Terms<'_> {
    type Value = Vec<OriginTerm>;
    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("an ordered bounded static term list")
    }
    fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<Self::Value, A::Error> {
        let mut result = Vec::new();
        loop {
            if result.len() == self.limit {
                if seq.next_element::<Excess>()?.is_some() {
                    return Err(A::Error::custom("static term list limit"));
                }
                return Ok(result);
            }
            let Some(term) = seq.next_element_seed(Term {
                remaining: self.remaining,
                depth: self.depth,
                category: self.category,
            })?
            else {
                return Ok(result);
            };
            result.push(term);
        }
    }
}
fn children<'de, A: SeqAccess<'de>>(
    seq: &mut A,
    remaining: &mut usize,
    depth: usize,
    category: Category,
    limit: usize,
) -> Result<Vec<OriginTerm>, A::Error> {
    seq.next_element_seed(Terms {
        remaining,
        depth: depth + 1,
        limit,
        category,
    })?
    .ok_or_else(|| A::Error::custom("missing static term children"))
}

pub(super) fn arguments<'de, D: Deserializer<'de>>(
    decoder: D,
) -> Result<Vec<OriginTerm>, D::Error> {
    Terms {
        remaining: &mut 4096,
        depth: 0,
        limit: 128,
        category: Category::Term,
    }
    .deserialize(decoder)
}
