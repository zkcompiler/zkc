//! Bounded JSON documents with duplicate-key rejection before typed conversion.
//! Array-only carriers use their narrower parser and contracts.
use serde::{
    Deserializer,
    de::{self, DeserializeSeed, MapAccess, SeqAccess, Visitor},
};
use serde_json::{Map, Value};
use std::fmt;

// A source schema has depth at most 32. Variants add two JSON containers,
// and request envelopes add four; this admits every supported logical shape.
pub(crate) const MAX_DEPTH: usize = 72;

pub(crate) struct Budget {
    bytes: usize,
    nodes: usize,
}
impl Budget {
    pub fn new(bytes: usize) -> Self {
        Self {
            bytes,
            nodes: 200_000,
        }
    }
    pub fn remaining_bytes(&self) -> usize {
        self.bytes
    }
    pub fn read(&mut self, bytes: &[u8]) -> Result<Value, String> {
        self.bytes = self
            .bytes
            .checked_sub(bytes.len())
            .ok_or("entry-request-limit")?;
        natural_numbers(bytes)?;
        let mut decoder = serde_json::Deserializer::from_slice(bytes);
        let mut limited = false;
        let value = Node {
            remaining: &mut self.nodes,
            limited: &mut limited,
            depth: 0,
        }
        .deserialize(&mut decoder)
        .map_err(|_| {
            if limited {
                "entry-request-limit"
            } else {
                "entry-request-format"
            }
        })?;
        decoder.end().map_err(|_| "entry-request-format")?;
        Ok(value)
    }
}
pub(crate) fn read(bytes: &[u8], limit: usize) -> Result<Value, String> {
    Budget::new(limit).read(bytes)
}
// Invocation numbers are u64 naturals. Check their lexical form before serde's
// arbitrary-precision extension can present a large number as a private map.
fn natural_numbers(bytes: &[u8]) -> Result<(), String> {
    let (mut i, mut quoted, mut escaped) = (0, false, false);
    while i < bytes.len() {
        let b = bytes[i];
        if quoted {
            if escaped {
                escaped = false;
            } else if b == b'\\' {
                escaped = true;
            } else if b == b'"' {
                quoted = false;
            }
        } else if b == b'"' {
            quoted = true;
        } else if b == b'-' || b.is_ascii_digit() {
            let start = i;
            while i < bytes.len()
                && !matches!(bytes[i], b',' | b']' | b'}' | b' ' | b'\n' | b'\r' | b'\t')
            {
                i += 1;
            }
            if !bytes[start..i].iter().all(u8::is_ascii_digit)
                || std::str::from_utf8(&bytes[start..i])
                    .ok()
                    .and_then(|s| s.parse::<u64>().ok())
                    .is_none()
            {
                return Err("entry-request-format".into());
            }
            continue;
        }
        i += 1;
    }
    Ok(())
}
struct Node<'a> {
    remaining: &'a mut usize,
    limited: &'a mut bool,
    depth: usize,
}
impl<'de> DeserializeSeed<'de> for Node<'_> {
    type Value = Value;
    fn deserialize<D: Deserializer<'de>>(self, decoder: D) -> Result<Value, D::Error> {
        if self.depth > MAX_DEPTH {
            *self.limited = true;
            return Err(de::Error::custom("document depth"));
        }
        *self.remaining = self.remaining.checked_sub(1).ok_or_else(|| {
            *self.limited = true;
            de::Error::custom("document nodes")
        })?;
        decoder.deserialize_any(self)
    }
}
impl<'de> Visitor<'de> for Node<'_> {
    type Value = Value;
    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("bounded JSON without duplicate keys")
    }
    fn visit_unit<E: de::Error>(self) -> Result<Value, E> {
        Ok(Value::Null)
    }
    fn visit_bool<E: de::Error>(self, v: bool) -> Result<Value, E> {
        Ok(Value::Bool(v))
    }
    fn visit_u64<E: de::Error>(self, v: u64) -> Result<Value, E> {
        Ok(Value::Number(v.into()))
    }
    fn visit_i64<E: de::Error>(self, v: i64) -> Result<Value, E> {
        Ok(Value::Number(v.into()))
    }
    fn visit_f64<E: de::Error>(self, _: f64) -> Result<Value, E> {
        Err(de::Error::custom("expected a bounded natural"))
    }
    fn visit_str<E: de::Error>(self, v: &str) -> Result<Value, E> {
        Ok(Value::String(v.into()))
    }
    fn visit_string<E: de::Error>(self, v: String) -> Result<Value, E> {
        Ok(Value::String(v))
    }
    fn visit_seq<A: SeqAccess<'de>>(self, mut sequence: A) -> Result<Value, A::Error> {
        let mut values = Vec::new();
        while let Some(value) = sequence.next_element_seed(Node {
            remaining: self.remaining,
            limited: self.limited,
            depth: self.depth + 1,
        })? {
            values.push(value);
        }
        Ok(Value::Array(values))
    }
    fn visit_map<A: MapAccess<'de>>(self, mut fields: A) -> Result<Value, A::Error> {
        let mut values = Map::new();
        while let Some(name) = fields.next_key::<String>()? {
            if values.contains_key(&name) {
                return Err(de::Error::custom("duplicate key"));
            }
            *self.remaining = self.remaining.checked_sub(1).ok_or_else(|| {
                *self.limited = true;
                de::Error::custom("document nodes")
            })?;
            let value = fields.next_value_seed(Node {
                remaining: self.remaining,
                limited: self.limited,
                depth: self.depth + 1,
            })?;
            values.insert(name, value);
        }
        Ok(Value::Object(values))
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn exact_bytes_and_duplicate_keys_at_every_depth() {
        let bytes = r#"{"P":{"input":[true,2,null,"é"]}}"#.as_bytes();
        assert!(read(bytes, bytes.len()).is_ok());
        assert_eq!(
            read(bytes, bytes.len() - 1).unwrap_err(),
            "entry-request-limit"
        );
        for s in [
            r#"{"x":1,"x":2}"#,
            r#"{"P":{"x":1,"\u0078":2}}"#,
            r#"[{"x":0,"x":0}]"#,
            r#"{}{}"#,
        ] {
            assert!(read(s.as_bytes(), 4096).is_err(), "{s}");
        }
    }
    #[test]
    fn structure_is_bounded_during_decoding() {
        let at = "[".repeat(MAX_DEPTH) + "0" + &"]".repeat(MAX_DEPTH);
        assert!(read(at.as_bytes(), 4096).is_ok());
        let over = format!("[{at}]");
        assert_eq!(
            read(over.as_bytes(), 4096).unwrap_err(),
            "entry-request-limit"
        );
        let wide = "[".to_owned() + &vec!["0"; 200_000].join(",") + "]";
        assert_eq!(
            read(wide.as_bytes(), wide.len()).unwrap_err(),
            "entry-request-limit"
        );
        for bytes in [b"[\"\xff\"]".as_slice(), b"1e999", b"NaN"] {
            assert!(read(bytes, 4096).is_err());
        }
    }
}
