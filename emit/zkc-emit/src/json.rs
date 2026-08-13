//! A minimal JSON reader/writer for the canonical-document grammar.
//!
//! The canonical OIR document (docs/spec/carrier.md §6) uses objects,
//! arrays, strings, and non-negative integers, serialized compactly with
//! keys in a fixed order. This module parses that grammar, preserves key
//! order, and re-serializes byte-identically — the round trip is asserted
//! before any derived view (the semantic-id erasure) is computed, so the
//! writer cannot silently disagree with the canonical form. Binding files
//! reuse the same reader; they may carry whitespace.

use std::fmt::Write as _;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Json {
    Object(Vec<(String, Json)>),
    Array(Vec<Json>),
    String(String),
    UInt(u64),
}

impl Json {
    pub fn as_object(&self) -> Option<&[(String, Json)]> {
        match self {
            Json::Object(entries) => Some(entries),
            _ => None,
        }
    }
    pub fn as_array(&self) -> Option<&[Json]> {
        match self {
            Json::Array(items) => Some(items),
            _ => None,
        }
    }
    pub fn as_str(&self) -> Option<&str> {
        match self {
            Json::String(text) => Some(text),
            _ => None,
        }
    }
    /// Object field lookup by key.
    pub fn get(&self, key: &str) -> Option<&Json> {
        self.as_object()?
            .iter()
            .find(|(name, _)| name == key)
            .map(|(_, value)| value)
    }
}

pub fn parse(bytes: &[u8]) -> Result<Json, String> {
    let mut parser = Parser { bytes, position: 0 };
    parser.skip_whitespace();
    let value = parser.value()?;
    parser.skip_whitespace();
    if parser.position != parser.bytes.len() {
        return Err(format!("trailing bytes at offset {}", parser.position));
    }
    Ok(value)
}

struct Parser<'a> {
    bytes: &'a [u8],
    position: usize,
}

impl<'a> Parser<'a> {
    fn peek(&self) -> Option<u8> {
        self.bytes.get(self.position).copied()
    }

    fn bump(&mut self) -> Result<u8, String> {
        let byte = self.peek().ok_or("unexpected end of input")?;
        self.position += 1;
        Ok(byte)
    }

    fn skip_whitespace(&mut self) {
        while matches!(self.peek(), Some(b' ' | b'\t' | b'\r' | b'\n')) {
            self.position += 1;
        }
    }

    fn expect(&mut self, byte: u8) -> Result<(), String> {
        let got = self.bump()?;
        if got != byte {
            return Err(format!(
                "expected '{}' at offset {}, found '{}'",
                byte as char,
                self.position - 1,
                got as char
            ));
        }
        Ok(())
    }

    fn value(&mut self) -> Result<Json, String> {
        match self.peek().ok_or("unexpected end of input")? {
            b'{' => self.object(),
            b'[' => self.array(),
            b'"' => Ok(Json::String(self.string()?)),
            b'0'..=b'9' => self.number(),
            other => Err(format!(
                "unsupported JSON at offset {}: '{}' (the canonical grammar has objects, arrays, strings, and non-negative integers)",
                self.position, other as char
            )),
        }
    }

    fn object(&mut self) -> Result<Json, String> {
        self.expect(b'{')?;
        let mut entries = Vec::new();
        self.skip_whitespace();
        if self.peek() == Some(b'}') {
            self.position += 1;
            return Ok(Json::Object(entries));
        }
        loop {
            self.skip_whitespace();
            let key = self.string()?;
            if entries.iter().any(|(existing, _)| *existing == key) {
                return Err(format!("duplicate key '{key}'"));
            }
            self.skip_whitespace();
            self.expect(b':')?;
            self.skip_whitespace();
            let value = self.value()?;
            entries.push((key, value));
            self.skip_whitespace();
            match self.bump()? {
                b',' => continue,
                b'}' => return Ok(Json::Object(entries)),
                other => return Err(format!("expected ',' or '}}', found '{}'", other as char)),
            }
        }
    }

    fn array(&mut self) -> Result<Json, String> {
        self.expect(b'[')?;
        let mut items = Vec::new();
        self.skip_whitespace();
        if self.peek() == Some(b']') {
            self.position += 1;
            return Ok(Json::Array(items));
        }
        loop {
            self.skip_whitespace();
            items.push(self.value()?);
            self.skip_whitespace();
            match self.bump()? {
                b',' => continue,
                b']' => return Ok(Json::Array(items)),
                other => return Err(format!("expected ',' or ']', found '{}'", other as char)),
            }
        }
    }

    fn string(&mut self) -> Result<String, String> {
        self.expect(b'"')?;
        let mut text = String::new();
        loop {
            match self.bump()? {
                b'"' => return Ok(text),
                b'\\' => match self.bump()? {
                    b'"' => text.push('"'),
                    b'\\' => text.push('\\'),
                    b'/' => text.push('/'),
                    b'n' => text.push('\n'),
                    b't' => text.push('\t'),
                    b'r' => text.push('\r'),
                    other => {
                        return Err(format!(
                            "unsupported escape '\\{}' (the canonical writer emits none of these)",
                            other as char
                        ))
                    }
                },
                byte if byte < 0x20 => return Err("control byte inside string".into()),
                byte => text.push(byte as char),
            }
        }
    }

    fn number(&mut self) -> Result<Json, String> {
        let start = self.position;
        while matches!(self.peek(), Some(b'0'..=b'9')) {
            self.position += 1;
        }
        let text = std::str::from_utf8(&self.bytes[start..self.position]).unwrap();
        if text.len() > 1 && text.starts_with('0') {
            return Err(format!("non-canonical integer '{text}'"));
        }
        text.parse::<u64>()
            .map(Json::UInt)
            .map_err(|_| format!("integer '{text}' out of range"))
    }
}

/// Compact serialization, matching the canonical writer: no whitespace,
/// keys in stored order, plain decimal integers.
pub fn serialize(value: &Json) -> String {
    let mut out = String::new();
    write_value(value, &mut out);
    out
}

fn write_value(value: &Json, out: &mut String) {
    match value {
        Json::Object(entries) => {
            out.push('{');
            for (index, (key, entry)) in entries.iter().enumerate() {
                if index > 0 {
                    out.push(',');
                }
                write_string(key, out);
                out.push(':');
                write_value(entry, out);
            }
            out.push('}');
        }
        Json::Array(items) => {
            out.push('[');
            for (index, item) in items.iter().enumerate() {
                if index > 0 {
                    out.push(',');
                }
                write_value(item, out);
            }
            out.push(']');
        }
        Json::String(text) => write_string(text, out),
        Json::UInt(number) => {
            let _ = write!(out, "{number}");
        }
    }
}

fn write_string(text: &str, out: &mut String) {
    out.push('"');
    for character in text.chars() {
        match character {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            other => out.push(other),
        }
    }
    out.push('"');
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_trip_compact() {
        let bytes = br#"{"a":["x",["r",0,1]],"b":"y"}"#;
        let parsed = parse(bytes).unwrap();
        assert_eq!(serialize(&parsed).as_bytes(), bytes);
    }

    #[test]
    fn whitespace_tolerated_on_read() {
        let parsed = parse(b"{ \"a\" : [ 1 , 2 ] }").unwrap();
        assert_eq!(serialize(&parsed), r#"{"a":[1,2]}"#);
    }

    #[test]
    fn duplicate_keys_refuse() {
        assert!(parse(br#"{"a":1,"a":2}"#).is_err());
    }
}
