//! Exact array records and bounded integer-token parsing, including JSON -0.
use crate::Error;
use num_bigint::BigUint;
use serde_json::Value;

pub fn parse(bytes: &[u8]) -> Result<Value, Error> {
    if bytes.len() > 1024 * 1024 {
        return Err(Error("byte-limit"));
    }
    let text = std::str::from_utf8(bytes).map_err(|_| Error("invalid-utf8"))?;
    let mut normalized = String::with_capacity(text.len());
    let mut chars = text.char_indices().peekable();
    let mut depth = 0usize;
    while let Some((_, ch)) = chars.next() {
        match ch {
            '"' => {
                normalized.push(ch);
                let mut closed = false;
                while let Some((_, c)) = chars.next() {
                    normalized.push(c);
                    if c == '\\' {
                        let (_, e) = chars.next().ok_or(Error("invalid-json"))?;
                        normalized.push(e);
                    } else if c == '"' {
                        closed = true;
                        break;
                    }
                }
                if !closed {
                    return Err(Error("invalid-json"));
                }
            }
            '{' | '}' => return Err(Error("invalid-shape")),
            '-' | '0'..='9' => {
                let negative = ch == '-';
                let mut digits = String::new();
                if !negative {
                    digits.push(ch);
                }
                while let Some(&(_, c)) = chars.peek() {
                    if !c.is_ascii_digit() {
                        break;
                    }
                    chars.next();
                    digits.push(c);
                }
                if digits.is_empty() || (digits.len() > 1 && digits.starts_with('0')) {
                    return Err(Error("invalid-json"));
                }
                if digits.len() > 1024 {
                    return Err(Error("number-limit"));
                }
                if chars
                    .peek()
                    .is_some_and(|&(_, c)| matches!(c, '.' | 'e' | 'E'))
                    || (negative && digits != "0")
                {
                    return Err(Error("expected-natural"));
                }
                normalized.push_str(&digits);
                normalized.push(' ');
            }
            '[' => {
                depth += 1;
                if depth > 512 {
                    return Err(Error("depth-limit"));
                }
                normalized.push(ch);
            }
            ']' => {
                depth = depth.checked_sub(1).ok_or(Error("invalid-json"))?;
                normalized.push(ch);
            }
            _ => normalized.push(ch),
        }
    }
    let mut de = serde_json::Deserializer::from_str(&normalized);
    de.disable_recursion_limit();
    // Value::deserialize requires serde directly; streaming into Value also
    // verifies end-of-input without exposing a permissive trailing suffix.
    let mut stream = de.into_iter::<Value>();
    let value = stream
        .next()
        .ok_or(Error("invalid-json"))?
        .map_err(|_| Error("invalid-json"))?;
    if stream.next().is_some() {
        return Err(Error("invalid-json"));
    }
    Ok(value)
}
pub fn array(value: &Value, size: usize) -> Result<&[Value], Error> {
    let a = value.as_array().ok_or(Error("invalid-shape"))?;
    if a.len() != size {
        return Err(Error("invalid-shape"));
    }
    Ok(a)
}
pub fn list(value: &Value) -> Result<&[Value], Error> {
    value
        .as_array()
        .map(Vec::as_slice)
        .ok_or(Error("invalid-shape"))
}
pub fn string(value: &Value) -> Result<&str, Error> {
    value.as_str().ok_or(Error("expected-string"))
}
pub fn natural(value: &Value) -> Result<BigUint, Error> {
    if !value.is_number() {
        return Err(Error("expected-natural"));
    }
    value
        .to_string()
        .parse()
        .map_err(|_| Error("expected-natural"))
}
pub fn number(value: &BigUint) -> Value {
    Value::Number(
        value
            .to_string()
            .parse()
            .expect("BigUint decimal is a JSON number"),
    )
}
