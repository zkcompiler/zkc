//! Versioned source spelling and reversible source/native name encodings.
//!
//! Native contracts keep their ASCII grammars. These helpers implement the
//! independent Rust counterpart of Language/Names; they never normalize names.
//! Callers enforce their source-byte limits before identifier/NFC admission.
use unicode_normalization::is_nfc;

mod data {
    include!(concat!(env!("OUT_DIR"), "/source_unicode.rs"));
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SourceScalar {
    pub value: u32,
    pub bytes: usize,
}
pub fn decode_source_scalar(source: &[u8], offset: usize) -> Option<SourceScalar> {
    let bytes = match *source.get(offset)? {
        0..=0x7f => 1,
        0xc2..=0xdf => 2,
        0xe0..=0xef => 3,
        0xf0..=0xf4 => 4,
        _ => return None,
    };
    let end = offset.checked_add(bytes)?;
    let text = std::str::from_utf8(source.get(offset..end)?).ok()?;
    Some(SourceScalar {
        value: text.chars().next()? as u32,
        bytes,
    })
}
fn contains(ranges: &[(u32, u32)], value: u32) -> bool {
    let index = ranges.partition_point(|&(_, hi)| hi < value);
    ranges.get(index).is_some_and(|&(lo, _)| lo <= value)
}
pub fn source_identifier_start(value: u32) -> bool {
    contains(data::IDENTIFIER_START, value)
}
pub fn source_identifier_continue(value: u32) -> bool {
    contains(data::IDENTIFIER_CONTINUE, value)
}
pub fn is_source_identifier(name: &str) -> bool {
    let mut chars = name.chars();
    chars
        .next()
        .is_some_and(|c| source_identifier_start(c as u32))
        && chars.all(|c| source_identifier_continue(c as u32))
        && is_source_nfc(name)
}
pub fn is_source_nfc(text: &str) -> bool {
    is_nfc(text)
}
fn syntax_scalar(value: u32) -> bool {
    char::from_u32(value).is_some_and(|c| is_source_nfc(c.encode_utf8(&mut [0; 4])))
}
pub fn is_mathematical_symbol(value: u32) -> bool {
    contains(data::MATH_SYMBOL, value) && syntax_scalar(value)
}
pub fn matching_source_delimiter(opener: u32) -> Option<u32> {
    let index = data::BRACKETS
        .binary_search_by_key(&opener, |&(lo, _)| lo)
        .ok()?;
    let closer = data::BRACKETS[index].1;
    (syntax_scalar(opener) && syntax_scalar(closer)).then_some(closer)
}
pub fn is_source_delimiter_closer(value: u32) -> bool {
    data::BRACKETS.iter().any(|&(opener, closer)| {
        closer == value && matching_source_delimiter(opener) == Some(value)
    })
}
pub fn source_name_profile_identity() -> &'static str {
    data::IDENTITY
}
pub fn native_role_name(index: u32) -> String {
    format!("role{index:08x}")
}
pub fn native_setup_name(index: u32) -> String {
    format!("setup{index:08x}")
}
pub fn native_alternative_name(index: u32) -> String {
    format!("case{index:08x}")
}
pub fn encode_nominal_identity(name: &str) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    name.bytes()
        .flat_map(|byte| {
            [
                HEX[usize::from(byte >> 4)] as char,
                HEX[usize::from(byte & 15)] as char,
            ]
        })
        .collect()
}
pub fn decode_nominal_identity(encoded: &str, max_bytes: u64) -> Option<String> {
    if !encoded.len().is_multiple_of(2) || encoded.len() as u64 / 2 > max_bytes {
        return None;
    }
    fn digit(b: u8) -> Option<u8> {
        match b {
            b'0'..=b'9' => Some(b - b'0'),
            b'a'..=b'f' => Some(b - b'a' + 10),
            _ => None,
        }
    }
    let decoded: Option<Vec<_>> = encoded
        .as_bytes()
        .as_chunks::<2>()
        .0
        .iter()
        .map(|pair| Some(digit(pair[0])? * 16 + digit(pair[1])?))
        .collect();
    String::from_utf8(decoded?).ok()
}
pub fn encode_source_symbol(qualified_name: &str, max_bytes: u64) -> Option<String> {
    // Calculate the complete expansion before allocating; lengths count UTF-8 bytes.
    let mut size = 1u64;
    for part in qualified_name.split("::") {
        let bytes = part.len() as u64;
        size = size
            .checked_add(u64::from(bytes.checked_ilog10().unwrap_or(0)) + 2)?
            .checked_add(bytes.checked_mul(2)?)?;
        if size > max_bytes || !is_source_identifier(part) {
            return None;
        }
    }
    let mut encoded = String::with_capacity(usize::try_from(size).ok()?);
    encoded.push('s');
    for part in qualified_name.split("::") {
        use std::fmt::Write;
        write!(encoded, "{}h{}", part.len(), encode_nominal_identity(part)).ok()?;
    }
    Some(encoded)
}

#[cfg(test)]
mod tests;
