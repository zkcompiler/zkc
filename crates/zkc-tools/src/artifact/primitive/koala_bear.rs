//! Independent canonical-value validation for the Lean source interpreter.
//! Lean owns numerical arithmetic; this service installs no numerical callback.
use super::{Result, codec};
use serde_json::Value as Json;

pub(super) fn validate(ty: &str, wire: &str, attrs: &Json) -> Result<Vec<Json>> {
    if !codec::array(attrs)?.is_empty() {
        return Err("primitive-attributes");
    }
    let bytes = codec::unhex(wire)?;
    let body = match ty {
        "field:koala-bear" => {
            let body = codec::payload(&bytes, 19)?;
            if body.len() != 4 {
                return Err("primitive-field");
            }
            body
        }
        "vector:koala-bear" => codec::counted(&bytes, 20, 4, 1 << 16)?,
        "polynomial:koala-bear" => codec::counted(&bytes, 21, 4, 1 << 16)?,
        "round:koala-bear" => {
            let body = codec::payload(&bytes, 22)?;
            if body.len() != 12 {
                return Err("primitive-round");
            }
            body
        }
        _ => return Err("primitive-nominal-type"),
    };
    for coefficient in body.as_chunks::<4>().0 {
        if u32::from_le_bytes(*coefficient) >= 2_130_706_433 {
            return Err("primitive-field");
        }
    }
    if ty == "polynomial:koala-bear" && body.ends_with(&[0; 4]) {
        return Err("primitive-polynomial");
    }
    Ok(vec![])
}
