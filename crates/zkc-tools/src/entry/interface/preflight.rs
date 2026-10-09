//! Bound recursive metadata before serde allocates its typed records. This is
//! a lexical resource and natural-number check; serde owns JSON syntax/UTF-8.
use super::{InterfaceError, Result};

pub(super) fn check(bytes: &[u8]) -> Result<()> {
    if bytes.len() > super::super::package::INTERFACE_BYTES {
        return Err(InterfaceError::Limit);
    }
    let (mut depth, mut nodes, mut length) = (0usize, 0usize, 0usize);
    let (mut quoted, mut escaped, mut scalar) = (false, false, false);
    let (mut numeric, mut leading_zero, mut invalid_number) = (false, false, false);
    for &b in bytes {
        if quoted {
            if !escaped && b == b'"' {
                quoted = false;
                continue;
            }
            length += 1;
            // A Unicode escape uses at most six bytes per decoded byte.
            if length > 6 * 256 * 1024 {
                return Err(InterfaceError::Limit);
            }
            if escaped {
                escaped = false;
            } else if b == b'\\' {
                escaped = true;
            }
            continue;
        }
        match b {
            b'[' | b'{' | b'"' => {
                scalar = false;
                nodes += 1;
                if b == b'"' {
                    quoted = true;
                    length = 0;
                } else {
                    depth += 1;
                }
            }
            b']' | b'}' => {
                scalar = false;
                depth = depth.checked_sub(1).ok_or(InterfaceError::Format)?;
            }
            b',' | b':' | b' ' | b'\t' | b'\n' | b'\r' => scalar = false,
            _ => {
                if !scalar {
                    nodes += 1;
                    length = 0;
                    scalar = true;
                    numeric = b.is_ascii_digit() || matches!(b, b'-' | b'+');
                    leading_zero = b == b'0';
                }
                length += 1;
                if length > 10 {
                    return Err(InterfaceError::Limit);
                }
                // Tagged-enum buffering can normalize -0 before typed decoding.
                // Check the original token, retaining resource-limit precedence.
                if numeric && (!b.is_ascii_digit() || leading_zero && length > 1) {
                    invalid_number = true;
                }
            }
        }
        if depth > 256 || nodes > 200_000 {
            return Err(InterfaceError::Limit);
        }
    }
    if quoted || depth != 0 || invalid_number {
        return Err(InterfaceError::Format);
    }
    Ok(())
}
