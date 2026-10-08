//! Bound recursive metadata before serde allocates its typed records. This is
//! a lexical resource check; serde remains responsible for JSON syntax/UTF-8.
use super::{InterfaceError, Result};

pub(super) fn check(bytes: &[u8]) -> Result<()> {
    if bytes.len() > super::super::package::INTERFACE_BYTES {
        return Err(InterfaceError::Limit);
    }
    let (mut depth, mut nodes, mut length) = (0usize, 0usize, 0usize);
    let (mut quoted, mut escaped, mut scalar) = (false, false, false);
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
                }
                length += 1;
                if length > 10 {
                    return Err(InterfaceError::Limit);
                }
            }
        }
        if depth > 256 || nodes > 200_000 {
            return Err(InterfaceError::Limit);
        }
    }
    if quoted || depth != 0 {
        return Err(InterfaceError::Format);
    }
    Ok(())
}
