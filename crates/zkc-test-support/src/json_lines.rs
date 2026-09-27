//! Bounded JSON-lines transport for cross-reader probes, without semantic rules.
use serde_json::{Map, Value, json};
use std::io::{self, BufRead, Write};
const LINE_LIMIT: usize = 16384;

fn envelope(line: &[u8]) -> Option<usize> {
    let (mut quoted, mut escaped, mut depth, mut fields) = (false, false, 0_u32, 0);
    for &c in line {
        if !c.is_ascii() || (c < 32 && c != b'\t' && c != b'\r') {
            return None;
        }
        if quoted {
            if escaped {
                escaped = false;
            } else if c == b'\\' {
                escaped = true;
            } else if c == b'"' {
                quoted = false;
            }
        } else {
            match c {
                b'"' => quoted = true,
                b'{' | b'[' => {
                    depth += 1;
                    if depth > 8 {
                        return None;
                    }
                }
                b'}' | b']' => depth = depth.checked_sub(1)?,
                b':' => fields += 1,
                _ => {}
            }
        }
    }
    (!quoted && depth == 0).then_some(fields)
}

pub fn request(line: &[u8]) -> Option<Map<String, Value>> {
    let fields = envelope(line)?;
    let Value::Object(request) = serde_json::from_slice(line).ok()? else {
        return None;
    };
    (request.len() == fields).then_some(request)
}

fn emit(
    output: &mut impl Write,
    line: &[u8],
    oversized: bool,
    respond: &impl Fn(&[u8]) -> Option<Value>,
) -> io::Result<()> {
    let value =
        if oversized { None } else { respond(line) }.unwrap_or_else(|| json!({"accepted": false}));
    writeln!(output, "{value}")?;
    output.flush()
}

pub fn run(respond: impl Fn(&[u8]) -> Option<Value>) -> io::Result<()> {
    let mut input = io::stdin().lock();
    let mut output = io::stdout().lock();
    let mut line = Vec::new();
    let mut oversized = false;
    loop {
        let buffer = input.fill_buf()?;
        if buffer.is_empty() {
            break;
        }
        let consumed = buffer.len();
        for &byte in buffer {
            if byte == b'\n' {
                emit(&mut output, &line, oversized, &respond)?;
                line.clear();
                oversized = false;
            } else if line.len() < LINE_LIMIT {
                line.push(byte);
            } else {
                oversized = true;
            }
        }
        input.consume(consumed);
    }
    if !line.is_empty() || oversized {
        emit(&mut output, &line, oversized, &respond)?;
    }
    Ok(())
}
