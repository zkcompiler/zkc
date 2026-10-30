//! Borrowed views of the canonical arrays-and-strings grammar.
use super::{CodecError, Result, TreeLimits};
use serde_json::Value;
use std::io::{self, Write};

/// A logical tree without an owned JSON or hexadecimal intermediate.
/// Hex denotes a lowercase ASCII string, not a new wire tag.
#[derive(Clone, Copy, Debug)]
pub enum Tree<'a> {
    Text(&'a str),
    Hex(&'a [u8]),
    Array(&'a [Tree<'a>]),
    Json(&'a Value),
}

/// Fully checked encoding borrowing immutable source data. Preparation checks
/// the complete grammar and all limits before a sink receives any bytes.
#[derive(Debug)]
pub struct Encoding<'a> {
    tree: Tree<'a>,
    size: usize,
}

impl<'a> Tree<'a> {
    pub fn prepare(self) -> Result<Encoding<'a>> {
        Ok(Encoding {
            size: self.measure(0, &mut 0)?,
            tree: self,
        })
    }

    fn measure(self, depth: usize, nodes: &mut usize) -> Result<usize> {
        // JSON is a view of the same node, not another level of nesting.
        if let Self::Json(value) = self {
            return match value {
                Value::String(s) => Self::Text(s).measure(depth, nodes),
                Value::Array(a) => measure_array(a.iter().map(Self::Json), depth, nodes),
                _ => {
                    count_node(depth, nodes)?;
                    Err(CodecError("tree-kind"))
                }
            };
        }
        if let Self::Array(a) = self {
            return measure_array(a.iter().copied(), depth, nodes);
        }
        count_node(depth, nodes)?;
        let length = match self {
            Self::Text(s) => s.len(),
            Self::Hex(bytes) => bytes.len().checked_mul(2).ok_or(CodecError("tree-limit"))?,
            _ => unreachable!(),
        };
        if length > TreeLimits::STRING_BYTES {
            return Err(CodecError("tree-limit"));
        }
        bounded_add(9, length)
    }

    fn write(self, out: &mut impl Write) -> io::Result<()> {
        match self {
            Self::Text(s) => {
                header(out, 0, s.len())?;
                out.write_all(s.as_bytes())
            }
            Self::Hex(bytes) => {
                header(out, 0, bytes.len() * 2)?;
                let mut buffer = [0; 1024];
                const DIGITS: &[u8; 16] = b"0123456789abcdef";
                for chunk in bytes.chunks(buffer.len() / 2) {
                    for (byte, pair) in chunk.iter().zip(buffer.as_chunks_mut::<2>().0) {
                        pair[0] = DIGITS[(byte >> 4) as usize];
                        pair[1] = DIGITS[(byte & 15) as usize];
                    }
                    out.write_all(&buffer[..chunk.len() * 2])?;
                }
                Ok(())
            }
            Self::Array(a) => write_array(a.iter().copied(), out),
            Self::Json(Value::String(s)) => Self::Text(s).write(out),
            Self::Json(Value::Array(a)) => write_array(a.iter().map(Self::Json), out),
            Self::Json(_) => unreachable!("encoding preflight"),
        }
    }
}

fn count_node(depth: usize, nodes: &mut usize) -> Result<()> {
    if depth > TreeLimits::DEPTH || *nodes == TreeLimits::NODES {
        return Err(CodecError("tree-limit"));
    }
    *nodes += 1;
    Ok(())
}
fn bounded_add(a: usize, b: usize) -> Result<usize> {
    a.checked_add(b)
        .filter(|n| *n <= TreeLimits::BYTES)
        .ok_or(CodecError("tree-limit"))
}
fn measure_array<'a>(
    a: impl ExactSizeIterator<Item = Tree<'a>>,
    depth: usize,
    nodes: &mut usize,
) -> Result<usize> {
    count_node(depth, nodes)?;
    if a.len() > TreeLimits::ARRAY_LENGTH {
        return Err(CodecError("tree-limit"));
    }
    let mut size = 9;
    for child in a {
        size = bounded_add(size, child.measure(depth + 1, nodes)?)?;
    }
    Ok(size)
}
fn header(out: &mut impl Write, tag: u8, length: usize) -> io::Result<()> {
    let mut bytes = [tag; 9];
    bytes[1..].copy_from_slice(&(length as u64).to_le_bytes());
    out.write_all(&bytes)
}
fn write_array<'a>(
    a: impl ExactSizeIterator<Item = Tree<'a>>,
    out: &mut impl Write,
) -> io::Result<()> {
    header(out, 1, a.len())?;
    for child in a {
        child.write(out)?;
    }
    Ok(())
}
impl Encoding<'_> {
    pub fn size(&self) -> usize {
        self.size
    }
    /// Sink failures are propagated and may leave a prefix in the sink. The
    /// caller owns publication/rollback; this method never flushes the sink.
    pub fn write(&self, out: &mut impl Write) -> io::Result<()> {
        self.tree.write(out)
    }
    pub fn to_vec(&self) -> Result<Vec<u8>> {
        let mut bytes = Vec::new();
        bytes
            .try_reserve_exact(self.size)
            .map_err(|_| CodecError("tree-allocation"))?;
        self.write(&mut bytes).expect("reserved vector writer");
        Ok(bytes)
    }
}
