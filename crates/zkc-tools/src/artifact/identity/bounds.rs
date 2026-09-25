//! Charge output nodes and bytes before copying subtrees or allocating arrays.
use super::{Json, Result};
use zkc_runtime::logical::TreeLimits as L;

#[derive(Default)]
pub(super) struct Builder {
    nodes: usize,
    bytes: usize,
}
impl Builder {
    fn charge(&mut self, depth: usize, bytes: usize) -> Result<()> {
        self.nodes = self.nodes.checked_add(1).ok_or("identity-tree-limit")?;
        self.bytes = self.bytes.checked_add(bytes).ok_or("identity-tree-limit")?;
        if depth > L::DEPTH || self.nodes > L::NODES || self.bytes > L::BYTES {
            return Err("identity-tree-limit".into());
        }
        Ok(())
    }
    pub fn array(&mut self, n: usize, depth: usize) -> Result<Vec<Json>> {
        self.charge(depth, 9)?;
        if n > L::ARRAY_LENGTH || n > L::NODES - self.nodes {
            return Err("identity-tree-limit".into());
        }
        let mut out = Vec::new();
        out.try_reserve_exact(n)
            .map_err(|_| "identity-allocation")?;
        Ok(out)
    }
    pub fn string(&mut self, s: &str, depth: usize) -> Result<Json> {
        if s.len() > L::STRING_BYTES {
            return Err("identity-tree-limit".into());
        }
        self.charge(depth, 9 + s.len())?;
        Ok(Json::String(s.to_owned()))
    }
    /// No allocation, and at most DEPTH+1 stack frames, even for caller-built trees.
    pub fn measure(&mut self, v: &Json, depth: usize, string_limit: usize) -> Result<()> {
        match v {
            Json::String(s) => {
                if s.len() > string_limit {
                    return Err("identity-string-limit".into());
                }
                self.charge(depth, 9 + s.len())
            }
            Json::Array(a) => {
                self.charge(depth, 9)?;
                if a.len() > L::ARRAY_LENGTH || a.len() > L::NODES - self.nodes {
                    return Err("identity-tree-limit".into());
                }
                for v in a {
                    self.measure(v, depth + 1, string_limit)?;
                }
                Ok(())
            }
            _ => Err("identity-tree-kind".into()),
        }
    }
    pub fn copy(&mut self, v: &Json, depth: usize) -> Result<Json> {
        self.measure(v, depth, L::STRING_BYTES)?;
        Ok(v.clone())
    }
    pub fn record(&mut self, r: &[Json], depth: usize) -> Result<Json> {
        let mut out = self.array(r.len(), depth)?;
        for v in r {
            out.push(self.copy(v, depth + 1)?);
        }
        Ok(Json::Array(out))
    }
}

pub(super) fn source_tree(value: &Json) -> Result<()> {
    Builder::default().measure(value, 0, 4096)
}

/// Count JSON before allocating its byte vector, including escaping expansion.
pub(super) fn serialize(value: &Json, limit: usize) -> Result<Vec<u8>> {
    struct Count {
        bytes: usize,
        limit: usize,
    }
    impl std::io::Write for Count {
        fn write(&mut self, b: &[u8]) -> std::io::Result<usize> {
            self.bytes = self
                .bytes
                .checked_add(b.len())
                .filter(|n| *n <= self.limit)
                .ok_or_else(|| std::io::Error::other("identity-byte-limit"))?;
            Ok(b.len())
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }
    // Bounds apply before serde's recursive traversal too.
    Builder::default().measure(value, 0, L::STRING_BYTES)?;
    let mut count = Count { bytes: 0, limit };
    serde_json::to_writer(&mut count, value).map_err(|_| "identity-byte-limit")?;
    let mut bytes = Vec::new();
    bytes
        .try_reserve_exact(count.bytes)
        .map_err(|_| "identity-allocation")?;
    serde_json::to_writer(&mut bytes, value).map_err(|_| "identity-json")?;
    Ok(bytes)
}
