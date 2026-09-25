//! Bounded sectioned binary container used by the pinned snarkjs formats.
use super::{Error, Limits, Result};
use std::{fs::File, io::Read, path::Path};
pub(super) fn read(path: &Path, limits: &Limits) -> Result<Vec<u8>> {
    let mut f = File::open(path).map_err(|_| Error("import-io"))?;
    let len = usize::try_from(f.metadata().map_err(|_| Error("import-io"))?.len())
        .map_err(|_| Error("import-file-limit"))?;
    if len > limits.file_bytes() {
        return Err(Error("import-file-limit"));
    }
    let mut out = reserve(len)?;
    out.resize(len, 0);
    f.read_exact(&mut out).map_err(|_| Error("import-io"))?;
    let mut tail = [0];
    if f.read(&mut tail).map_err(|_| Error("import-io"))? != 0 {
        return Err(Error("import-file-changed"));
    }
    Ok(out)
}
pub(super) fn reserve<T>(n: usize) -> Result<Vec<T>> {
    let mut v = Vec::new();
    v.try_reserve_exact(n)
        .map_err(|_| Error("import-allocation"))?;
    Ok(v)
}
pub(super) struct Cursor<'a>(pub &'a [u8]);
impl<'a> Cursor<'a> {
    pub fn take(&mut self, n: usize) -> Result<&'a [u8]> {
        let (a, b) = self
            .0
            .split_at_checked(n)
            .ok_or(Error("import-truncated"))?;
        self.0 = b;
        Ok(a)
    }
    pub fn u32(&mut self) -> Result<u32> {
        Ok(u32::from_le_bytes(self.take(4)?.try_into().unwrap()))
    }
    pub fn finish(self) -> Result<()> {
        if self.0.is_empty() {
            Ok(())
        } else {
            Err(Error("import-trailing-bytes"))
        }
    }
}
pub(super) fn sections<'a>(
    bytes: &'a [u8],
    magic: &[u8; 4],
    version: u32,
    max_section: u32,
    limits: &Limits,
) -> Result<Vec<Option<&'a [u8]>>> {
    if bytes.len() > limits.file_bytes() {
        return Err(Error("import-file-limit"));
    }
    let mut r = Cursor(bytes);
    if r.take(4)? != magic {
        return Err(Error("import-magic"));
    }
    if r.u32()? != version {
        return Err(Error("import-version"));
    }
    let count = r.u32()?;
    if count == 0 || count > max_section {
        return Err(Error("import-section-count"));
    }
    let mut sections = vec![None; max_section as usize + 1];
    for _ in 0..count {
        let id = r.u32()?;
        if id == 0 || id > max_section {
            return Err(Error("import-section-id"));
        }
        let slot = &mut sections[id as usize];
        if slot.is_some() {
            return Err(Error("import-duplicate-section"));
        }
        let len = usize::try_from(u64::from_le_bytes(r.take(8)?.try_into().unwrap()))
            .map_err(|_| Error("import-section-length"))?;
        *slot = Some(r.take(len)?);
    }
    r.finish()?;
    Ok(sections)
}
pub(super) fn section<'a>(sections: &[Option<&'a [u8]>], id: usize) -> Result<&'a [u8]> {
    sections[id].ok_or(Error("import-missing-section"))
}
pub(super) fn exact_count(bytes: &[u8], n: usize, width: usize) -> Result<()> {
    if n.checked_mul(width) != Some(bytes.len()) {
        Err(Error("import-section-length"))
    } else {
        Ok(())
    }
}
