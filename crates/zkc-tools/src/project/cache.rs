//! Optional local reuse of complete compilation outputs under captured inputs.
//! No witness, provider, session or mutable IR is retained here.
use super::{CompilationRequest, CompilationResult, Compiler, Error, Project};
use crate::{entry::Package, host::io};
use sha2::{Digest, Sha256};
use std::{
    fs::{self, File, OpenOptions},
    io::Write,
    path::{Path, PathBuf},
};

/// Trusted local store. Readers still authenticate containers and Hosts still
/// perform their normal admission. This is not a deployment trust root.
pub struct CompilationCache {
    directory: PathBuf,
    capacity: u64,
}
impl CompilationCache {
    pub fn new(directory: impl AsRef<Path>, capacity: u64) -> Result<Self, Error> {
        if capacity == 0 || capacity > 16 * 1024 * 1024 * 1024 {
            return Err("source-cache-capacity".into());
        }
        fs::create_dir_all(directory.as_ref()).map_err(|_| "source-cache-io")?;
        let directory = directory
            .as_ref()
            .canonicalize()
            .map_err(|_| "source-cache-io")?;
        Ok(Self {
            directory,
            capacity,
        })
    }
    fn lock(&self, name: &str) -> Result<File, Error> {
        OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(self.directory.join(name))
            .map_err(|_| "source-cache-io".into())
    }
    /// Serializes only store accounting, never compilation or benchmark execution.
    pub fn clear(&self) -> Result<u64, Error> {
        let lock = self.lock("store.lock")?;
        lock.lock().map_err(|_| "source-cache-io")?;
        let mut removed = 0;
        for (path, bytes, _) in self.entries()? {
            fs::remove_file(path).map_err(|_| "source-cache-io")?;
            removed += bytes;
        }
        Ok(removed)
    }
    fn entries(&self) -> Result<Vec<(PathBuf, u64, std::time::SystemTime)>, Error> {
        let mut entries = Vec::new();
        for entry in fs::read_dir(&self.directory).map_err(|_| "source-cache-io")? {
            let entry = entry.map_err(|_| "source-cache-io")?;
            let name = entry.file_name();
            let Some(key) = name.to_str().and_then(|s| s.strip_suffix(".zkcache")) else {
                continue;
            };
            if key.len() != 64 || !key.bytes().all(|c| c.is_ascii_hexdigit()) {
                continue;
            }
            let metadata = entry.metadata().map_err(|_| "source-cache-io")?;
            if entry.file_type().map_err(|_| "source-cache-io")?.is_file() {
                entries.push((
                    entry.path(),
                    metadata.len(),
                    metadata.modified().map_err(|_| "source-cache-io")?,
                ));
            }
        }
        Ok(entries)
    }
    fn retain(&self, path: &Path, bytes: &[u8]) -> Result<bool, Error> {
        if bytes.len() as u64 > self.capacity {
            return Ok(false);
        }
        let lock = self.lock("store.lock")?;
        lock.lock().map_err(|_| "source-cache-io")?;
        let mut entries = self.entries()?;
        let mut used = entries.iter().map(|e| e.1).sum::<u64>();
        entries.sort_by_key(|e| e.2);
        for (old, size, _) in entries {
            if used + bytes.len() as u64 <= self.capacity {
                break;
            }
            fs::remove_file(old).map_err(|_| "source-cache-io")?;
            used -= size;
        }
        let mut output =
            tempfile::NamedTempFile::new_in(&self.directory).map_err(|_| "source-cache-io")?;
        output.write_all(bytes).map_err(|_| "source-cache-io")?;
        output.persist(path).map_err(|_| "source-cache-io")?;
        Ok(true)
    }
    pub(super) fn build(
        &self,
        compiler: &Compiler,
        request: CompilationRequest<'_>,
    ) -> Result<CompilationResult, Error> {
        if request.observations.is_some() {
            let mut result = compiler.build(CompilationRequest {
                cache: None,
                ..request
            })?;
            result.cache =
                Some(serde_json::json!({"status":"recomputed","reason":"observations-requested"}));
            return Ok(result);
        }
        // Compile exactly this private snapshot, never the mutable paths prescanned
        // for a key. Names/formats and length-delimited bodies define its closure.
        let snapshot = Snapshot::capture(request.project)?;
        let identity = compiler.capabilities()?;
        let mut key = snapshot.identity;
        frame(
            &mut key,
            &serde_json::to_vec(&identity).map_err(|_| "source-cache-format")?,
        );
        frame(&mut key, request.selection.name.unwrap_or("").as_bytes());
        frame(&mut key, format!("{:?}", request.selection.kind).as_bytes());
        for flag in request.options.flags() {
            frame(&mut key, flag.as_bytes());
        }
        let key = crate::host::inputs::hex(&key.finalize());
        let path = self.directory.join(format!("{key}.zkcache"));
        // Bounded striped writer locks prevent partial/interleaved publication;
        // a concurrent compiler can recompute without waiting on another build.
        let writer = self.lock(&format!("writer-{}.lock", &key[..2]))?;
        let writing = writer.try_lock().is_ok();
        {
            let lock = self.lock("store.lock")?;
            lock.lock().map_err(|_| "source-cache-io")?;
            if let Ok(bytes) = io::read_regular(&path, Package::MAX_BYTES + 65) {
                let cached = (|| {
                    let (pin, package) = bytes.split_at_checked(65).ok_or("source-cache-format")?;
                    if pin[64] != b'\n' {
                        return Err("source-cache-format".into());
                    }
                    let text =
                        std::str::from_utf8(&pin[..64]).map_err(|_| "source-cache-format")?;
                    let pin = crate::host::inputs::digest(text)?;
                    let actual: [u8; 32] = Sha256::digest(package).into();
                    if actual != pin {
                        return Err("source-cache-format".into());
                    }
                    Compiler::captured(package, request.selection, request.options)
                        .map_err(|e| e.code)
                })();
                if let Ok(mut result) = cached {
                    result.cache = Some(serde_json::json!({"status":"hit","key":key}));
                    return Ok(result);
                }
                fs::remove_file(&path).map_err(|_| "source-cache-io")?;
            }
        }
        let mut result = compiler
            .build(CompilationRequest {
                project: &snapshot.project,
                cache: None,
                ..request
            })
            .map_err(|mut error| {
                if let Some(text) = &mut error.diagnostics {
                    for (captured, original) in &snapshot.diagnostic_paths {
                        *text = text.replace(captured, original);
                    }
                }
                if let Some(record) = &mut error.structured
                    && let Some(sources) = record["sources"].as_array_mut()
                {
                    for source in sources {
                        if let Some(path) = source["path"].as_str()
                            && let Some((_, original)) =
                                snapshot.diagnostic_paths.iter().find(|(p, _)| p == path)
                        {
                            source["path"] = serde_json::json!(original);
                        }
                    }
                }
                error
            })?;
        // A concurrently rebuilt compiler must not publish under the prior binary.
        if compiler.capabilities()? != identity {
            return Err("source-compiler-changed".into());
        }
        let mut bytes = crate::host::inputs::hex(result.package.identity()).into_bytes();
        bytes.push(b'\n');
        bytes.extend_from_slice(result.package.bytes());
        let retained = if writing && result.diagnostics.is_none() {
            self.retain(&path, &bytes)?
        } else {
            false
        };
        result.cache = Some(
            serde_json::json!({"status":"miss","key":key,"retained":retained,"capacity_bytes":self.capacity}),
        );
        Ok(result)
    }
}
fn frame(hash: &mut Sha256, bytes: &[u8]) {
    hash.update((bytes.len() as u64).to_le_bytes());
    hash.update(bytes);
}
struct Snapshot {
    _directory: tempfile::TempDir,
    project: Project,
    identity: Sha256,
    diagnostic_paths: Vec<(String, String)>,
}
impl Snapshot {
    fn capture(project: &Project) -> Result<Self, Error> {
        let directory = tempfile::tempdir().map_err(|_| "source-cache-io")?;
        let mut modules = std::collections::BTreeMap::new();
        let mut assets = std::collections::BTreeMap::new();
        let mut identity = Sha256::new();
        frame(&mut identity, b"zkc.compilation-cache/0");
        let mut total = 0usize;
        let mut diagnostic_paths = Vec::new();
        for (index, flag) in project.flags.iter().enumerate() {
            let (header, path, asset) = if let Some(module) = flag.strip_prefix("--module=") {
                let (name, path) = module.split_once('=').ok_or("source-project-format")?;
                (name.to_owned(), path, None)
            } else {
                let (name, rest) = flag
                    .strip_prefix("--asset=")
                    .and_then(|s| s.split_once('='))
                    .ok_or("source-project-format")?;
                let (format, path) = rest.split_once('=').ok_or("source-project-format")?;
                (name.to_owned(), path, Some(format))
            };
            let bytes = io::read_regular(
                path,
                if asset.is_some() {
                    64 * 1024 * 1024
                } else {
                    1024 * 1024
                },
            )
            .map_err(|_| "source-project-io")?;
            total = total
                .checked_add(bytes.len())
                .filter(|n| *n <= 72 * 1024 * 1024)
                .ok_or("source-project-limit")?;
            frame(&mut identity, header.as_bytes());
            frame(&mut identity, asset.unwrap_or("source").as_bytes());
            frame(&mut identity, &bytes);
            let target = directory.path().join(index.to_string());
            fs::write(&target, bytes).map_err(|_| "source-cache-io")?;
            diagnostic_paths.push((
                target.to_str().ok_or("source-cache-io")?.into(),
                path.into(),
            ));
            let path = target.to_str().ok_or("source-cache-io")?.to_owned();
            if let Some(format) = asset {
                assets.insert(
                    header,
                    super::Asset {
                        format: format.into(),
                        path,
                    },
                );
            } else {
                modules.insert(header, path);
            }
        }
        let project = Project::explicit(modules, assets)?;
        Ok(Self {
            _directory: directory,
            project,
            identity,
            diagnostic_paths,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;
    #[test]
    fn snapshots_are_owned_and_changes_in_every_input_kind_change_identity() {
        let root = tempfile::tempdir().unwrap();
        let source = root.path().join("main.zkc");
        let asset = root.path().join("relation.json");
        fs::write(&source, "module example;").unwrap();
        fs::write(&asset, "{}").unwrap();
        let project = Project::explicit(
            BTreeMap::from([("example".into(), source.to_str().unwrap().into())]),
            BTreeMap::from([(
                "relation".into(),
                super::super::Asset {
                    format: "air-json".into(),
                    path: asset.to_str().unwrap().into(),
                },
            )]),
        )
        .unwrap();
        let first = Snapshot::capture(&project).unwrap();
        let identity = first.identity.clone().finalize();
        fs::write(&source, "module example; // changed").unwrap();
        assert_ne!(
            identity,
            Snapshot::capture(&project).unwrap().identity.finalize()
        );
        // The first snapshot's private body is unchanged after external mutation.
        let flag = first
            .project
            .flags
            .iter()
            .find(|f| f.starts_with("--module="))
            .unwrap();
        assert_eq!(
            fs::read_to_string(flag.splitn(3, '=').nth(2).unwrap()).unwrap(),
            "module example;"
        );
        fs::write(&source, "module example;").unwrap();
        fs::write(&asset, "{\"changed\":true}").unwrap();
        assert_ne!(
            identity,
            Snapshot::capture(&project).unwrap().identity.finalize()
        );
    }
    #[test]
    fn publication_evicts_complete_records_and_skips_oversized_results() {
        let root = tempfile::tempdir().unwrap();
        let cache = CompilationCache::new(root.path(), 128).unwrap();
        let first = root.path().join(format!("{}.zkcache", "a".repeat(64)));
        let second = root.path().join(format!("{}.zkcache", "b".repeat(64)));
        assert!(cache.retain(&first, &[1; 80]).unwrap());
        assert!(cache.retain(&second, &[2; 80]).unwrap());
        assert!(!first.exists());
        assert_eq!(fs::read(&second).unwrap(), vec![2; 80]);
        assert!(!cache.retain(&first, &[3; 129]).unwrap());
        assert_eq!(
            cache.entries().unwrap().iter().map(|e| e.1).sum::<u64>(),
            80
        );
    }
    #[test]
    fn cleanup_owns_only_complete_cache_entries_and_capacity_is_bounded() {
        let root = tempfile::tempdir().unwrap();
        assert!(CompilationCache::new(root.path(), 0).is_err());
        assert!(CompilationCache::new(root.path(), 17 * 1024 * 1024 * 1024).is_err());
        let cache = CompilationCache::new(root.path(), 128).unwrap();
        fs::write(
            root.path().join(format!("{}.zkcache", "a".repeat(64))),
            b"abc",
        )
        .unwrap();
        fs::write(root.path().join("owner.txt"), b"preserve").unwrap();
        assert_eq!(cache.clear().unwrap(), 3);
        assert_eq!(cache.clear().unwrap(), 0);
        assert!(root.path().join("owner.txt").exists());
    }
}
