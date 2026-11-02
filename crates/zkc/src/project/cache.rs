//! Optional local reuse of complete compilation outputs under captured inputs.
//! No witness, provider, session or mutable IR is retained here.
use super::{CompilationRequest, CompilationResult, Compiler, Error, Project};
use crate::{entry::Package, io};
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
        // Replacement consumes only the new record's size. Counting both copies
        // needlessly evicts other keys, including when repairing a corrupt entry.
        entries.retain(|entry| entry.0 != path);
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
    fn read(&self, path: &Path) -> Result<Option<Vec<u8>>, Error> {
        let lock = self.lock("store.lock")?;
        lock.lock().map_err(|_| "source-cache-io")?;
        let Ok(bytes) = io::read_regular(path, Package::MAX_BYTES + 65) else {
            return Ok(None);
        };
        let authenticated = bytes.split_at_checked(65).is_some_and(|(pin, package)| {
            let digest: [u8; 32] = Sha256::digest(package).into();
            pin[64] == b'\n'
                && std::str::from_utf8(&pin[..64])
                    .ok()
                    .and_then(|text| crate::io::bytes::digest(text).ok())
                    == Some(digest)
        });
        if !authenticated {
            fs::remove_file(path).map_err(|_| "source-cache-io")?;
            return Ok(None);
        }
        // The immutable owned bytes outlive this accounting lock. Package
        // validation and interface capture can run concurrently for other keys.
        Ok(Some(bytes))
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
        // for a key. The source format, names/formats and length-delimited bodies
        // define its closure.
        let snapshot = Snapshot::capture(request.project)?;
        let identity = compiler.capabilities()?;
        let mut key = snapshot.identity.clone();
        frame(
            &mut key,
            &serde_json::to_vec(&identity).map_err(|_| "source-cache-format")?,
        );
        frame(&mut key, request.selection.name.unwrap_or("").as_bytes());
        frame(&mut key, format!("{:?}", request.selection.kind).as_bytes());
        frame_options(&mut key, &request.options)?;
        let key = crate::io::bytes::hex(&key.finalize());
        let path = self.directory.join(format!("{key}.zkcache"));
        // Bounded striped writer locks prevent partial/interleaved publication;
        // a concurrent compiler can recompute without waiting on another build.
        let writer = self.lock(&format!("writer-{}.lock", &key[..2]))?;
        let writing = writer.try_lock().is_ok();
        if let Some(bytes) = self.read(&path)?
            && let Ok(mut result) =
                Compiler::captured(&bytes[65..], request.selection, request.options.clone())
        {
            result.cache = Some(serde_json::json!({"status":"hit","key":key}));
            return Ok(result);
        }
        let mut result = compiler
            .build(CompilationRequest {
                project: &snapshot.project,
                cache: None,
                ..request
            })
            .map_err(|error| snapshot.restore_diagnostics(error))?;
        // A concurrently rebuilt compiler must not publish under the prior binary.
        if compiler.capabilities()? != identity {
            return Err("source-compiler-changed".into());
        }
        let mut bytes = crate::io::bytes::hex(result.package.identity()).into_bytes();
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
fn frame_options(hash: &mut Sha256, options: &crate::entry::CompileOptions) -> Result<(), Error> {
    for flag in options.flags().map_err(|e| e.to_string())? {
        frame(hash, flag.as_bytes());
    }
    Ok(())
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
    fn restore_diagnostics(&self, mut error: Error) -> Error {
        if let Some(text) = &mut error.diagnostics {
            for (captured, original) in &self.diagnostic_paths {
                *text = text.replace(captured, original);
            }
            error.diagnostics_truncated |= super::compiler::trim_diagnostics(text);
        }
        if let Some(record) = &mut error.structured
            && let Some(sources) = record["sources"].as_array_mut()
        {
            for source in sources {
                if let Some(path) = source["path"].as_str()
                    && let Some((_, original)) =
                        self.diagnostic_paths.iter().find(|(p, _)| p == path)
                {
                    source["path"] = serde_json::json!(original);
                }
            }
        }
        error
    }
    fn capture(project: &Project) -> Result<Self, Error> {
        let directory = tempfile::tempdir().map_err(|_| "source-cache-io")?;
        let mut modules = std::collections::BTreeMap::new();
        let mut assets = std::collections::BTreeMap::new();
        let mut identity = Sha256::new();
        frame(&mut identity, b"zkc.compilation-cache/0");
        // The same bytes read under another grammar are another compilation.
        frame(&mut identity, project.source_format.as_str().as_bytes());
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
            // Fixed-width names cannot prefix another input's name in diagnostics.
            let target = directory.path().join(format!("{index:08x}"));
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
        let project = Project::explicit(project.source_format, modules, assets)?;
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
    use crate::project::SourceFormat;
    use std::collections::BTreeMap;
    #[test]
    fn snapshots_are_owned_and_changes_in_every_input_kind_change_identity() {
        let root = tempfile::tempdir().unwrap();
        let source = root.path().join("main.zkc");
        let asset = root.path().join("relation.json");
        fs::write(&source, "module example;").unwrap();
        fs::write(&asset, "{}").unwrap();
        let project = Project::explicit(
            SourceFormat::Zkc,
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
    fn the_source_format_is_part_of_the_snapshot_identity() {
        let root = tempfile::tempdir().unwrap();
        let source = root.path().join("main.zkc");
        fs::write(&source, "module example;").unwrap();
        let project = |format| {
            Project::explicit(
                format,
                BTreeMap::from([("example".into(), source.to_str().unwrap().into())]),
                BTreeMap::new(),
            )
            .unwrap()
        };
        let zkc = Snapshot::capture(&project(SourceFormat::Zkc)).unwrap();
        let layout = Snapshot::capture(&project(SourceFormat::ZkcLayout)).unwrap();
        // The private copy compiles under the selection it is keyed by.
        assert_eq!(zkc.project.source_format, SourceFormat::Zkc);
        assert_eq!(layout.project.source_format, SourceFormat::ZkcLayout);
        assert_ne!(zkc.identity.finalize(), layout.identity.finalize());
    }
    /// The same sources under another grammar never reuse a cached package.
    #[cfg(unix)]
    #[test]
    fn a_cached_package_is_reused_only_under_its_source_format() {
        use crate::entry::Package;
        use std::os::unix::fs::PermissionsExt;
        let root = tempfile::tempdir().unwrap();
        let digest = |bytes: &[u8]| crate::io::bytes::hex(&Sha256::digest(bytes));
        let schema = serde_json::json!({"kind":"unit","type":"()","identity":digest(b"()"),
            "generated":null,"custody":0,"sealed":false,"roles":[],"element":null,
            "constructible":true,"permissions":["Copy","Drop"],"fields":[],"alternatives":[],"leaves":[]});
        let interface = serde_json::json!({"format":"zkc.language-interface/0",
            "capture":digest(b"capture"),"original":digest(b"original"),"toolchain":"test",
            "entry":"example::Main","selection":{"kind":"function","function":"example::Main"},
            "functions":[{"symbol":"example::Main","parameters":[],"result":schema}],
            "protocols":[],"relations":[],"setups":[]});
        let options = super::super::ResolvedSettings::default().options();
        let package = serde_json::json!({"format":"zkc.entry/0","original":"original",
            "interface":interface.to_string(),"artifact":"artifact","assets":[],"options":options})
        .to_string();
        assert!(
            Package::capture(
                package.as_bytes(),
                &Sha256::digest(package.as_bytes()).into(),
                Package::MAX_BYTES
            )
            .is_ok()
        );
        let package_path = root.path().join("package.json");
        fs::write(&package_path, &package).unwrap();
        let log = root.path().join("formats.log");
        let compiler = root.path().join("compiler");
        fs::write(
            &compiler,
            format!(
                "#!/bin/sh\ncase \"$1\" in\n--capabilities) printf '%s' '{{\"format\":\"zkc.compiler-capabilities/0\"}}';;\n\
                 language-package) for arg do case \"$arg\" in --source-format=*) printf '%s\\n' \"${{arg#--source-format=}}\" >> '{}';; esac; done; cat '{}';;\n\
                 *) exit 9;;\nesac\n",
                log.display(),
                package_path.display()
            ),
        )
        .unwrap();
        fs::set_permissions(&compiler, fs::Permissions::from_mode(0o700)).unwrap();
        let compiler = Compiler::new(compiler.to_str().unwrap()).unwrap();
        let source = root.path().join("main.zkc");
        fs::write(&source, "module example;").unwrap();
        let cache = CompilationCache::new(root.path().join("cache"), 1024 * 1024).unwrap();
        let build = |format| {
            let project = Project::explicit(
                format,
                BTreeMap::from([("example".into(), source.to_str().unwrap().into())]),
                BTreeMap::new(),
            )
            .unwrap();
            let result = compiler
                .build(CompilationRequest {
                    project: &project,
                    selection: Default::default(),
                    options: options.clone(),
                    observations: None,
                    cache: Some(&cache),
                })
                .unwrap();
            assert_eq!(result.package.bytes(), package.as_bytes());
            result.cache.unwrap()
        };
        let first = build(SourceFormat::Zkc);
        assert_eq!(first["status"], "miss");
        assert_eq!(first["retained"], true);
        let reused = build(SourceFormat::Zkc);
        assert_eq!(reused["status"], "hit");
        assert_eq!(reused["key"], first["key"]);
        let other = build(SourceFormat::ZkcLayout);
        assert_eq!(other["status"], "miss");
        assert_ne!(other["key"], first["key"]);
        // Only misses invoke the compiler, each with the project's selection.
        assert_eq!(fs::read_to_string(&log).unwrap(), "zkc\nzkc-layout\n");
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
    fn replacing_a_record_does_not_evict_unrelated_entries() {
        let root = tempfile::tempdir().unwrap();
        let cache = CompilationCache::new(root.path(), 160).unwrap();
        let first = root.path().join(format!("{}.zkcache", "a".repeat(64)));
        let second = root.path().join(format!("{}.zkcache", "b".repeat(64)));
        assert!(cache.retain(&first, &[1; 80]).unwrap());
        assert!(cache.retain(&second, &[2; 80]).unwrap());
        assert!(cache.retain(&first, &[3; 80]).unwrap());
        assert_eq!(fs::read(&first).unwrap(), vec![3; 80]);
        assert_eq!(fs::read(&second).unwrap(), vec![2; 80]);
    }
    #[test]
    fn snapshot_diagnostics_restore_distinct_paths_and_keep_source_indices() {
        let root = tempfile::tempdir().unwrap();
        let modules = (0..12)
            .map(|index| {
                let name = format!("module{index:02}");
                let path = root.path().join(format!("{name}.zkc"));
                fs::write(&path, format!("module {name};")).unwrap();
                (name, path.to_str().unwrap().to_owned())
            })
            .collect();
        let project = Project::explicit(SourceFormat::Zkc, modules, BTreeMap::new()).unwrap();
        let mut snapshot = Snapshot::capture(&project).unwrap();
        let mut error: Error = "source-compilation".into();
        error.diagnostics = Some(
            snapshot
                .diagnostic_paths
                .iter()
                .map(|(path, _)| format!("{path}:1:2\n"))
                .collect(),
        );
        error.structured = Some(
            serde_json::json!({"sources":snapshot.diagnostic_paths.iter()
            .map(|(path,_)| serde_json::json!({"path":path})).collect::<Vec<_>>()}),
        );
        let error = snapshot.restore_diagnostics(error);
        let expected: String = snapshot
            .diagnostic_paths
            .iter()
            .map(|(_, path)| format!("{path}:1:2\n"))
            .collect();
        assert_eq!(error.diagnostics.unwrap(), expected);
        for (index, (_, original)) in snapshot.diagnostic_paths.iter().enumerate() {
            assert_eq!(
                error.structured.as_ref().unwrap()["sources"][index]["path"],
                *original
            );
        }
        snapshot.diagnostic_paths[0].1 = "xé".repeat(1300);
        let mut error: Error = "source-compilation".into();
        error.diagnostics = Some(snapshot.diagnostic_paths[0].0.repeat(20));
        let error = snapshot.restore_diagnostics(error);
        assert!(error.diagnostics_truncated);
        assert!(error.diagnostics.unwrap().len() <= 65536);
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
    #[test]
    fn oracle_selection_is_part_of_the_actual_cache_key() {
        use crate::entry::{OracleRoots, OracleSelection};
        let key = |options: &crate::entry::CompileOptions| {
            let mut hash = Sha256::new();
            frame_options(&mut hash, options).unwrap();
            hash.finalize()
        };
        let defaults = super::super::ResolvedSettings::default().options();
        let mut changed = defaults.clone();
        changed.oracle_realization.roots = OracleRoots::Exact(vec![]);
        assert_ne!(key(&defaults), key(&changed));
        let exact = |entries: &str| {
            OracleSelection::parse(&format!(
            r#"{{"format":"zkc.oracle-selection/0","roots":{{"kind":"exact","entries":{entries}}},"order":"unrestricted","authentication":"per-query"}}"#
        )).unwrap()
        };
        let a = r#"{"entry":"a","path":[0],"scheme":"","grouping":"individual","order":"natural"}"#;
        let b = a.replace(r#""a""#, r#""b""#);
        changed.oracle_realization = exact(&format!("[{a},{b}]"));
        let first = key(&changed);
        changed.oracle_realization = exact(&format!("[{b},{a}]"));
        assert_eq!(first, key(&changed));
        changed.oracle_realization.order = crate::entry::OracleQueryOrder::AfterFinalDraw;
        assert_ne!(first, key(&changed));
    }
}
