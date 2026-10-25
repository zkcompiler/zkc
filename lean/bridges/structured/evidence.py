"""Durable reports and scoped source archives for structured suites."""

import hashlib
import io
import json
import os
import shutil
from pathlib import Path
import subprocess
import tarfile
import tempfile


def owned_sources(directory, suffixes):
    """Walk a source owner, never caches, private experiments or directory links.

    Unlike rglob, os.walk with onerror does not silently drop unreadable trees.
    Ownership roots and source extensions are supplied by the suite, not Git.
    """
    def fail(error):
        raise error

    if directory.is_symlink():
        raise ValueError(f"source directory is a symlink: {directory}")
    excluded = {"build", "target", "__pycache__", "private", "experiments"}
    for parent, directories, files in os.walk(directory, onerror=fail, followlinks=False):
        directories[:] = sorted(name for name in directories
                                if not name.startswith(".") and name not in excluded)
        for name in directories:
            if (Path(parent) / name).is_symlink():
                raise ValueError(f"source directory is a symlink: {Path(parent) / name}")
        for name in sorted(files):
            path = Path(parent) / name
            if not name.startswith(".") and path.suffix in suffixes:
                if path.is_symlink():
                    raise ValueError(f"owned source is a symlink: {path}")
                yield path


def retain_tool(source, store, target):
    """Retain one executable per content digest and link it into a run.

    The store keeps a single read-only copy for each digest; every run's tool
    directory receives a hard link to it, or a copy where links are unsupported.
    Repeated suites therefore retain unchanged executables once. A stored copy is
    published only after its digest matches the source, and an existing entry
    whose bytes no longer match its name is replaced. The source and the linked
    file are rechecked afterwards."""
    def sha256(path):
        return hashlib.sha256(path.read_bytes()).hexdigest()

    expected = sha256(source)
    store.mkdir(parents=True, exist_ok=True)
    stored = store / f"{expected}-{source.name}"
    if not stored.exists() or sha256(stored) != expected:
        descriptor, name = tempfile.mkstemp(dir=store, prefix=f".{source.name}-")
        os.close(descriptor)
        partial = Path(name)
        try:
            shutil.copy2(source, partial)
            if sha256(partial) != expected:
                raise ValueError(f"tool changed during capture: {source}")
            partial.chmod(0o555)
            os.replace(partial, stored)
        finally:
            partial.unlink(missing_ok=True)
    try:
        os.link(stored, target)
    except OSError:
        shutil.copy2(stored, target)
    if sha256(target) != expected or sha256(source) != expected:
        raise ValueError(f"tool changed during capture: {source}")
    return expected


def atomic_json(path, value):
    """Publish a whole report, including across interruption or host restart."""
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=path.parent,
                                         delete=False) as stream:
            temporary = Path(stream.name)
            json.dump(value, stream, indent=2)
            stream.write("\n")
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
        descriptor = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(descriptor)
        finally:
            os.close(descriptor)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def source_names(root, inventory=None):
    """Normalize an explicit inventory, or ask Git for the working source set."""
    if inventory is None:
        names = subprocess.check_output(
            ["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z"], cwd=root)
        inventory = [os.fsdecode(name) for name in names.split(b"\0") if name]
    names = set()
    for entry in inventory:
        path = Path(entry)
        if path.is_absolute():
            path = path.relative_to(root)
        if ".." in path.parts or not path.parts:
            raise ValueError(f"source path must be within the project: {entry}")
        names.add(path.as_posix())
    return sorted(names)


def archive_sources(root, destination, *, inventory=None, scope=None):
    """Archive current tracked and nonignored untracked project files.

    Read working bytes, not HEAD or index blobs. Keep all project sources so
    transitive local imports are included without maintaining a dependency list.
    Ignored build caches and external packages are deliberately not vendored;
    their manifests and toolchain pins are part of this project archive.

    An explicit inventory requires every selected path to be readable and does
    not consult Git. Both modes use the same archive and manifest schema.
    """
    names = source_names(root, inventory)
    files, deleted = {}, []
    archive = destination.with_suffix(".tar.gz")
    with tarfile.open(archive, "w:gz") as output:
        for name in names:
            source = root / name
            if inventory is None and not source.exists() and not source.is_symlink():
                deleted.append(name)
                continue
            info = output.gettarinfo(str(source), arcname=name)
            if info.isfile():
                data = source.read_bytes()
                info.size = len(data)
                output.addfile(info, io.BytesIO(data))
                files[name] = {"sha256": hashlib.sha256(data).hexdigest(), "size": len(data)}
            elif info.issym():
                output.addfile(info)
                files[name] = {"symlink": info.linkname}
            else:
                raise ValueError(f"unsupported source entry (including submodules): {name}")
    # Verify retained contents, not just the compressed container's hash.
    with tarfile.open(archive) as retained:
        for name, entry in files.items():
            if "symlink" in entry:
                if not (retained.getmember(name).linkname == entry["symlink"]):
                    raise AssertionError('bridges/structured/evidence.py:152: retained.getmember(name).linkname == entry["symlink"]')
            else:
                if not (hashlib.sha256(retained.extractfile(name).read()).hexdigest() == entry["sha256"]):
                    raise AssertionError('bridges/structured/evidence.py:154: hashlib.sha256(retained.extractfile(name).read()).hexdigest() == entry["sha256"]')
    manifest = destination.with_suffix(".json")
    atomic_json(manifest, {"files": files, "deletedTrackedPaths": deleted})
    return {"path": str(archive), "sha256": hashlib.sha256(archive.read_bytes()).hexdigest(),
            "manifest": str(manifest), "fileCount": len(files), "bytes": archive.stat().st_size,
            "scope": scope or ("explicit project source inventory" if inventory is not None else
                     "all tracked and nonignored untracked project files at capture time; "
                     "external dependencies and ignored build caches excluded")}


def check_sources(root, archive, inventory=None):
    """Check captured identities without letting one unreadable path abort reporting."""
    manifest = json.loads(Path(archive["manifest"]).read_text(encoding="utf-8"))
    current, changed, restored, errors = {}, [], [], {}
    for name, before in manifest["files"].items():
        source = root / name
        try:
            if source.is_symlink():
                entry = {"symlink": os.readlink(source)}
            else:
                data = source.read_bytes()
                entry = {"sha256": hashlib.sha256(data).hexdigest(), "size": len(data)}
            current[name] = entry
            if entry != before:
                changed.append(name)
        except OSError as error:
            errors[name] = f"{type(error).__name__}: {error}"
    for name in manifest["deletedTrackedPaths"]:
        try:
            (root / name).lstat()
        except FileNotFoundError:
            continue
        except OSError as error:
            errors[name] = f"{type(error).__name__}: {error}"
        else:
            restored.append(name)
    previous = set(manifest["files"]) | set(manifest["deletedTrackedPaths"])
    added = sorted(set(source_names(root, inventory)) - previous)
    return {"name": "source-stability", "passed": not (changed or restored or errors or added),
            "files": current, "changed": changed, "restored": restored,
            "errors": errors, "added": added}
