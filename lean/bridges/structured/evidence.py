"""Durable reports and complete project-source archives for structured suites."""

import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import tarfile
import tempfile


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


def archive_sources(root, destination):
    """Archive current tracked and nonignored untracked project files.

    Read working bytes, not HEAD or index blobs. Keep all project sources so
    transitive local imports are included without maintaining a dependency list.
    Ignored build caches and external packages are deliberately not vendored;
    their manifests and toolchain pins are part of this project archive.
    """
    names = subprocess.check_output(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z"], cwd=root)
    files, deleted = {}, []
    archive = destination.with_suffix(".tar.gz")
    with tarfile.open(archive, "w:gz") as output:
        for name in sorted(set(os.fsdecode(name) for name in names.split(b"\0") if name)):
            source = root / name
            if not source.exists() and not source.is_symlink():
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
                assert retained.getmember(name).linkname == entry["symlink"]
            else:
                assert hashlib.sha256(retained.extractfile(name).read()).hexdigest() == entry["sha256"]
    manifest = destination.with_suffix(".json")
    atomic_json(manifest, {"files": files, "deletedTrackedPaths": deleted})
    return {"path": str(archive), "sha256": hashlib.sha256(archive.read_bytes()).hexdigest(),
            "manifest": str(manifest), "fileCount": len(files), "bytes": archive.stat().st_size,
            "scope": "all tracked and nonignored untracked project files at capture time; "
                     "external dependencies and ignored build caches excluded"}
