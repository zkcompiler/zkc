"""Share immutable example packages within one pytest run, including xdist workers.

This is preparation for selected proof tests, not a persistent build cache.
Mutation and compiler-behavior tests continue to compile their own packages.
"""

import fcntl
from functools import lru_cache
from hashlib import sha256
import json
from pathlib import Path
import tempfile
import tomllib

from journal import Journal


@lru_cache(maxsize=16)
def _tool_digest(path, size, modified):
    return sha256(Path(path).read_bytes()).hexdigest()


def _tool_identity(path):
    path = Path(path).resolve()
    stat = path.stat()
    return {"path": str(path), "sha256": _tool_digest(str(path), stat.st_size, stat.st_mtime_ns)}


def _sources(project):
    document = tomllib.loads(project.read_text())
    # Keep the supported dependency surface explicit. A new project feature
    # must not silently introduce inputs absent from the preparation identity.
    assert document["format"] == "zkc.project/0"
    assert set(document) <= {"format", "modules", "assets"}, document.keys()
    paths = {project, *(project.parent / path for path in document["modules"].values()),
             *(project.parent / asset["path"] for asset in document.get("assets", {}).values())}
    return {str(path.resolve()): sha256(path.read_bytes()).hexdigest()
            for path in sorted(paths)}


class CompiledProjects:
    def __init__(self, directory, toolchain):
        self.directory = Path(directory)
        self.directory.mkdir(parents=True, exist_ok=True)
        self.toolchain = toolchain

    def compile(self, project, entry, flags, journal):
        project = Path(project).resolve()
        identity = {"sources": _sources(project), "entry": entry, "flags": list(flags),
                    "compiler": _tool_identity(self.toolchain.compiler),
                    "runtime": _tool_identity(self.toolchain.runtime)}
        key = sha256(json.dumps(identity, sort_keys=True).encode()).hexdigest()
        slot = self.directory / key
        slot.mkdir(exist_ok=True)
        manifest = slot / "package.json"
        # A session-scoped pytest fixture runs once per worker. The file lock
        # covers compilation and publication, and is released on process exit.
        with (slot / "lock").open("a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            if not manifest.exists():
                attempt = Path(tempfile.mkdtemp(prefix="compile-", dir=slot))
                preparation = Journal(attempt)
                package = attempt / "program.zkpkg"
                report = preparation.json([
                    self.toolchain.runtime, "--json", "compile",
                    f"--compiler={self.toolchain.compiler}", f"--project={project}",
                    entry, f"--output={package}", *flags,
                ], keep="compile")
                assert _sources(project) == identity["sources"], "project changed during compilation"
                pin = sha256(package.read_bytes()).hexdigest()
                assert pin == report["package_sha256"], report
                package.chmod(0o444)
                result = {"identity": identity, "package": str(package), "sha256": pin,
                          "journal": str(attempt / "commands.jsonl")}
                pending = preparation.write("package.json", result)
                pending.replace(manifest)
            result = json.loads(manifest.read_text())
            package = Path(result["package"])
            assert result["identity"] == identity
            assert sha256(package.read_bytes()).hexdigest() == result["sha256"], "shared package was modified"
        # Every consumer retains the provenance, without sharing proof files,
        # runtime state, inputs, or its own command journal.
        journal.write(f"preparations/{key}.json", result)
        return package, result["sha256"]
