"""Public fixture and source-basis binding for copied replay."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

from .diagnostics import ProvenanceError
from .terms import artifact_id, canonical_json_bytes, framed_hash, load_json_bytes


PACKAGE_RELATIVE = Path("evaluation/duplex-sponge-transcript")
LOADED_REPO_ROOT = Path(__file__).resolve().parents[3]
PUBLIC_MODEL_FILES = (
    "__init__.py",
    "construction.py",
    "diagnostics.py",
    "execution.py",
    "independent.py",
    "mutations.py",
    "provenance.py",
    "report.py",
    "terms.py",
    "transition.py",
)


@dataclass(frozen=True)
class FixtureBinding:
    path: str
    role: str
    raw: bytes
    value: Any
    artifact_content_id: str
    canonical_content_id: str

    def public_term(self) -> dict[str, str]:
        return {
            "path": self.path,
            "role": self.role,
            "artifact_content_id": self.artifact_content_id,
            "canonical_content_id": self.canonical_content_id,
        }


def assert_loaded_root(repo_root: Path) -> Path:
    try:
        resolved = repo_root.resolve(strict=True)
    except OSError as error:
        raise ProvenanceError(f"replay root cannot be resolved: {error}") from error
    if resolved != LOADED_REPO_ROOT.resolve(strict=True):
        raise ProvenanceError("requested replay root differs from the loaded source root")
    return resolved


def load_fixture(repo_root: Path, relative: str, *, role: str) -> FixtureBinding:
    root = assert_loaded_root(repo_root)
    relative_path = Path(relative)
    if relative_path.is_absolute() or ".." in relative_path.parts:
        raise ProvenanceError("fixture path must be repository relative")
    path = root / relative_path
    try:
        raw = path.read_bytes()
    except OSError as error:
        raise ProvenanceError(f"fixture cannot be read: {relative}") from error
    value = load_json_bytes(raw)
    return FixtureBinding(
        relative_path.as_posix(),
        role,
        raw,
        value,
        artifact_id(raw),
        framed_hash("zkc.artifact.canonical-json", (canonical_json_bytes(value),)),
    )


def public_source_paths(repo_root: Path) -> tuple[Path, ...]:
    root = assert_loaded_root(repo_root)
    model_root = root / PACKAGE_RELATIVE / "duplexmodel"
    actual = {path.name for path in model_root.glob("*.py")}
    if actual != set(PUBLIC_MODEL_FILES):
        raise ProvenanceError("public model source allowlist differs")
    paths = tuple(model_root / name for name in PUBLIC_MODEL_FILES) + (
        root / PACKAGE_RELATIVE / "run.py",
    )
    if any(not path.is_file() or path.is_symlink() for path in paths):
        raise ProvenanceError("public source closure is incomplete")
    return paths


def source_manifest(repo_root: Path) -> tuple[dict[str, str], ...]:
    root = assert_loaded_root(repo_root)
    entries: list[dict[str, str]] = []
    for path in public_source_paths(root):
        raw = path.read_bytes()
        entries.append(
            {
                "path": path.relative_to(root).as_posix(),
                "artifact_content_id": artifact_id(raw),
            }
        )
    return tuple(entries)


def validation_basis_id(
    manifest: Iterable[dict[str, str]], fixtures: Iterable[FixtureBinding]
) -> str:
    body = {
        "source_manifest": list(manifest),
        "public_fixtures": [fixture.public_term() for fixture in fixtures],
        "provider_classification": "DeterministicTransitionConformanceOnly",
        "operational_assumptions": [
            "stable checkout during one replay",
            "standard Python integer and byte semantics",
            "no hostile same-process mutation",
        ],
    }
    return framed_hash("zkc.validation.basis", (canonical_json_bytes(body),))


def report_source_paths() -> tuple[str, ...]:
    return tuple(
        path.relative_to(LOADED_REPO_ROOT).as_posix()
        for path in public_source_paths(LOADED_REPO_ROOT)
    )
