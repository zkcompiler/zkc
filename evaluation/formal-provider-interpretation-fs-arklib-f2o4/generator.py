#!/usr/bin/env python3
"""Untrusted generator for the finite ArkLib Fiat--Shamir interpretation."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
from types import ModuleType
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
GENERATED = HERE / "generated"
TEMPLATE = HERE / "template.lean"
TERM_PROBE = HERE / "TermEvaluatorProbe.lean"
LEAN_OUT = GENERATED / "FiatShamirSchnorrArkLib.lean"
CERTIFICATE_OUT = GENERATED / "certificate.json"

SOURCE_PACKAGE = ROOT / "evaluation/formal-source-fs-runtime-f0v3c"
SOURCE_MODEL = SOURCE_PACKAGE / "model.py"
SOURCE_RUNS = SOURCE_PACKAGE / "expected-runs-one-shot.json"
SOURCE_TABLE = SOURCE_PACKAGE / "derivation-vectors-one-shot.json"
RETRYING_RUNS = SOURCE_PACKAGE / "expected-runs.json"
RETRYING_TABLE = SOURCE_PACKAGE / "derivation-vectors.json"
BASE_MODULE = (
    ROOT
    / "evaluation/formal-provider-interpretation-arklib-f2o3/generated"
    / "SchnorrArkLib.lean"
)
TERM_VECTORS = (
    ROOT / "evaluation/formal-kernel-mechanization-m0/vectors/m2-term-calculus.json"
)
TERMINAL_MECHANIZATION = (
    ROOT / "evaluation/formal-kernel-mechanization-m0/lean/M0/Terminal.lean"
)

OWNER_PAGES = (
    ROOT / "docs-next/pir/interactive-core.md",
    ROOT / "docs-next/pir/fiat-shamir.md",
    ROOT / "docs-next/analysis/analysis-model.md",
)
PROFILE_MANIFESTS = (
    ROOT / "docs-next/foundation/semantic-profile-manifests.json",
    ROOT / "docs-next/pir/profiles/interaction.json",
    ROOT / "docs-next/analysis/profiles/kernel.json",
)
PACKAGE_INPUTS = (
    TEMPLATE,
    TERM_PROBE,
    SOURCE_MODEL,
    SOURCE_PACKAGE / "executor.py",
    SOURCE_PACKAGE / "replay.py",
    SOURCE_PACKAGE / "views.py",
    SOURCE_RUNS,
    SOURCE_TABLE,
    RETRYING_RUNS,
    RETRYING_TABLE,
    BASE_MODULE,
    TERM_VECTORS,
    TERMINAL_MECHANIZATION,
)

FORMAT = "zkc.formal-provider-interpretation.fs-arklib.certificate.v0"
PROVIDER_REVISION = "fad5cbf808774838924dc8273715724c6a6caa1f"
PROVIDER_TREE = "e38383088598a1305c15447c53db309ccd6b35ee"
VCVIO_REVISION = "cbd4144b51d92da00dd50f05e068b2348fa6e529"
VCVIO_TREE = "28c268057ed58427973e5bbf4854d472a7088954"
TOOLCHAIN = "leanprover/lean4:v4.31.0"
PROVIDER_DEFAULT = Path("/home/wonjae/code/ArkLib")
PROVIDER_SOURCE_FILES = (
    "ArkLib/OracleReduction/Basic.lean",
    "ArkLib/OracleReduction/Execution.lean",
    "ArkLib/OracleReduction/ProtocolSpec/Basic.lean",
    "ArkLib/OracleReduction/FiatShamir/Basic.lean",
    "lake-manifest.json",
    "lean-toolchain",
)


class GeneratorError(RuntimeError):
    """The named inputs do not determine the generated artifacts."""


def _require(condition: bool, detail: str) -> None:
    if not condition:
        raise GeneratorError(detail)


def _load(name: str, path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise ImportError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _file_pins(paths: tuple[Path, ...]) -> dict[str, str]:
    return {path.relative_to(ROOT).as_posix(): _sha256(path) for path in paths}


def _read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def _external_git_env() -> dict[str, str]:
    environment = dict(os.environ)
    for name in (
        "GIT_OBJECT_DIRECTORY",
        "GIT_ALTERNATE_OBJECT_DIRECTORIES",
        "GIT_INDEX_FILE",
        "GIT_WORK_TREE",
    ):
        environment.pop(name, None)
    return environment


def _provider_inputs() -> dict[str, Any]:
    provider = Path(
        os.environ.get("ZKC_ARKLIB_ROOT", str(PROVIDER_DEFAULT))
    ).resolve()
    _require(provider.is_dir(), f"pinned provider tree is absent: {provider}")
    revision = subprocess.run(
        ["git", "rev-parse", "HEAD", "HEAD^{tree}"],
        cwd=provider,
        env=_external_git_env(),
        check=False,
        capture_output=True,
        text=True,
    )
    _require(
        revision.returncode == 0
        and revision.stdout.split() == [PROVIDER_REVISION, PROVIDER_TREE],
        "provider revision or tree differs from the pin",
    )
    dependency = provider / ".lake/packages/VCVio"
    dep_revision = subprocess.run(
        ["git", "rev-parse", "HEAD", "HEAD^{tree}"],
        cwd=dependency,
        env=_external_git_env(),
        check=False,
        capture_output=True,
        text=True,
    )
    _require(
        dep_revision.returncode == 0
        and dep_revision.stdout.split() == [VCVIO_REVISION, VCVIO_TREE],
        "provider dependency revision or tree differs from the pin",
    )
    return {
        "git_tree": PROVIDER_TREE,
        "dependency_revision": VCVIO_REVISION,
        "dependency_tree": VCVIO_TREE,
        "source_sha256": {
            name: _sha256(provider / name) for name in PROVIDER_SOURCE_FILES
        },
    }


def _table() -> tuple[dict[str, Any], list[dict[str, int]]]:
    table = _read_json(SOURCE_TABLE)
    _require(
        table.get("format")
        == "zkc.formal-source-fs-runtime.derivation-vectors.v1",
        "derivation-table format drifted",
    )
    rows: list[dict[str, int]] = []
    for entry in table.get("entries", []):
        point = entry.get("input", {})
        output = entry.get("output", {})
        _require(
            point.get("challenge") == 0
            and type(point.get("statement")) is int
            and type(point.get("commitment")) is int
            and output.get("kind") == "value"
            and output.get("draw_count") == 1
            and type(output.get("value")) is int,
            "one-shot table has a non-value or malformed row",
        )
        rows.append(
            {
                "statement": point["statement"],
                "commitment": point["commitment"],
                "answer": output["value"],
            }
        )
    rows.sort(key=lambda row: (row["statement"], row["commitment"]))
    _require(
        [(row["statement"], row["commitment"]) for row in rows]
        == [(statement, commitment) for statement in range(3) for commitment in range(3)],
        "one-shot table is not the exact finite nine-point domain",
    )
    return table, rows


def lean_text() -> str:
    _table_value, rows = _table()
    cases = "\n".join(
        f"  | {row['statement']}, {row['commitment']} => some {row['answer']}"
        for row in rows
    )
    template = TEMPLATE.read_text(encoding="utf-8")
    _require(template.count("__TABLE_CASES__") == 1, "Lean template marker drifted")
    return template.replace("__TABLE_CASES__", cases)


def build_certificate() -> dict[str, Any]:
    table, rows = _table()
    source_model = _load("_fs_provider_generator_source_model", SOURCE_MODEL)
    subject = source_model.make_subject("one-shot")
    _require(
        subject.admission_outcome == "Affirmative",
        "the one-shot source is not owner-admitted",
    )
    return {
        "format": FORMAT,
        "authority": "none; untrusted generator output",
        "question": (
            "Does ArkLib's Fiat-Shamir transform of the generated finite Schnorr "
            "reduction correspond run for run to the admitted one-shot "
            "canonical-framed protocol under the exact table-backed oracle?"
        ),
        "subject": {
            "core_id": source_model.identifier_text(subject.construction.core_id),
            "transcript_construction_id": source_model.identifier_text(
                subject.construction.identifier
            ),
            "fs_protocol_id": source_model.identifier_text(
                subject.fs_protocol.identifier
            ),
            "maximum_draws": 1,
            "finite_table": rows,
            "run_count": 54,
        },
        "provider": {
            "name": "ArkLib",
            "revision": PROVIDER_REVISION,
            "toolchain": TOOLCHAIN,
            "module": "ArkLib.OracleReduction.FiatShamir.Basic",
            "definition": "Reduction.fiatShamir",
            "closed_carrier": {
                "schema": "Option Unit",
                "canonical_values": ["none", "some ()"],
            },
            "modelled_lanes": ["Accepted", "Rejected"],
            **_provider_inputs(),
        },
        "inputs": {
            "owner_pages": _file_pins(OWNER_PAGES),
            "profile_manifests": _file_pins(PROFILE_MANIFESTS),
            "package_inputs": _file_pins(PACKAGE_INPUTS),
        },
        "occurrence_to_step": [
            {"occurrence": 0, "kind": "ProverMessage", "step": "proof.commitment"},
            {"occurrence": 1, "kind": "Challenge", "step": "oracle.query.round-one"},
            {"occurrence": 2, "kind": "ProverMessage", "step": "proof.response"},
            {"occurrence": 3, "kind": "Check", "step": "verifier.check"},
            {"occurrence": 4, "kind": "Terminal", "step": "verifier.accept"},
            {"occurrence": 5, "kind": "Terminal", "step": "verifier.reject"},
        ],
        "type_map": [
            {"source": "public statement", "provider": "StmtIn", "carrier": "ZMod 3"},
            {"source": "private witness", "provider": "WitIn", "carrier": "ZMod 3"},
            {"source": "commitment", "provider": "proof round zero", "carrier": "ZMod 3"},
            {"source": "challenge", "provider": "oracle answer", "carrier": "ZMod 3"},
            {"source": "response", "provider": "proof round two", "carrier": "ZMod 3"},
            {"source": "check", "provider": "verifier predicate", "carrier": "Bool"},
            {"source": "terminal", "provider": "verifier result", "carrier": "Option Unit"},
        ],
        "lane_map": [
            {"lane": "Accepted", "provider_lane_image": {"case": "Image", "value": "some ()"}},
            {"lane": "Rejected", "provider_lane_image": {"case": "Image", "value": "none"}},
            {"lane": "Aborted", "provider_lane_image": {"case": "Unmodelled"}},
            {"lane": "InterpretationFailed", "provider_lane_image": {"case": "Unmodelled"}},
            {"lane": "StrategyStopped", "provider_lane_image": {"case": "Unmodelled"}},
            {"lane": "OperationalNoncompletion", "provider_lane_image": {"case": "Unmodelled"}},
        ],
        "source_table_sha256": _sha256(SOURCE_TABLE),
        "source_runs_sha256": _sha256(SOURCE_RUNS),
        "lean_sha256": hashlib.sha256(lean_text().encode("utf-8")).hexdigest(),
    }


def certificate_text() -> str:
    return json.dumps(build_certificate(), indent=2, sort_keys=True) + "\n"


def check_generated() -> None:
    _require(LEAN_OUT.read_text(encoding="utf-8") == lean_text(), "generated Lean drifted")
    _require(
        CERTIFICATE_OUT.read_text(encoding="utf-8") == certificate_text(),
        "generated certificate drifted",
    )


def write_generated() -> None:
    GENERATED.mkdir(exist_ok=True)
    LEAN_OUT.write_text(lean_text(), encoding="utf-8")
    CERTIFICATE_OUT.write_text(certificate_text(), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", action="store_true")
    parser.add_argument("--certificate", action="store_true")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    if sum((args.lean, args.certificate, args.check, args.write)) != 1:
        parser.error("select exactly one output mode")
    if args.check:
        check_generated()
        print("generated Fiat-Shamir module and certificate match their inputs")
    elif args.write:
        write_generated()
        print("generated Fiat-Shamir module and certificate written")
    elif args.lean:
        print(lean_text(), end="")
    else:
        print(certificate_text(), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
