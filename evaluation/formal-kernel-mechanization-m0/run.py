#!/usr/bin/env python3
"""Run the M2 mechanized portable-term and Schnorr-denotation gate.

The gate answers one bounded question: can the K1 portable-term calculus and
the R1B finite Schnorr check denotation be mechanized in core Lean, while
retaining M0/M1 and reproducing every available predecessor golden?  The K1
independent oracle currently contains no term-evaluation operation, so that
required evidence remains CannotAnswer even when the Lean/R1B comparisons
pass.  Nothing under `lean/` is normative.

When no Lean toolchain is available the Lean-dependent findings are classified
`Unsupported/M0-U-LEAN-TOOLCHAIN` and the frozen comparison fails; the gate
never passes silently without building and running the Lean text.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time
from types import ModuleType
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
LEAN = HERE / "lean"
VECTORS = HERE / "vectors"
EXPECTED = HERE / "expected-findings.json"
EXPORT = HERE / "export_vectors.py"
M2_EXPORT = HERE / "export_m2_vectors.py"
M2_VECTORS = VECTORS / "m2-term-calculus.json"
D1_EXPECTED = (
    ROOT / "evaluation/formal-source-integrated-graph-f0v2b2d1/expected-findings.json"
)
ORACLE_CASES = ROOT / "evaluation/k1-executable-foundations/oracle/cases"
FOUNDATION = ROOT / "docs-next/foundation/executable-foundations.md"
TARGET = ROOT / "docs-next/pir/interactive-core.md"

AFFIRMATIVE_AGGREGATE = "M2-A-TERM-CALCULUS-REPRODUCES-GOLDENS"
CANNOT_ANSWER_AGGREGATE = "M2-C-TERM-EVALUATION-ORACLE-ABSENT"
TOOLCHAIN = "leanprover/lean4:v4.33.1"
LEAN_VERSION = "4.33.1"
D1_AGGREGATE = "F0V2B2D1-A-INTEGRATED-PCGRAPH-CLOSURE"
D1_FINDINGS_SHA256 = "6df7aa212836ddd9f4eb4f740167b9183a8e155c853cd3ee7e801f832e75e48a"
ORACLE_REQUESTS_SHA256 = "43302085a81540e6d7aca57c2ec15338fd2082ddf0b5960517cedac5e6600b8e"
ORACLE_EXPECTED_SHA256 = "c7c6f87c5cd591f25e604ed157134e5d113449d1fea0c48eaeb9e76a9e7eab42"
ORACLE_BOUNDARY_SHA256 = "318b98c12f6a5a358885cff8e0dcbc13e7c0f38796a0dc2c036fe6eb6f334d41"
STANDARD_AXIOMS = frozenset(("propext", "Classical.choice", "Quot.sound"))
KERNEL_MODULES = (
    "Datum", "Encode", "Decode", "Core", "PCGraph", "Theorems", "Term", "Eval"
)
TRANSPORT_MODULES = ("Transport",)
PRIMARY_THEOREMS = (
    "M0.decode_encode", "M0.parse_canonical", "M0.decode_canonical",
    "M0.encode_injective", "M0.encode_prefix_free"
)
ORDER_THEOREMS = ("M0.class_fold_topological_order_independent",)
MAGNITUDE_THEOREMS = ("M0.magnitude_eq_quadratic",)
M2_THEOREMS = (
    "M0.evaluation_deterministic",
    "M0.evaluation_completed_mono",
    "M0.schnorr_denotation_eq_closed_form",
)
LATTICE_THEOREMS = (
    "M0.Join_cons",
    "M0.PCClass.join_assoc",
    "M0.PCClass.join_comm",
    "M0.PCClass.join_idem",
    "M0.PCClass.join_invalid_left",
    "M0.PCClass.join_invalid_right",
)
UNSUPPORTED_OUTCOME = "Unsupported"
UNSUPPORTED_CODE = "M0-U-LEAN-TOOLCHAIN"
BUILD_TIMEOUT_SECONDS = 1800
FORBIDDEN_IMPORT = re.compile(r"^\s*import\s+(Mathlib|Batteries|Std|VCVio|ArkLib)\b", re.M)


class GateFailure(RuntimeError):
    """The package detected drift, disagreement, or a checker defect."""


@dataclass(frozen=True)
class Finding:
    name: str
    outcome: str
    code: str

    def value(self) -> list[str]:
        return [self.name, self.outcome, self.code]


def _load(name: str, path: Path) -> ModuleType:
    if name in sys.modules:
        return sys.modules[name]
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:  # pragma: no cover - host failure
        raise ImportError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _require(condition: bool, detail: str) -> None:
    if not condition:
        raise GateFailure(detail)


def _finding(name: str, outcome: str, code: str) -> Finding:
    return Finding(name, outcome, code)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


# --- Lean toolchain discovery -----------------------------------------------------


@dataclass(frozen=True)
class Toolchain:
    lake: str | None
    reason: str
    elan: str | None


def _discover_toolchain() -> Toolchain:
    """Find a `lake` that will run the pinned toolchain without the network."""

    pinned = (LEAN / "lean-toolchain").read_text(encoding="utf-8").strip()
    if pinned != TOOLCHAIN:
        return Toolchain(None, f"lean-toolchain pins {pinned!r}, expected {TOOLCHAIN!r}", None)
    override = os.environ.get("ZKC_LAKE")
    if override is not None:
        # An explicit override is used as given; a wrong one does not fall back.
        if not Path(override).is_file():
            return Toolchain(None, f"ZKC_LAKE names no executable: {override!r}", None)
        candidates = [override]
    else:
        candidates = [shutil.which("lake"), str(Path.home() / ".elan" / "bin" / "lake")]
    lake = next((item for item in candidates if item and Path(item).is_file()), None)
    if lake is None:
        return Toolchain(None, "no lake executable found on PATH or under ~/.elan/bin", None)
    elan_candidates = [shutil.which("elan"), str(Path(lake).parent / "elan")]
    elan = next((item for item in elan_candidates if item and Path(item).is_file()), None)
    if elan is not None:
        listed = subprocess.run(
            (elan, "toolchain", "list"), check=False, capture_output=True, text=True
        )
        if TOOLCHAIN not in listed.stdout.split():
            return Toolchain(
                None,
                f"elan does not have {TOOLCHAIN} installed; installing it needs the network",
                elan,
            )
        return Toolchain(lake, f"elan-managed lake at {lake}", elan)
    version = subprocess.run(
        (lake, "--version"), cwd=LEAN, check=False, capture_output=True, text=True
    )
    if f"Lean version {LEAN_VERSION}" not in version.stdout:
        return Toolchain(
            None, f"lake at {lake} does not run Lean {LEAN_VERSION}: {version.stdout.strip()}", None
        )
    return Toolchain(lake, f"lake at {lake} runs Lean {LEAN_VERSION}", None)


def _run_lake(toolchain: Toolchain, arguments: tuple[str, ...]) -> tuple[subprocess.CompletedProcess[str], float]:
    assert toolchain.lake is not None
    started = time.perf_counter()
    completed = subprocess.run(
        (toolchain.lake, *arguments),
        cwd=LEAN,
        check=False,
        capture_output=True,
        text=True,
        timeout=BUILD_TIMEOUT_SECONDS,
    )
    return completed, time.perf_counter() - started


# --- static facts about the Lean text ---------------------------------------------


def _lean_sources() -> list[Path]:
    return sorted(
        [*(LEAN / "M0").glob("*.lean"), LEAN / "M0.lean", LEAN / "Main.lean", LEAN / "Axioms.lean"]
    )


def _lean_boundary() -> dict[str, Any]:
    """Imports, forbidden libraries, `sorry`, and declared axioms in the Lean text."""

    imports: dict[str, list[str]] = {}
    sorries: list[str] = []
    axioms: list[str] = []
    forbidden: list[str] = []
    for path in _lean_sources():
        text = path.read_text(encoding="utf-8")
        name = path.relative_to(LEAN).as_posix()
        imports[name] = re.findall(r"^\s*import\s+(\S+)", text, re.M)
        if re.search(r"\bsorry\b", text):
            sorries.append(name)
        if re.search(r"^\s*axiom\b", text, re.M):
            axioms.append(name)
        if FORBIDDEN_IMPORT.search(text):
            forbidden.append(name)
    lakefile = (LEAN / "lakefile.lean").read_text(encoding="utf-8")
    kernel_imports_only_m0 = all(
        all(item.startswith("M0") for item in imports[f"M0/{module}.lean"])
        for module in KERNEL_MODULES
    )
    json_importers = sorted(
        name for name, items in imports.items() if any(item.startswith("Lean") for item in items)
    )
    return {
        "imports": imports,
        "sorry_files": sorries,
        "axiom_files": axioms,
        "forbidden_import_files": forbidden,
        "lakefile_requires": bool(re.search(r"^\s*require\b", lakefile, re.M)),
        "kernel_modules_import_only_m0": kernel_imports_only_m0,
        "lean_library_importers": json_importers,
    }


def _line_counts() -> dict[str, dict[str, int]]:
    counts: dict[str, dict[str, int]] = {}
    for path in _lean_sources() + [LEAN / "lakefile.lean"]:
        lines = path.read_text(encoding="utf-8").splitlines()
        code = 0
        in_block = False
        for line in lines:
            stripped = line.strip()
            if in_block:
                if "-/" in stripped:
                    in_block = False
                continue
            if stripped.startswith("/-"):
                if "-/" not in stripped:
                    in_block = True
                continue
            if not stripped or stripped.startswith("--"):
                continue
            code += 1
        counts[path.relative_to(LEAN).as_posix()] = {"lines": len(lines), "code_lines": code}
    return counts


AXIOM_LINE = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]")
NO_AXIOM_LINE = re.compile(r"'([^']+)' does not depend on any axioms")


def _parse_axioms(text: str) -> dict[str, list[str]]:
    closure: dict[str, list[str]] = {}
    for match in AXIOM_LINE.finditer(text):
        closure[match.group(1)] = [item.strip() for item in match.group(2).split(",") if item.strip()]
    for match in NO_AXIOM_LINE.finditer(text):
        closure[match.group(1)] = []
    return closure


# --- Python boundary probe ---------------------------------------------------------


def _nat_boundary_probe(k1: ModuleType) -> dict[str, Any]:
    """Measure the K1 encoder at exactly the constitutional byte bound.

    The Foundation page says reaching a bound is allowed. A natural whose
    canonical encoding is exactly `2^20` octets (one tag, eight length octets,
    a `2^20 - 9` octet magnitude) reaches it; so do a symbol, an octet string,
    and a signed integer of the same total length.
    """

    limit = k1.MAX_CANONICAL_BYTES
    size = limit - 9

    def verdict(value: object) -> str:
        try:
            encoded = k1.encode_datum(value)
        except k1.CanonicalError as error:
            return f"refused: {error}"
        return f"accepted: {len(encoded)} octets"

    exact_nat = k1.Nat(1 << (8 * (size - 1)))
    crossing_nat = k1.Nat(1 << (8 * size))
    nat_raw = b"\x03" + size.to_bytes(8, "big") + b"\x01" + b"\x00" * (size - 1)
    try:
        k1.decode_datum(nat_raw)
        nat_decode = "accepted"
    except k1.CanonicalError as error:
        nat_decode = f"refused: {error}"
    return {
        "byte_bound": limit,
        "nat_magnitude_octets": size,
        "nat_encode": verdict(exact_nat),
        "nat_decode_of_exact_bound_input": nat_decode,
        "nat_crossing_encode": verdict(crossing_nat),
        "symbol_encode": verdict(k1.Symbol("a" * size)),
        "bytes_encode": verdict(k1.BytesValue(b"a" * size)),
        "int_encode": verdict(k1.IntValue(1 << (8 * (size - 2)))),
    }


# --- the gate --------------------------------------------------------------------


def evaluate(artifacts: Path) -> tuple[list[Finding], dict[str, Any]]:
    started = time.perf_counter()
    timings: dict[str, float] = {}
    findings: list[Finding] = []
    export = _load("_zkc_m0_export", EXPORT)
    m2_export = _load("_zkc_m2_export", M2_EXPORT)
    k1 = export._load("_zkc_m0_k1", export.K1_MODEL)

    # Predecessor pins.
    d1 = _read_json(D1_EXPECTED)
    _require(
        d1["aggregate"] == D1_AGGREGATE and d1["findings_sha256"] == D1_FINDINGS_SHA256,
        "D1 predecessor result drifted",
    )
    _require(
        _sha256(ORACLE_CASES / "requests.jsonl") == ORACLE_REQUESTS_SHA256
        and _sha256(ORACLE_CASES / "expected.jsonl") == ORACLE_EXPECTED_SHA256,
        "K1 oracle case files drifted",
    )
    _require(
        _sha256(ORACLE_CASES / "natural-byte-bound.json") == ORACLE_BOUNDARY_SHA256,
        "K1 natural byte-bound vectors drifted",
    )
    findings.append(_finding("predecessor-pin", "Affirmative", "M0-A-PREDECESSOR-PIN"))

    # Target law pins and nonpublication.
    foundation = FOUNDATION.read_text(encoding="utf-8")
    target = TARGET.read_text(encoding="utf-8")
    tag_rows = ("| `0x00` | Unit |", "| `0x03` | Natural |", "| `0x04` | Signed integer |",
                "| `0x08` | Record |", "| `0x09` | Variant |")
    _require(
        all(row in foundation for row in tag_rows)
        and "maximum root-zero depth        = 384" in foundation
        and "consumes exactly one value" in foundation
        and "PCClass = StaticPublic | PublicHistory | VerifierPrivate | Invalid" in target
        and "least `M(PCNodeBody(node))`" in target
        and "Publish(x) = PublicHistory" in target
        and "V(13,R{0:N(occurrence_ref),1:N(output_ordinal)})" in target,
        "Foundation or Section 11 law text drifted",
    )
    _require(
        "formal-kernel-mechanization" not in foundation
        and "formal-kernel-mechanization" not in target
        and "M0-" not in foundation
        and "M0-" not in target,
        "target pages mention this package",
    )
    findings.extend(
        (
            _finding("target-law-pin", "Affirmative", "M0-A-TARGET-LAW-PIN"),
            _finding("target-authority-untouched", "Affirmative", "M0-A-NONPUBLICATION"),
        )
    )

    # The committed vectors are exactly what the predecessors export today.
    t0 = time.perf_counter()
    regenerated = export.export()
    t1 = time.perf_counter()
    regenerated_m2 = m2_export.export()
    timings["m2_vector_export_seconds"] = round(time.perf_counter() - t1, 3)
    timings["vector_export_seconds"] = round(time.perf_counter() - t0, 3)
    committed = {name: (VECTORS / name).read_text(encoding="utf-8") for name in regenerated}
    _require(
        all(committed[name] == export._dump(value) for name, value in regenerated.items()),
        "committed vectors differ from the regenerated export",
    )
    _require(
        M2_VECTORS.read_text(encoding="utf-8") == m2_export._dump(regenerated_m2),
        "committed M2 vectors differ from the regenerated export",
    )
    findings.append(_finding("vector-export-stable", "Affirmative", "M0-A-VECTOR-EXPORT-STABLE"))

    # The Lean text depends on the core library only.
    boundary = _lean_boundary()
    _require(
        not boundary["forbidden_import_files"]
        and not boundary["lakefile_requires"]
        and boundary["kernel_modules_import_only_m0"]
        and not boundary["sorry_files"]
        and not boundary["axiom_files"]
        and boundary["lean_library_importers"] == ["M0/Transport.lean"],
        f"Lean dependency boundary violated: {boundary}",
    )
    findings.append(_finding("core-lean-only", "Affirmative", "M0-A-CORE-LEAN-ONLY"))

    # Toolchain.
    toolchain = _discover_toolchain()
    lean_available = toolchain.lake is not None
    metrics: dict[str, Any] = {
        "toolchain": {"pinned": TOOLCHAIN, "available": lean_available, "reason": toolchain.reason},
        "lean_line_counts": _line_counts(),
        "lean_boundary": {k: v for k, v in boundary.items() if k != "imports"},
    }

    def lean_finding(name: str, ok: bool, code: str) -> Finding:
        if not lean_available:
            return _finding(name, UNSUPPORTED_OUTCOME, UNSUPPORTED_CODE)
        return _finding(name, "Affirmative" if ok else "Refused", code if ok else code.replace("-A-", "-R-"))

    report: dict[str, Any] = {}
    axioms: dict[str, list[str]] = {}
    build_ok = False
    if lean_available:
        was_built = (LEAN / ".lake" / "build" / "lib").is_dir()
        build, seconds = _run_lake(toolchain, ("build",))
        timings["lake_build_seconds"] = round(seconds, 3)
        metrics["lake_build_was_warm"] = was_built
        build_ok = build.returncode == 0 and "declaration uses 'sorry'" not in build.stdout + build.stderr
        (artifacts / "lake-build.log").write_text(build.stdout + build.stderr, encoding="utf-8")
        _require(build_ok, f"lake build failed:\n{build.stdout}\n{build.stderr}")

        # Assemble the Lean input: committed vectors plus digest-checked regenerated bodies.
        t0 = time.perf_counter()
        d1_model = export._load("_zkc_m0_d1_model", export.D1_MODEL)
        bodies = export.regenerate_bodies(d1_model, k1)
        digests = {row["name"]: row for row in regenerated["body-digests.json"]["bodies"]}
        _require(set(bodies) == set(digests), "regenerated body names differ from the pinned digests")
        _require(
            all(bodies[name]["sha256"] == digests[name]["sha256"] for name in bodies),
            "regenerated D1 bodies differ from the pinned digests",
        )
        encode_rows = list(regenerated["k1-encoding-vectors.json"]["encode"]) + [
            {"name": row["name"], "source": row["source"], "value": row["value"], "hex": row["hex"]}
            for row in bodies.values()
        ]
        reject_rows = list(regenerated["k1-encoding-vectors.json"]["reject"]) + list(
            regenerated["structural-negatives.json"]["reject"]
        )
        lean_input = {
            "encode": encode_rows,
            "reject": reject_rows,
            "pcgraph_construction": regenerated["pcgraph-construction.json"]["carriers"],
            "m2": regenerated_m2,
        }
        input_path = artifacts / "m0-input.json"
        input_path.write_text(json.dumps(lean_input, separators=(",", ":")), encoding="utf-8")
        timings["lean_input_assembly_seconds"] = round(time.perf_counter() - t0, 3)

        run, seconds = _run_lake(toolchain, ("exe", "m0", str(input_path)))
        timings["lake_exe_seconds"] = round(seconds, 3)
        _require(run.returncode == 0, f"lake exe m0 failed:\n{run.stdout}\n{run.stderr}")
        (artifacts / "m0-report.json").write_text(run.stdout, encoding="utf-8")
        report = json.loads(run.stdout)

        axiom_run, seconds = _run_lake(toolchain, ("env", "lean", "Axioms.lean"))
        timings["axiom_report_seconds"] = round(seconds, 3)
        _require(axiom_run.returncode == 0, f"axiom report failed:\n{axiom_run.stdout}\n{axiom_run.stderr}")
        axioms = _parse_axioms(axiom_run.stdout)
    findings.append(lean_finding("lean-build", build_ok, "M1-A-LEAN-BUILD"))

    # Retained M0 basis: canonical encoder/decoder vectors still agree.
    by_source: dict[str, list[dict[str, Any]]] = {}
    for row in report.get("encode", []):
        by_source.setdefault(row["source"], []).append(row)

    def all_encode(source: str) -> bool:
        rows = by_source.get(source, [])
        return bool(rows) and all(
            row["encode_matches"] and row["well_formed"] and row["within_limits"]
            and row["transport_error"] is None
            for row in rows
        )

    encoding_ok = all(all_encode(source) for source in (
        "k1-oracle", "d1-core-body", "d1-public-coin-body"
    ))
    rows = report.get("encode", [])
    roundtrip_ok = bool(rows) and all(row["decode_roundtrips"] and row["decoded_equals_value"] for row in rows)
    rejects = {row["name"]: row["rejected"] for row in report.get("reject", [])}
    oracle_rejects = [name for name in rejects if name.startswith("k1-oracle/")]
    crafted_rejects = [name for name in rejects if name.startswith("crafted/")]
    oracle_reject_ok = bool(oracle_rejects) and all(rejects[name] for name in oracle_rejects)
    crafted_reject_ok = bool(crafted_rejects) and all(rejects[name] for name in crafted_rejects)
    retained_ok = encoding_ok and roundtrip_ok and oracle_reject_ok and crafted_reject_ok
    findings.extend(
        (
            lean_finding("retained-m0-encoding-goldens", encoding_ok, "M1-A-RETAINED-ENCODING-GOLDENS"),
            lean_finding("retained-m0-decoder-vectors", roundtrip_ok and oracle_reject_ok and crafted_reject_ok,
                         "M1-A-RETAINED-DECODER-VECTORS"),
        )
    )

    # Stage 1: derive all graph products from decoded Core and module declarations.
    carriers = report.get("pcgraph_construction", [])
    core_ok = len(carriers) == 5 and all(row["core_tables_decoded"] == 14 for row in carriers)
    modules_ok = bool(carriers) and all(row["module_declarations_decoded"] > 0 for row in carriers)
    nodes_ok = bool(carriers) and all(row["nodes_match"] for row in carriers)
    edges_ok = bool(carriers) and all(row["edges_match"] for row in carriers)
    edge_families_ok = bool(carriers) and all(
        row["terminal_preemption_edges"] > 0
        and row["oracle_query_answer_edges"] > 0
        and row["module_edges"] > 0
        for row in carriers
    )
    order_ok = bool(carriers) and all(row["order_matches"] for row in carriers)
    classes_ok = bool(carriers) and all(row["classes_match"] for row in carriers)
    sinks_ok = bool(carriers) and all(
        row["sinks_match"] and row["acceptance_sinks_match"]
        and row["private_predecessors_match"] for row in carriers
    )
    cones_ok = bool(carriers) and all(
        row["logical_cones_match"] and row["logical_intersections_match"] for row in carriers
    )
    readings_agree = bool(carriers) and all(row["challenge_readings_agree"] for row in carriers)
    stage1_ok = all((core_ok, modules_ok, nodes_ok, edges_ok, edge_families_ok,
                     order_ok, classes_ok, sinks_ok, cones_ok))
    findings.extend(
        (
            lean_finding("decode-fourteen-core-tables", core_ok, "M1-A-S1-CORE-TABLES-DECODED"),
            lean_finding("decode-used-module-declarations", modules_ok, "M1-A-S1-MODULE-DECLARATIONS-DECODED"),
            lean_finding("derived-node-sets-five-carriers", nodes_ok, "M1-A-S1-NODE-SETS"),
            lean_finding("derived-edge-sets-five-carriers", edges_ok, "M1-A-S1-EDGE-SETS"),
            lean_finding("terminal-oracle-module-edge-families", edge_families_ok,
                         "M1-A-S1-EDGE-FAMILIES-EXERCISED"),
            lean_finding("kahn-order-five-carriers", order_ok, "M1-A-S1-KAHN-ORDER"),
            lean_finding("class-tables-five-carriers", classes_ok, "M1-A-S1-CLASS-TABLES"),
            lean_finding("sink-products-five-carriers", sinks_ok, "M1-A-S1-SINK-PRODUCTS"),
            lean_finding("logical-cones-five-carriers", cones_ok, "M1-A-S1-LOGICAL-CONES"),
            lean_finding("stage-1-graph-construction", stage1_ok, "M1-A-S1-GRAPH-CONSTRUCTION"),
            _finding("challenge-dependency-order-wording", "CannotAnswer",
                     "M1-C-S11-CHALLENGE-DEPENDENCY-ORDER"),
            _finding("public-query-transfer-coordinate-wording", "CannotAnswer",
                     "M1-C-S11-PUBLIC-QUERY-COORDINATE"),
            _finding("verifier-message-transfer-coordinate-wording", "CannotAnswer",
                     "M1-C-S11-VERIFIER-MESSAGE-COORDINATE"),
            _finding("logical-publication-transfer-coordinate-wording", "CannotAnswer",
                     "M1-C-S11-LOGICAL-PUBLICATION-COORDINATE"),
            _finding("public-query-sink-coordinate-wording", "CannotAnswer",
                     "M1-C-S11-PUBLIC-QUERY-SINK-COORDINATE"),
        )
    )

    # Stages 2 and 3: decoder canonicity and class-table uniqueness.
    def proved(names: tuple[str, ...]) -> bool:
        return all(name in axioms and set(axioms[name]) <= STANDARD_AXIOMS for name in names)

    primary_ok = proved(PRIMARY_THEOREMS)
    lattice_ok = proved(LATTICE_THEOREMS)
    decoder_canonicity_ok = proved(("M0.parse_canonical", "M0.decode_canonical"))
    order_independence_ok = proved(ORDER_THEOREMS)
    magnitude_equivalence_ok = proved(MAGNITUDE_THEOREMS)
    axioms_ok = bool(axioms) and all(set(items) <= STANDARD_AXIOMS for items in axioms.values())
    findings.extend(
        (
            lean_finding("decoder-canonicity-proved", decoder_canonicity_ok,
                         "M1-A-S2-DECODER-CANONICITY"),
            lean_finding("class-fold-order-independence-proved", order_independence_ok,
                         "M1-A-S3-ORDER-INDEPENDENCE"),
            lean_finding("retained-encoding-and-lattice-theorems", primary_ok and lattice_ok,
                         "M1-A-RETAINED-THEOREMS"),
        )
    )

    # Stage 4: linear-list magnitude and an actually executed 2^20-octet natural.
    lean_boundary = report.get("natural_boundary", {})
    lean_boundary_ok = (
        lean_boundary.get("magnitude_octets") == (1 << 20) - 9
        and lean_boundary.get("encoded_octets") == 1 << 20
        and lean_boundary.get("reaches_bound") is True
        and lean_boundary.get("checked_encoder_accepts") is True
    )
    findings.extend(
        (
            lean_finding("linear-magnitude-equals-m0-reference", magnitude_equivalence_ok,
                         "M1-A-S4-LINEAR-MAGNITUDE-EQUIVALENT"),
            lean_finding("lean-natural-exact-byte-bound", lean_boundary_ok,
                         "M1-A-S4-LEAN-NATURAL-BOUNDARY"),
        )
    )

    # Stage 5: apply the K1 owner decision and freeze one positive/negative recipe pair.
    t0 = time.perf_counter()
    boundary_probe = _nat_boundary_probe(k1)
    timings["python_boundary_probe_seconds"] = round(time.perf_counter() - t0, 3)
    boundary_vectors = regenerated["k1-encoding-vectors.json"]["natural_byte_bound"]["vectors"]
    k1_boundary_ok = (
        [item["expected"]["outcome"] for item in boundary_vectors] == ["Completed", "Malformed"]
        and boundary_probe["nat_encode"] == "accepted: 1048576 octets"
        and boundary_probe["nat_decode_of_exact_bound_input"] == "accepted"
        and boundary_probe["nat_crossing_encode"].startswith("refused")
        and boundary_probe["int_encode"] == "accepted: 1048576 octets"
    )
    findings.extend(
        (
            _finding("m0-natural-byte-bound-resolved", "Affirmative",
                     "M1-A-S5-M0-NAT-BYTE-BOUND-RESOLVED") if k1_boundary_ok else
                _finding("m0-natural-byte-bound-resolved", "Refused",
                         "M1-R-S5-M0-NAT-BYTE-BOUND-DIVERGES"),
            _finding("k1-positive-negative-boundary-vectors", "Affirmative",
                     "M1-A-S5-K1-BOUNDARY-VECTORS") if k1_boundary_ok else
                _finding("k1-positive-negative-boundary-vectors", "Refused",
                         "M1-R-S5-K1-BOUNDARY-VECTORS"),
        )
    )

    # M2 Stage 1: exact portable-term carrier and relational typing text.
    term_text = (LEAN / "M0" / "Term.lean").read_text(encoding="utf-8")
    eval_text = (LEAN / "M0" / "Eval.lean").read_text(encoding="utf-8")
    term_constructors = (
        "| literal", "| variable", "| letE", "| recordConstruct", "| project",
        "| inject", "| caseE", "| sequenceConstruct", "| sequenceLength", "| fail",
        "| strictIndex", "| boundedAppend", "| primitiveCall", "| boundedIterate",
        "| conditional",
    )
    stage1_term_ok = all(constructor in term_text for constructor in term_constructors)
    stage1_typing_ok = (
        "inductive HasType" in term_text
        and "inductive TermsHaveType" in term_text
        and "inductive FieldsHaveType" in term_text
        and "inductive BranchesHaveType" in term_text
    )
    stage1_abis_ok = (
        "def declaredPrimitiveABIs" in term_text
        and all(name in term_text for name in (
            "sha2-256", "bytes.concat", "u64.to-be", "bytes.first-u64-be", "nat.lt",
            "nat.mod-positive", "bytes.take", "fixture.bytes.reverse",
            "fixture.bytes.prefix-27",
        ))
    )
    findings.extend(
        (
            lean_finding("m2-portable-term-carrier", stage1_term_ok,
                         "M2-A-S1-PORTABLE-TERM-CARRIER"),
            lean_finding("m2-relational-typing", stage1_typing_ok,
                         "M2-A-S1-RELATIONAL-TYPING"),
            lean_finding("m2-k1-primitive-abi-families", stage1_abis_ok,
                         "M2-A-S1-PRIMITIVE-ABI-FAMILIES"),
        )
    )
    m2_stage1_ok = all((stage1_term_ok, stage1_typing_ok, stage1_abis_ok))

    # M2 Stage 2: evaluator and exact evidence availability.
    outcome_names = (
        "unsupported", "missingDependency", "cannotAnswer", "kindMismatch",
        "malformed", "refused", "deterministicLimitExceeded", "checkerFailure",
    )
    stage2_definition_ok = (
        "def evalCore" in eval_text and "def evaluate" in eval_text
        and "structure Limits" in eval_text and "structure Charge" in eval_text
    )
    stage2_partition_ok = all(f"| {name}" in eval_text for name in outcome_names)
    oracle_inventory = regenerated_m2["oracle_inventory"]
    oracle_term_rows = oracle_inventory["term_evaluation_requests"]
    _require(
        oracle_term_rows == 0
        and oracle_inventory["operations"]
        == ["content_id", "decode", "encode", "prior_meta_id", "verify_id"],
        "the frozen K1 oracle inventory changed",
    )
    findings.extend(
        (
            lean_finding("m2-evaluator-definition", stage2_definition_ok,
                         "M2-A-S2-EVALUATOR-DEFINITION"),
            lean_finding("m2-noncompletion-partition", stage2_partition_ok,
                         "M2-A-S2-NONCOMPLETION-PARTITION"),
            _finding("m2-k1-term-evaluation-oracle-vectors", "CannotAnswer",
                     "M2-C-S2-K1-TERM-EVALUATION-ORACLE-ABSENT"),
            _finding("m2-noncompletion-byte-encoding", "CannotAnswer",
                     "M2-C-S2-NONCOMPLETION-BYTES-UNDEFINED"),
        )
    )
    m2_stage2_ok = stage2_definition_ok and stage2_partition_ok and oracle_term_rows > 0

    # M2 Stage 3: exact preimages, elaborated terms, and all finite inputs.
    m2_report = report.get("m2", {})
    m2_preimages_ok = all(m2_report.get(key) is True for key in (
        "check_preimage_decodes", "guard_preimage_decodes",
        "check_preimage_roundtrips", "guard_preimage_roundtrips",
    ))
    m2_elaboration_ok = all(m2_report.get(key) is True for key in (
        "check_term_elaborates_exactly", "guard_term_elaborates_exactly",
    ))
    m2_check_cases_ok = (
        m2_report.get("check_cases") == 81 and m2_report.get("check_cases_agree") is True
    )
    m2_guard_cases_ok = (
        m2_report.get("guard_cases") == 2 and m2_report.get("guard_cases_agree") is True
    )
    findings.extend(
        (
            lean_finding("m2-r1b-preimages-strictly-decoded", m2_preimages_ok,
                         "M2-A-S3-R1B-PREIMAGES-DECODED"),
            lean_finding("m2-r1b-terms-elaborate-exactly", m2_elaboration_ok,
                         "M2-A-S3-R1B-TERMS-ELABORATED"),
            lean_finding("m2-schnorr-check-81-inputs", m2_check_cases_ok,
                         "M2-A-S3-SCHNORR-81-INPUTS"),
            lean_finding("m2-guard-two-inputs", m2_guard_cases_ok,
                         "M2-A-S3-GUARD-TWO-INPUTS"),
        )
    )
    m2_stage3_ok = all((m2_preimages_ok, m2_elaboration_ok,
                        m2_check_cases_ok, m2_guard_cases_ok))

    # M2 Stages 4 and 5: proof closure and the closed finite equation.
    m2_determinism_ok = proved(("M0.evaluation_deterministic",))
    m2_monotonicity_ok = proved(("M0.evaluation_completed_mono",))
    m2_equation_ok = proved(("M0.schnorr_denotation_eq_closed_form",))
    m2_axioms_ok = proved(M2_THEOREMS)
    findings.extend(
        (
            lean_finding("m2-evaluation-deterministic", m2_determinism_ok,
                         "M2-A-S4-EVALUATION-DETERMINISTIC"),
            lean_finding("m2-completion-monotone-in-limits", m2_monotonicity_ok,
                         "M2-A-S4-COMPLETION-MONOTONE"),
            lean_finding("m2-theorems-standard-axioms-only", m2_axioms_ok,
                         "M2-A-S4-STANDARD-AXIOMS-ONLY"),
            lean_finding("m2-schnorr-term-denotation-defined",
                         "def schnorrDenotation" in eval_text,
                         "M2-A-S5-SCHNORR-DENOTATION"),
            lean_finding("m2-schnorr-closed-form-equation", m2_equation_ok,
                         "M2-A-S5-SCHNORR-CLOSED-FORM"),
        )
    )
    m2_stage4_ok = all((m2_determinism_ok, m2_monotonicity_ok, m2_axioms_ok))

    # M2 Stage 6: bounded cost and exact owner-text underdetermination.
    findings.append(
        _finding("m2-section-8-no-universal-result-bytes", "CannotAnswer",
                 "M2-C-S6-SECTION8-NO-UNIVERSAL-RESULT-BYTES")
    )

    # Report the full axiom closure; timings become the cost ledger.
    findings.append(lean_finding("axiom-closure-standard-only", axioms_ok,
                                 "M1-A-S6-STANDARD-AXIOMS-ONLY"))

    # Complete the Stage 6 cost ledger.
    timings["total_seconds"] = round(time.perf_counter() - started, 3)
    findings.append(_finding("cost-ledger-recorded", "Affirmative", "M1-A-S6-COST-LEDGER-RECORDED"))

    # Non-claims and the aggregate.
    findings.extend(
        (
            _finding("lean-definitions-not-normative", "CannotAnswer", "M0-C-NOT-NORMATIVE"),
            _finding("implementation-correspondence", "CannotAnswer", "M0-C-NO-IMPLEMENTATION-CORRESPONDENCE"),
            _finding("security-and-applicability", "CannotAnswer", "M0-C-NO-SECURITY-OR-APPLICABILITY-CLAIM"),
            _finding("general-k1-evaluator-conformance", "CannotAnswer",
                     "M2-C-NO-GENERAL-K1-EVALUATOR-CONFORMANCE"),
        )
    )
    if not lean_available:
        findings.append(_finding("mechanized-kernel-definitions", "CannotAnswer", "M0-C-LEAN-TOOLCHAIN-UNAVAILABLE"))
    elif all((retained_ok, stage1_ok, decoder_canonicity_ok, order_independence_ok,
              magnitude_equivalence_ok, lean_boundary_ok, k1_boundary_ok,
              primary_ok, lattice_ok, axioms_ok, m2_stage1_ok, m2_stage2_ok,
              m2_stage3_ok, m2_stage4_ok, m2_equation_ok)):
        findings.append(_finding("mechanized-kernel-definitions", "Affirmative",
                                 AFFIRMATIVE_AGGREGATE))
    else:
        findings.append(_finding("mechanized-kernel-definitions", "CannotAnswer",
                                 CANNOT_ANSWER_AGGREGATE))

    payload = [finding.value() for finding in findings]
    checksum = hashlib.sha256(
        json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()
    metrics.update(
        {
            "findings": len(findings),
            "findings_sha256": checksum,
            "timings": timings,
            "vectors": {
                "encode_by_source": {source: len(rows) for source, rows in sorted(by_source.items())},
                "reject_oracle": len(oracle_rejects),
                "reject_crafted": len(crafted_rejects),
                "carriers": len(carriers),
                "skipped_oracle_cases": [
                    item["case"] for item in regenerated["k1-encoding-vectors.json"]["skipped"]
                ],
            },
            "pcgraph": {
                row["carrier"]: {
                    key: row[key]
                    for key in (
                        "node_count", "edge_count", "nodes_match", "edges_match", "order_matches",
                        "classes_match", "sinks_match", "acceptance_sinks_match",
                        "private_predecessors_match", "logical_cones_match",
                        "logical_intersections_match", "terminal_preemption_edges",
                        "oracle_query_answer_edges", "module_edges", "challenge_count",
                        "challenge_readings_agree",
                    )
                }
                for row in carriers
            },
            "challenge_readings_agree_on_all_carriers": readings_agree,
            "axioms": axioms,
            "lean_version": report.get("lean_version"),
            "nat_byte_bound_probe": boundary_probe,
            "m2": {
                "stage_1_passed": m2_stage1_ok,
                "stage_2_passed": m2_stage2_ok,
                "stage_3_passed": m2_stage3_ok,
                "stage_4_passed": m2_stage4_ok,
                "k1_term_evaluation_oracle_vectors": oracle_term_rows,
                "lean_report": m2_report,
            },
        }
    )
    return findings, metrics


def _load_expected() -> dict[str, Any]:
    try:
        value = json.loads(EXPECTED.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise GateFailure("cannot load frozen findings") from error
    _require(type(value) is dict, "expected findings root differs")
    return value


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--artifacts", type=Path, help="directory for logs and the Lean input/report")
    args = parser.parse_args()
    artifacts = args.artifacts or (
        Path(os.environ["ZKC_CHECK_ARTIFACTS"]) if os.environ.get("ZKC_CHECK_ARTIFACTS") else None
    )
    if artifacts is None:
        artifacts = Path(tempfile.mkdtemp(prefix="zkc-m0-"))
    artifacts.mkdir(parents=True, exist_ok=True)
    findings, metrics = evaluate(artifacts)
    observed = {
        "aggregate": next(f.code for f in findings if f.name == "mechanized-kernel-definitions"),
        "findings_sha256": metrics["findings_sha256"],
        "finding_codes": [finding.value() for finding in findings],
    }
    if args.check and observed != _load_expected():
        unsupported = [f.name for f in findings if f.outcome == UNSUPPORTED_OUTCOME]
        if unsupported:
            print(
                f"Lean toolchain unavailable ({metrics['toolchain']['reason']}); "
                f"{len(unsupported)} Lean-dependent findings are Unsupported/{UNSUPPORTED_CODE}",
                file=sys.stderr,
            )
        print(
            json.dumps(
                {"expected": _load_expected(), "observed": observed},
                indent=2,
                sort_keys=True,
            )
        )
        return 1
    counts: dict[str, int] = {}
    for finding in findings:
        counts[finding.outcome] = counts.get(finding.outcome, 0) + 1
    output: dict[str, Any] = {
        "aggregate": observed["aggregate"],
        "outcomes": dict(sorted(counts.items())),
        "metrics": metrics,
        "artifacts": str(artifacts),
    }
    if args.json:
        output["finding_codes"] = observed["finding_codes"]
    print(json.dumps(output, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
