"""Deterministic public validation report for the finite FRI/IOR package."""

from __future__ import annotations

import ast
import importlib.util
import json
from pathlib import Path
import sys
from typing import Any

from .analysis import (
    canonical_property_questions,
    canonical_theorem_questions,
    check_question_formation,
)
from .classical_fixtures import parse_classical_replay_policy
from .committed import verify_committed_fri
from .fixtures import (
    PACKAGE_ROOT,
    _read_regular_file,
    bind_repository_root,
    load_fixture,
    parse_negative_proofs,
    parse_public_inputs,
    parse_public_native_vector,
    parse_public_proof,
    parse_replay_policy,
)
from .native import verify_native_trace
from .provenance import (
    artifact_content_id,
    canonical_json_content_id,
    load_source_ledger_bytes,
    validation_basis_id,
)
from .terms import CheckResult, ModelFailure, OutcomeClass, ResourceCounter


REPORT_SCHEMA = "zkc.native-fri-ior.public-validation-report.v3"
EXPECTED_SCHEMA = "zkc.native-fri-ior.expected-report-projection.v3"
PUBLIC_CASES = {
    "public_inputs": "evaluation/native-fri-ior/cases/public-inputs.json",
    "public_proof": "evaluation/native-fri-ior/cases/public-proof.json",
    "public_native_vector": "evaluation/native-fri-ior/cases/public-native-vector.json",
    "negative_proofs": "evaluation/native-fri-ior/cases/public-negative-proofs.json",
    "replay_policy": "evaluation/native-fri-ior/cases/replay-policy.json",
    "exact_classical_public_inputs": (
        "evaluation/native-fri-ior/cases/exact-classical-public-inputs.json"
    ),
    "exact_classical_public_proof": (
        "evaluation/native-fri-ior/cases/exact-classical-public-proof.json"
    ),
    "exact_classical_replay_policy": (
        "evaluation/native-fri-ior/cases/exact-classical-replay-policy.json"
    ),
    "source_ledger": "evaluation/native-fri-ior/cases/source-ledger.json",
}

SOURCE_BASES = {
    # These are entry points, not hand-maintained closures.  _source_closure
    # follows every static local import and includes package initialization.
    "native": ("fixtures.py", "native.py"),
    "committed": ("fixtures.py", "committed.py"),
    "analysis-formation": ("analysis.py",),
    "independent-replay": ("../independent.py",),
    "exact-classical-independent-replay": ("../classical_independent.py",),
    # Both reconstruction modules are loaded dynamically, so they are explicit
    # report roots rather than invisible runtime dependencies.
    "report": (
        "report.py",
        "../independent.py",
        "../classical_independent.py",
        "../run.py",
    ),
}

NONCLAIMS = (
    "no FRI proximity theorem is established",
    "no commitment binding, hiding, or compiler-correctness theorem is established",
    "no Fiat-Shamir security, knowledge, or outer-relation theorem is established",
    "the public native vector is declassified validation material, not a committed-verifier input",
    "the source ledger records declared exact-byte identities and metadata but is not externally authenticated by this report",
    "fixture replay assumes a non-hostile local filesystem and is not a sandbox boundary",
    "owner-local construction receipts are checked separately and are not public-report inputs",
    "validation source bases bind selected local Python bytes, not the interpreter, standard library, or complete runtime environment",
    "one positive execution and two refusals do not establish protocol-family coverage or refusal completeness",
    "the exact classical replay establishes one finite structural execution, not source-theorem applicability or probabilistic FRI correspondence",
)

EXPECTED_POSITIVE_CODES = {
    "native": "FRI-IOR-NATIVE-100",
    "committed": "FRI-IOR-COMMITTED-100",
    "independent_replay": "FRI-IOR-INDEPENDENT-100",
}
EXPECTED_EXACT_CLASSICAL_CODE = "FRI-IOR-CLASSICAL-INDEPENDENT-100"
EXPECTED_NEGATIVE_CODES = {
    "authenticated-fold-inconsistency": "FRI-IOR-COMMITTED-020",
    "fold-consistent-terminal-degree-excess": "FRI-IOR-COMMITTED-022",
}
EXPECTED_ANALYSIS_QUESTION_NAMES = (
    "property:AdaptiveClassicalRomKnowledgeSoundness",
    "property:AdaptiveClassicalRomSoundness",
    "property:AdaptiveQromSoundness",
    "property:CommittedInteractiveSoundness",
    "property:GeneralizedSpecialSoundness",
    "property:GrindingAdjustedCommittedSoundness",
    "property:HonestVerifierZeroKnowledge",
    "property:MaliciousVerifierZeroKnowledge",
    "property:NativeIoppCompleteness",
    "property:NativeIoppProximitySoundness",
    "property:RestrictedRestorationSoundness",
    "property:RoundByRoundVectorSoundness",
    "property:UnrestrictedRestorationSoundness",
    "theorem:bcs-restricted-restoration-to-classical-rom",
    "theorem:commitment-compilation-preservation",
    "theorem:direct-fri-classical-rom",
    "theorem:direct-fri-round-by-round",
    "theorem:fri-qrom-asymptotic",
    "theorem:grinding-over-vector-errors",
    "theorem:multi-round-fs-knowledge",
    "theorem:original-fri-native-proximity",
    "theorem:round-by-round-to-restricted-restoration",
    "theorem:round-by-round-to-unrestricted-restoration",
)


def canonical_pretty_json(value: Any) -> bytes:
    return (
        json.dumps(value, ensure_ascii=True, allow_nan=False, sort_keys=True, indent=2)
        + "\n"
    ).encode("ascii")


def _source_path(relative: str) -> str:
    if relative.startswith("../"):
        return f"evaluation/native-fri-ior/{relative.removeprefix('../')}"
    return f"evaluation/native-fri-ior/friiormodel/{relative}"


def _package_module(module: str) -> str | None:
    parts = module.split(".")
    if not parts or parts[0] != "friiormodel":
        return None
    if len(parts) == 1:
        return "__init__.py"
    if len(parts) == 2:
        return f"{parts[1]}.py"
    raise RuntimeError(
        f"nested local module is outside the source-basis model: {module}"
    )


def _local_imports(relative: str, raw: bytes) -> set[str]:
    """Return direct local Python dependencies of one validation source."""

    try:
        tree = ast.parse(raw.decode("utf-8"), filename=relative)
    except (SyntaxError, UnicodeDecodeError) as error:
        raise RuntimeError(f"validation source cannot be parsed: {relative}") from error
    discovered: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom):
            if node.level:
                if relative.startswith("../"):
                    continue
                if node.level != 1:
                    raise RuntimeError(
                        f"unsupported relative import in validation source: {relative}"
                    )
                if node.module is None:
                    discovered.update(
                        f"{alias.name}.py" for alias in node.names if alias.name != "*"
                    )
                else:
                    discovered.add(f"{node.module}.py")
                discovered.add("__init__.py")
                continue
            if node.module is not None:
                local = _package_module(node.module)
                if local is not None:
                    discovered.update(("__init__.py", local))
        elif isinstance(node, ast.Import):
            for alias in node.names:
                local = _package_module(alias.name)
                if local is not None:
                    discovered.update(("__init__.py", local))
    return discovered


def _source_closure(root: Path, roots: tuple[str, ...]) -> tuple[str, ...]:
    """Compute the exact static local-import closure of selected entry points."""

    pending = set(roots)
    if any(not item.startswith("../") for item in roots):
        pending.add("__init__.py")
    closed: set[str] = set()
    while pending:
        relative = min(pending, key=lambda item: item.encode("utf-8"))
        pending.remove(relative)
        if relative in closed:
            continue
        _, raw = _read_regular_file(root, _source_path(relative), 1 << 20)
        closed.add(relative)
        pending.update(_local_imports(relative, raw) - closed)
    return tuple(sorted(closed, key=lambda item: item.encode("utf-8")))


def _source_basis(root: Path, component: str, roots: tuple[str, ...]) -> str:
    manifest = []
    for relative in _source_closure(root, roots):
        path = _source_path(relative)
        _, raw = _read_regular_file(root, path, 1 << 20)
        manifest.append(
            {
                "path": path,
                "artifact_content_id": str(artifact_content_id(raw)),
                "byte_length": len(raw),
            }
        )
    return str(
        validation_basis_id(
            component,
            {
                "schema": "zkc.native-fri-ior.validation-source-basis.v1",
                "component": component,
                "sources": manifest,
            },
        )
    )


def _load_independent() -> Any:
    path = PACKAGE_ROOT / "independent.py"
    spec = importlib.util.spec_from_file_location("fri_ior_independent_replay", path)
    if spec is None or spec.loader is None:
        raise RuntimeError("independent replay module is unavailable")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _load_classical_independent() -> Any:
    path = PACKAGE_ROOT / "classical_independent.py"
    spec = importlib.util.spec_from_file_location(
        "fri_ior_exact_classical_independent_replay",
        path,
    )
    if spec is None or spec.loader is None:
        raise RuntimeError("exact classical independent replay module is unavailable")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def _case(
    name: str, result: CheckResult, resources: ResourceCounter | None = None
) -> dict[str, Any]:
    term = result.to_term()
    return {
        "name": name,
        "result": term,
        "resource_snapshot": None if resources is None else resources.snapshot(),
    }


def _fixture_term(fixture: Any) -> dict[str, Any]:
    return {
        "role": fixture.role,
        "path": fixture.relative_path,
        "artifact_content_id": str(fixture.artifact_id),
        "canonical_content_id": str(fixture.canonical_id),
        "byte_length": len(fixture.raw),
    }


def _build_public_report_from_loaded(
    root: Path, loaded: dict[str, Any]
) -> dict[str, Any]:
    """Build from one complete, explicitly supplied public-fixture set."""

    root = bind_repository_root(root)
    if set(loaded) != set(PUBLIC_CASES):
        raise RuntimeError("public report requires the exact public-fixture role set")
    inputs = parse_public_inputs(loaded["public_inputs"].value)
    proof = parse_public_proof(loaded["public_proof"].value)
    trace = parse_public_native_vector(loaded["public_native_vector"].value)
    negatives = parse_negative_proofs(loaded["negative_proofs"].value)
    limits = parse_replay_policy(loaded["replay_policy"].value)
    exact_classical_limits = parse_classical_replay_policy(
        loaded["exact_classical_replay_policy"].value
    )
    ledger = load_source_ledger_bytes(loaded["source_ledger"].raw)

    native_resources = ResourceCounter(limits)
    native_result = verify_native_trace(trace, native_resources)
    committed_resources = ResourceCounter(limits)
    committed_result = verify_committed_fri(inputs, proof, committed_resources)

    analysis_results = []
    for name, question in sorted(
        {
            **{
                f"property:{key.value}": value
                for key, value in canonical_property_questions().items()
            },
            **{
                f"theorem:{key}": value
                for key, value in canonical_theorem_questions().items()
            },
        }.items()
    ):
        result = check_question_formation(question)
        analysis_results.append({"name": name, "result": result.to_term()})

    # The reconstruction lane receives the frozen JSON terms directly.  It
    # must not depend on producer-side carrier formation or normalization,
    # even though those parsers separately require an exact round trip.
    independent = _load_independent().verify_public_fri(
        loaded["public_inputs"].value,
        loaded["public_proof"].value,
        limits=loaded["replay_policy"].value["limits"],
    )
    # This is the public verification path for the exact classical packet.
    # It receives the frozen JSON terms directly and does not call the
    # producer-side carrier constructors or verifiers.
    exact_classical_independent = (
        _load_classical_independent().verify_public_classical_fri(
            loaded["exact_classical_public_inputs"].value,
            loaded["exact_classical_public_proof"].value,
            limits=exact_classical_limits.to_term(),
        )
    )
    negative_cases = []
    for name, negative in negatives.items():
        resources = ResourceCounter(limits)
        negative_cases.append(
            _case(name, verify_committed_fri(inputs, negative, resources), resources)
        )

    producer_facts = {
        "outcome": committed_result.outcome.value,
        "beta0": committed_result.evidence.get("beta0"),
        "beta1": committed_result.evidence.get("beta1"),
        "ordered_initial_domain_indices": committed_result.evidence.get(
            "ordered_initial_domain_indices"
        ),
        "proof_bytes": committed_result.evidence.get("proof_bytes"),
        "resource_snapshot": committed_resources.snapshot(),
    }
    independent_facts = {
        "outcome": independent["outcome"],
        "beta0": independent.get("evidence", {}).get("beta0"),
        "beta1": independent.get("evidence", {}).get("beta1"),
        "ordered_initial_domain_indices": independent.get("evidence", {}).get(
            "ordered_initial_domain_indices"
        ),
        "proof_bytes": independent.get("evidence", {}).get("proof_bytes"),
        "resource_snapshot": independent.get("evidence", {}).get("resource_usage"),
    }
    reconciliation = {
        "scope": "exact-positive-public-execution-facts-only",
        "producer": producer_facts,
        "independent": independent_facts,
        "equal": producer_facts == independent_facts,
        "establishes_general_checker_correspondence": False,
    }

    bases = {
        component: _source_basis(root, component, files)
        for component, files in SOURCE_BASES.items()
    }
    body = {
        "schema": REPORT_SCHEMA,
        "fixture_inputs": [_fixture_term(loaded[name]) for name in sorted(loaded)],
        "source_ledger": {
            "artifact_content_id": str(ledger.artifact_id),
            "canonical_content_id": str(ledger.canonical_id),
            "binding_status": "self-identified-current-bytes-not-externally-anchored",
        },
        "validation_source_basis_ids": bases,
        "positive_execution": {
            "native": _case("native-execution", native_result, native_resources),
            "committed": _case(
                "committed-public-verification", committed_result, committed_resources
            ),
            "independent_replay": independent,
            "reconciliation": reconciliation,
        },
        "exact_classical_execution": {
            "scope": "one-frozen-three-fold-scalar-terminal-strong-fs-public-replay",
            "independent_replay": exact_classical_independent,
            "verification_authority": (
                "separately-coded-public-verifier-over-frozen-public-terms"
            ),
            "uses_owner_generation_input": False,
            "establishes_source_theorem_correspondence": False,
        },
        "negative_executions": negative_cases,
        "analysis_question_formation": analysis_results,
        "nonclaims": list(NONCLAIMS),
    }
    report_id = str(canonical_json_content_id(body))
    return {"report_content_id": report_id, "report": body}


def build_public_report(root: Path) -> dict[str, Any]:
    """Build from public validation inputs only; counters are never caller supplied."""

    root = bind_repository_root(root)
    loaded = {
        name: load_fixture(root, relative, name)
        for name, relative in PUBLIC_CASES.items()
    }
    return _build_public_report_from_loaded(root, loaded)


def expected_projection(report: dict[str, Any]) -> dict[str, Any]:
    body = report["report"]
    return {
        "report_content_id": report["report_content_id"],
        "fixture_ids": {
            item["role"]: item["artifact_content_id"] for item in body["fixture_inputs"]
        },
        "validation_source_basis_ids": body["validation_source_basis_ids"],
        "positive_outcomes": {
            "native": body["positive_execution"]["native"]["result"]["code"],
            "committed": body["positive_execution"]["committed"]["result"]["code"],
            "independent_replay": body["positive_execution"]["independent_replay"][
                "code"
            ],
            "reconciliation_equal": body["positive_execution"]["reconciliation"][
                "equal"
            ],
            "exact_classical_independent_replay": body[
                "exact_classical_execution"
            ]["independent_replay"]["code"],
        },
        "negative_outcomes": {
            item["name"]: item["result"]["code"] for item in body["negative_executions"]
        },
        "analysis_question_count": len(body["analysis_question_formation"]),
    }


def _report_policy_valid(report: object) -> bool:
    """Retype one report candidate without consulting fixture storage."""

    if type(report) is not dict or set(report) != {"report_content_id", "report"}:
        return False
    body = report["report"]
    if type(body) is not dict or body.get("schema") != REPORT_SCHEMA:
        return False
    try:
        candidate_content_id = str(canonical_json_content_id(body))
    except (ModelFailure, UnicodeError, ValueError):
        return False
    if report["report_content_id"] != candidate_content_id:
        return False
    positive = body.get("positive_execution", {})
    if type(positive) is not dict:
        return False
    native_case = positive.get("native")
    committed_case = positive.get("committed")
    independent_case = positive.get("independent_replay")
    reconciliation = positive.get("reconciliation")
    exact_classical = body.get("exact_classical_execution")
    if not all(
        type(value) is dict
        for value in (
            native_case,
            committed_case,
            independent_case,
            reconciliation,
        )
    ):
        return False
    if type(exact_classical) is not dict:
        return False
    exact_classical_replay = exact_classical.get("independent_replay")
    if type(exact_classical_replay) is not dict:
        return False
    native_result = native_case.get("result")
    committed_result = committed_case.get("result")
    if type(native_result) is not dict or type(committed_result) is not dict:
        return False
    observed_positive = {
        "native": native_result.get("code"),
        "committed": committed_result.get("code"),
    }
    observed_positive["independent_replay"] = independent_case.get("code")
    positive_types_valid = all(
        result.get("outcome") == OutcomeClass.AFFIRMATIVE.value
        for result in (native_result, committed_result)
    ) and independent_case.get("outcome") == OutcomeClass.AFFIRMATIVE.value
    negative = body.get("negative_executions", ())
    if type(negative) is not list or not all(type(item) is dict for item in negative):
        return False
    negative_results = [item.get("result") for item in negative]
    if not all(type(result) is dict for result in negative_results):
        return False
    negative_names = [item.get("name") for item in negative]
    if not all(type(name) is str for name in negative_names):
        return False
    observed_negative = {
        name: result.get("code")
        for name, result in zip(negative_names, negative_results, strict=True)
    }
    negative_types_valid = all(
        result.get("outcome") == OutcomeClass.REFUSED.value
        for result in negative_results
    )
    analysis = body.get("analysis_question_formation", ())
    if type(analysis) is not list or not all(type(item) is dict for item in analysis):
        return False
    analysis_results = [item.get("result") for item in analysis]
    if not all(type(result) is dict for result in analysis_results):
        return False
    analysis_names = tuple(item.get("name") for item in analysis)
    analysis_formed = all(
        result.get("outcome") == OutcomeClass.AFFIRMATIVE.value
        and result.get("code") == "FRI-IOR-ANALYSIS-101"
        for result in analysis_results
    )
    policy_valid = (
        observed_positive == EXPECTED_POSITIVE_CODES
        and positive_types_valid
        and observed_negative == EXPECTED_NEGATIVE_CODES
        and negative_types_valid
        and analysis_names == EXPECTED_ANALYSIS_QUESTION_NAMES
        and analysis_formed
        and reconciliation.get("equal") is True
        and exact_classical_replay.get("outcome")
        == OutcomeClass.AFFIRMATIVE.value
        and exact_classical_replay.get("code") == EXPECTED_EXACT_CLASSICAL_CODE
        and exact_classical.get("verification_authority")
        == "separately-coded-public-verifier-over-frozen-public-terms"
        and exact_classical.get("uses_owner_generation_input") is False
        and exact_classical.get("establishes_source_theorem_correspondence") is False
    )
    return policy_valid


def _verify_public_report_from_loaded(
    root: Path, report: object, loaded: dict[str, Any]
) -> bool:
    """Retype and rebuild a report from one explicit public-fixture set."""

    return _report_policy_valid(report) and _build_public_report_from_loaded(
        root, loaded
    ) == report


def verify_public_report(root: Path, report: object) -> bool:
    """Retype and rebuild a report from the checkout-bound public inputs."""

    return _report_policy_valid(report) and build_public_report(root) == report


__all__ = [
    "EXPECTED_SCHEMA",
    "REPORT_SCHEMA",
    "build_public_report",
    "canonical_pretty_json",
    "expected_projection",
    "verify_public_report",
]
