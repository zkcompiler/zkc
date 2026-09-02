#!/usr/bin/env python3
"""Run the F0-V2B2D2 Fresh completed-record schema gate."""

from __future__ import annotations

import argparse
import copy
from dataclasses import dataclass
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from types import ModuleType
from typing import Any, Callable


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
MODEL = HERE / "model.py"
INDEPENDENT = HERE / "independent.py"
EXPECTED = HERE / "expected-findings.json"
D1_EXPECTED = (
    ROOT
    / "evaluation/formal-source-integrated-graph-f0v2b2d1"
    / "expected-findings.json"
)
INVENTORY = ROOT / "evaluation/formal-source-constructor-closure-f0v2b2a/inventory.json"
TARGET = ROOT / "docs-next/pir/interactive-core.md"
FOUNDATION_TARGET = ROOT / "docs-next/foundation/executable-foundations.md"
F2O0_NOTE = (
    ROOT
    / "docs-next/notes/semantic-revalidation-and-redesign/formal-assurance-research"
    / "f2o0-provider-observable-audit.md"
)

AGGREGATE = "F0V2B2D2-A-FRESH-RUN-SCHEMA"
PROFILE_DIGEST = "76cf68774060fbe667ce5f1a7d0b67de525449d8fad92b262c7fd4adfd9b6b79"
PROFILE_BODY_SHA256 = "4272f9bb8285a84481da961c29cdc058aa7e4ce2411c7f73582a0149933d554d"
SCHEMA_GRAMMAR_SHA256 = "af8c25ffcaf7967e2b9985699f8374bf5f16f55a91c18ce4253702598de582a3"
SCHEMA_SOURCE_SHA256 = "f35c4517d6aa0482cb93e320ff54ad11cdb69c36b65e7fc52ae540e11adb419f"


class GateFailure(RuntimeError):
    """The D2 package detected drift, disagreement, or an accepted mutation."""


@dataclass(frozen=True)
class Finding:
    name: str
    outcome: str
    code: str

    def value(self) -> list[str]:
        return [self.name, self.outcome, self.code]


def _load(name: str, path: Path) -> ModuleType:
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


def _expect(result: object, outcome: str, code: str, label: str) -> None:
    _require(
        result.outcome == outcome and result.code == code,
        f"{label}: expected {outcome}/{code}, got {result.outcome}/{result.code}",
    )


def _rejects(operation: Callable[[], object], expected: object) -> bool:
    try:
        operation()
    except expected:  # type: ignore[misc]
        return True
    return False


def _algorithm_preimages(model: ModuleType, fixture: object) -> tuple[Any, ...]:
    return tuple(
        sorted(
            (
                item.identity.internal_reference(),
                model.k1.algorithm_preimage(item),
            )
            for item in fixture.algorithms
        )
    )


def _cold_project(
    model: ModuleType,
    independent: ModuleType,
    fixture: object,
) -> tuple[dict[int, Any], dict[str, Any]]:
    return independent.project(
        fixture.candidate.profiled_body,
        fixture.candidate.asserted_id.internal_reference(),
        fixture.protocol_candidate.profiled_body,
        fixture.protocol_candidate.asserted_id.internal_reference(),
        model.d1.raw_module_sources(fixture.environment),
        _algorithm_preimages(model, fixture),
        model.k1.DEFAULT_EVALUATION_CONTRACT.identity.internal_reference(),
    )


def _mutations(model: ModuleType, baseline: dict[int, Any]) -> dict[str, Any]:
    result: dict[str, Any] = {}

    changed = copy.deepcopy(baseline)
    changed[6][2][0] = copy.deepcopy(changed[6][2][1])
    result["receipt-branch"] = changed

    changed = copy.deepcopy(baseline)
    changed[6][1][0][1] = copy.deepcopy(changed[6][1][1][1])
    result["receipt-coordinate"] = changed

    changed = copy.deepcopy(baseline)
    changed[6][2][1]["value"][3] = model.foundation._v(1)
    result["receipt-visibility"] = changed

    changed = copy.deepcopy(baseline)
    changed[6][0][0][1] = []
    result["receipt-arity"] = changed

    changed = copy.deepcopy(baseline)
    changed[6][1][0][3] = copy.deepcopy(changed[6][0][17][1][0])
    result["receipt-type"] = changed

    changed = copy.deepcopy(baseline)
    changed[6][3][0][0] = copy.deepcopy(changed[6][3][1][0])
    result["terminal-reference"] = changed

    changed = copy.deepcopy(baseline)
    changed[6][4][0]["value"][0][1] = copy.deepcopy(
        changed[6][4][0]["value"][1][1]
    )
    result["stopping-terminal"] = changed

    changed = copy.deepcopy(baseline)
    changed[6][4][0]["value"][0][4].append(
        copy.deepcopy(changed[6][4][0]["value"][1][1])
    )
    result["inactive-occurrence-receipt"] = changed

    changed = copy.deepcopy(baseline)
    changed[6][2][6]["value"][5] = model.foundation._v(2)
    result["fixation-marker"] = changed

    changed = copy.deepcopy(baseline)
    changed[6][2][3]["value"][2] = model.foundation._v(0)
    result["public-binding-upgrade"] = changed
    return result


def evaluate() -> tuple[list[Finding], dict[str, Any]]:
    model = _load("_zkc_f0v2b2d2_model", MODEL)
    independent = _load("_zkc_f0v2b2d2_independent", INDEPENDENT)
    findings: list[Finding] = []

    predecessor = json.loads(D1_EXPECTED.read_text(encoding="utf-8"))
    _require(
        predecessor["aggregate"] == "F0V2B2D1-A-INTEGRATED-PCGRAPH-CLOSURE"
        and predecessor["findings_sha256"]
        == "6df7aa212836ddd9f4eb4f740167b9183a8e155c853cd3ee7e801f832e75e48a",
        "D1 predecessor result drifted",
    )
    findings.append(
        _finding("d1-predecessor-pin", "Affirmative", "F0V2B2D2-A-D1-PIN")
    )

    inventory = json.loads(INVENTORY.read_text(encoding="utf-8"))
    family = [
        item
        for item in inventory["required_pressure_families"]
        if item["id"] == "fresh-runtime-oracle-receipts"
    ]
    _require(
        family
        == [
            {
                "id": "fresh-runtime-oracle-receipts",
                "owner": "pir.protocol",
                "views": ["ExecutionView"],
                "positive_carrier": "Fresh completed-record schema with every Oracle receipt branch and exact output arity",
                "negative_discriminator": "receipt branch, coordinate, visibility, arity, type, or terminal schema drift refuses",
                "stage": "B2D",
            }
        ],
        "B2D D2 pressure-family row drifted",
    )
    findings.append(
        _finding("b2d-family-pin", "Affirmative", "F0V2B2D2-A-FAMILY-PIN")
    )

    target_lines = TARGET.read_text(encoding="utf-8").splitlines()
    required_lines = {
        1091: "typed fixation marker",
        1092: "domain_law",
        1704: "first active terminal",
        1758: "OracleReceipt =",
        1767: "RunRecord(P) = {",
        1777: "PartialRunRecord(P) = the exact prefix",
        1791: "CompletedProtocolRecord(P) =",
        1814: "PartialRunRecord(P)` is diagnostic execution data",
        2128: "run_record_schema",
    }
    _require(
        all(text in target_lines[line - 1] for line, text in required_lines.items()),
        "target receipt/outcome source lines drifted",
    )
    foundation_lines = FOUNDATION_TARGET.read_text(encoding="utf-8").splitlines()
    _require(
        (
            "operational-outcome-partition=Unsupported,MissingDependency,"
            "CannotAnswer,KindMismatch,Malformed,Refused,"
            "DeterministicLimitExceeded,and-CheckerFailure-are-pairwise-distinct"
        )
        in foundation_lines[2257],
        "Foundation operational-outcome partition drifted",
    )
    f2o0 = F2O0_NOTE.read_text(encoding="utf-8").splitlines()
    _require(
        "The outcome-partition map has no owner" in f2o0[144]
        and "D2 should define the run" in f2o0[149],
        "F2-O0 D2 handoff drifted",
    )
    findings.extend(
        (
            _finding("target-law-pin", "Affirmative", "F0V2B2D2-A-TARGET-PIN"),
            _finding("f2o0-outcome-handoff", "Affirmative", "F0V2B2D2-A-F2O0-PIN"),
        )
    )

    model_source = MODEL.read_text(encoding="utf-8")
    independent_source = INDEPENDENT.read_text(encoding="utf-8")
    _require(
        "def project_execution(" in model_source
        and "def project(" in independent_source
        and "model.py" not in independent_source
        and "import model" not in independent_source
        and "from model" not in independent_source,
        "typed and cold D2 sources are not separated",
    )
    _require(
        model.d1 is not independent.d1
        and model.b2b is not independent.b2b
        and model.codec is not independent.codec,
        "cold path reused typed-owner module instances",
    )
    findings.extend(
        (
            _finding("projection-source-separation", "Affirmative", "F0V2B2D2-A-SOURCE-SEPARATION"),
            _finding("cold-module-separation", "Affirmative", "F0V2B2D2-A-COLD-MODULES"),
        )
    )

    typed_schema = model.schema_evidence()
    cold_schema = independent.configure(PROFILE_DIGEST, PROFILE_BODY_SHA256)
    _require(
        model.source_profile() == PROFILE_DIGEST
        and typed_schema["schema_grammar_sha256"] == SCHEMA_GRAMMAR_SHA256
        and typed_schema["schema_source_sha256"] == SCHEMA_SOURCE_SHA256
        and cold_schema["schema_grammar_sha256"] == SCHEMA_GRAMMAR_SHA256
        and cold_schema["schema_source_sha256"] == SCHEMA_SOURCE_SHA256,
        "D2 candidate profile or schema identity drifted",
    )
    _require(
        model.VIEW_SCHEMAS == independent.VIEW_SCHEMAS
        and typed_schema["definition_count"] == 101
        and typed_schema["source_node_count"] == 503
        and cold_schema["source_node_count"] == 503,
        "recursive and iterative D2 schema compilers disagree",
    )
    findings.extend(
        (
            _finding("profile-and-schema-pin", "Affirmative", "F0V2B2D2-A-SCHEMA-PIN"),
            _finding("dual-schema-compilation", "Affirmative", "F0V2B2D2-A-SCHEMA-AGREEMENT"),
        )
    )

    owner_values: dict[str, dict[int, Any]] = {}
    owner_bodies: dict[str, bytes] = {}
    protocol_handles: dict[str, object] = {}
    metrics_by_carrier: dict[str, Any] = {}
    evidence_keys = (
        "core_domain_sha256",
        "body_bytes",
        "occurrence_receipts",
        "challenge_receipts",
        "oracle_receipts",
        "oracle_branches",
        "terminal_alternatives",
        "strategy_stop_alternatives",
        "interpretation_failure_none",
        "operational_noncompletion_classes",
        "operational_noncompletion_names",
        "run_executions",
        "replay_executions",
    )
    for name, fixture in model.d1.fixtures().items():
        core_result = model.d1.admit_core(fixture.candidate, fixture.environment)
        _expect(
            core_result,
            "Affirmative",
            "F0V2B2D1-A-CORE-ADMITTED",
            f"{name} Core",
        )
        _require(core_result.handle is not None, f"{name} omitted Core authority")
        protocol_result = model.d1.admit_fresh_protocol(
            core_result.handle, fixture.protocol_candidate, fixture.environment
        )
        _expect(
            protocol_result,
            "Affirmative",
            "F0V2B2D1-A-FRESH-ADMITTED",
            f"{name} Fresh Protocol",
        )
        _require(
            protocol_result.handle is not None, f"{name} omitted Protocol authority"
        )
        owner_value, owner_evidence = model.project_execution(protocol_result.handle)
        cold_value, cold_evidence = _cold_project(model, independent, fixture)
        owner_body = model.execution_body(protocol_result.handle)
        cold_body = independent.encode_execution(cold_value)
        _require(owner_value == cold_value, f"{name} owner/cold values disagree")
        _require(owner_body == cold_body, f"{name} owner/cold bytes disagree")
        _require(
            {key: owner_evidence[key] for key in evidence_keys}
            == {key: cold_evidence[key] for key in evidence_keys},
            f"{name} owner/cold schema metrics disagree",
        )
        _require(
            owner_body == model.execution_body(protocol_result.handle),
            f"{name} typed reprojection is nondeterministic",
        )
        decoded = model.k1.decode_datum(owner_body)
        _require(
            model.k1.encode_datum(decoded) == owner_body,
            f"{name} candidate ExecutionView does not round-trip",
        )
        expected_metrics = {
            "occurrence_receipts": 23,
            "challenge_receipts": 3,
            "oracle_receipts": 9,
            "oracle_branches": (0, 1, 2, 0, 1, 2, 0, 1, 2),
            "terminal_alternatives": 3,
            "strategy_stop_alternatives": 4,
            "interpretation_failure_none": True,
            "operational_noncompletion_classes": 8,
            "operational_noncompletion_names": (
                "Unsupported",
                "MissingDependency",
                "CannotAnswer",
                "KindMismatch",
                "Malformed",
                "Refused",
                "DeterministicLimitExceeded",
                "CheckerFailure",
            ),
            "run_executions": 0,
            "replay_executions": 0,
        }
        _require(
            all(owner_evidence[key] == value for key, value in expected_metrics.items()),
            f"{name} D2 schema census drifted",
        )
        owner_values[name] = owner_value
        owner_bodies[name] = owner_body
        protocol_handles[name] = protocol_result.handle
        metrics_by_carrier[name] = {
            key: owner_evidence[key]
            for key in expected_metrics
            if key not in {"run_executions", "replay_executions"}
        }

    _require(len(set(owner_bodies.values())) == 5, "D2 carrier bodies are not distinct")
    findings.extend(
        (
            _finding("five-d1-core-admissions", "Affirmative", "F0V2B2D2-A-FIVE-CORES"),
            _finding("five-fresh-pairings", "Affirmative", "F0V2B2D2-A-FIVE-FRESH"),
            _finding("dual-execution-view-agreement", "Affirmative", "F0V2B2D2-A-VIEW-AGREEMENT"),
            _finding("five-distinct-exact-bodies", "Affirmative", "F0V2B2D2-A-FIVE-BODIES"),
            _finding("canonical-roundtrip", "Affirmative", "F0V2B2D2-A-CANONICAL-BODIES"),
            _finding("deterministic-reprojection", "Affirmative", "F0V2B2D2-A-DETERMINISM"),
            _finding("all-occurrence-receipt-types", "Affirmative", "F0V2B2D2-A-OCCURRENCE-RECEIPTS"),
            _finding("three-fresh-challenge-receipts", "Affirmative", "F0V2B2D2-A-FRESH-RECEIPTS"),
            _finding("all-oracle-receipt-branches", "Affirmative", "F0V2B2D2-A-ORACLE-BRANCHES"),
            _finding("oracle-mode-visibility-types", "Affirmative", "F0V2B2D2-A-ORACLE-SCHEMAS"),
            _finding("logical-zero-output-fixation", "Affirmative", "F0V2B2D2-A-LOGICAL-FIXATION"),
            _finding("terminal-reference-output-types", "Affirmative", "F0V2B2D2-A-TERMINAL-SCHEMAS"),
            _finding("three-lane-record-sum", "Affirmative", "F0V2B2D2-A-OUTCOME-LANES"),
            _finding("fresh-interpretation-failure-none", "Affirmative", "F0V2B2D2-A-NO-INTERPRETATION-FAILURE"),
            _finding("strategy-stop-partial-prefixes", "Affirmative", "F0V2B2D2-A-STRATEGY-PREFIXES"),
            _finding("operational-noncompletion-outside-record", "Affirmative", "F0V2B2D2-A-NONCOMPLETION-OUTSIDE"),
            _finding("no-run-executed", "Affirmative", "F0V2B2D2-A-NO-RUN"),
            _finding("no-replay-executed", "Affirmative", "F0V2B2D2-A-NO-REPLAY"),
        )
    )

    baseline = owner_values["integrated-baseline"]
    baseline_handle = protocol_handles["integrated-baseline"]
    _expect(
        model.admit_schema_claim(baseline_handle, copy.deepcopy(baseline)),
        "Affirmative",
        "F0V2B2D2-A-EXACT-SCHEMA-CLAIM",
        "exact schema claim",
    )
    findings.append(
        _finding("exact-schema-claim", "Affirmative", "F0V2B2D2-A-EXACT-CLAIM")
    )

    mutation_codes = {
        "receipt-branch": "F0V2B2D2-R-RECEIPT-BRANCH",
        "receipt-coordinate": "F0V2B2D2-R-RECEIPT-COORDINATE",
        "receipt-visibility": "F0V2B2D2-R-RECEIPT-VISIBILITY",
        "receipt-arity": "F0V2B2D2-R-RECEIPT-ARITY",
        "receipt-type": "F0V2B2D2-R-RECEIPT-TYPE",
        "terminal-reference": "F0V2B2D2-R-TERMINAL-REFERENCE",
        "stopping-terminal": "F0V2B2D2-R-STOPPING-TERMINAL",
        "inactive-occurrence-receipt": "F0V2B2D2-R-INACTIVE-OCCURRENCE-RECEIPT",
        "fixation-marker": "F0V2B2D2-R-FIXATION-MARKER",
        "public-binding-upgrade": "F0V2B2D2-R-PUBLICATION-MODE",
    }
    mutations = _mutations(model, baseline)
    _require(set(mutations) == set(mutation_codes), "mutation catalog drifted")
    for name, candidate in mutations.items():
        _expect(
            model.admit_schema_claim(baseline_handle, candidate),
            "Refused",
            mutation_codes[name],
            name,
        )
        findings.append(_finding(name, "Refused", mutation_codes[name]))

    fixture = model.d1.fixture("integrated-baseline")
    cold_args = (
        fixture.candidate.profiled_body,
        fixture.candidate.asserted_id.internal_reference(),
        fixture.protocol_candidate.profiled_body,
        fixture.protocol_candidate.asserted_id.internal_reference(),
        model.d1.raw_module_sources(fixture.environment),
        _algorithm_preimages(model, fixture),
        model.k1.DEFAULT_EVALUATION_CONTRACT.identity.internal_reference(),
    )
    cold_errors = (independent.ColdSchemaError, independent.d1.ColdIntegratedError)
    _require(
        _rejects(
            lambda: independent.project(cold_args[0][:-1], *cold_args[1:]),
            cold_errors,
        ),
        "cold D2 path accepted truncated Core bytes",
    )
    alternate = model.d1.fixture("history-challenge-condition")
    _require(
        _rejects(
            lambda: independent.project(
                cold_args[0],
                cold_args[1],
                alternate.protocol_candidate.profiled_body,
                alternate.protocol_candidate.asserted_id.internal_reference(),
                *cold_args[4:],
            ),
            cold_errors,
        ),
        "cold D2 path accepted a cross-Core Fresh Protocol",
    )
    _require(
        _rejects(
            lambda: independent.project(*cold_args[:5], cold_args[5][:-1], cold_args[6]),
            cold_errors,
        ),
        "cold D2 path accepted incomplete algorithm closure",
    )
    findings.extend(
        (
            _finding("cold-core-truncation", "Malformed", "F0V2B2D2-M-COLD-CORE"),
            _finding("cold-cross-core-fresh", "Refused", "F0V2B2D2-R-COLD-PROTOCOL"),
            _finding("cold-algorithm-closure", "Refused", "F0V2B2D2-R-COLD-ALGORITHM"),
        )
    )

    findings.extend(
        (
            _finding(
                "logical-fixation-receipt-placement-lines-1091-1092-and-1758-1765",
                "CannotAnswer",
                "F0V2B2D2-C-FIXATION-RECEIPT-PLACEMENT",
            ),
            _finding(
                "terminal-receipt-prefix-lines-1704-and-1767-1775",
                "CannotAnswer",
                "F0V2B2D2-C-TERMINAL-RECEIPT-PREFIX",
            ),
            _finding(
                "partial-run-body-line-1777",
                "CannotAnswer",
                "F0V2B2D2-C-PARTIAL-RUN-BODY",
            ),
            _finding(
                "strategy-stopped-membership-lines-1791-1794-and-1814-1817",
                "CannotAnswer",
                "F0V2B2D2-C-OUTCOME-OWNER",
            ),
            _finding(
                "execution-view-field-name-line-2128",
                "CannotAnswer",
                "F0V2B2D2-C-EXECUTION-FIELD-NAME",
            ),
            _finding("target-authority-untouched", "Affirmative", "F0V2B2D2-A-NONPUBLICATION"),
            _finding("general-core-derivation", "CannotAnswer", "F0V2B2D2-C-GENERAL-CORE"),
            _finding("runtime-generation", "CannotAnswer", "F0V2B2D2-C-RUNTIME"),
            _finding("replay-equality", "CannotAnswer", "F0V2B2D2-C-REPLAY"),
            _finding("canonical-transport-or-id", "CannotAnswer", "F0V2B2D2-C-TRANSPORT"),
            _finding("live-implementation-correspondence", "CannotAnswer", "F0V2B2D2-C-LIVE-CORRESPONDENCE"),
            _finding("cryptographic-or-protocol-theorem", "CannotAnswer", "F0V2B2D2-C-SECURITY"),
            _finding("fresh-run-schema-representability", "Affirmative", AGGREGATE),
        )
    )

    payload = [finding.value() for finding in findings]
    checksum = hashlib.sha256(
        json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()
    metrics = {
        "findings": len(findings),
        "findings_sha256": checksum,
        "carriers": len(owner_bodies),
        "exact_execution_view_bodies": len(owner_bodies),
        "distinct_execution_view_bodies": len(set(owner_bodies.values())),
        "exact_execution_view_body_bytes": sum(len(body) for body in owner_bodies.values()),
        "schema_definitions": typed_schema["definition_count"],
        "schema_source_nodes": typed_schema["source_node_count"],
        "occurrence_receipt_schemas": 23 * len(owner_bodies),
        "fresh_challenge_receipt_schemas": 3 * len(owner_bodies),
        "oracle_receipt_schemas": 9 * len(owner_bodies),
        "terminal_alternatives": 3 * len(owner_bodies),
        "strategy_stop_alternatives": 4 * len(owner_bodies),
        "schema_valid_mutations": len(mutations),
        "operational_noncompletion_names": list(
            model.OPERATIONAL_NONCOMPLETION_NAMES
        ),
        "run_executions": 0,
        "replay_executions": 0,
        "carriers_detail": metrics_by_carrier,
    }
    return findings, metrics


def _load_expected() -> dict[str, Any]:
    try:
        value = json.loads(EXPECTED.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise GateFailure("cannot load frozen findings") from error
    _require(type(value) is dict, "expected findings root differs")
    return value


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    findings, metrics = evaluate()
    observed = {
        "aggregate": AGGREGATE,
        "findings_sha256": metrics["findings_sha256"],
        "finding_codes": [finding.value() for finding in findings],
    }
    if args.check and observed != _load_expected():
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
        "aggregate": AGGREGATE,
        "outcomes": dict(sorted(counts.items())),
        "metrics": metrics,
    }
    if args.json:
        output["finding_codes"] = observed["finding_codes"]
    print(json.dumps(output, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
