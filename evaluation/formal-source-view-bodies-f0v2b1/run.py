#!/usr/bin/env python3
"""Run the bounded normalized owner-view grammar and derivation gate."""

from __future__ import annotations

import argparse
import copy
from dataclasses import asdict, dataclass, replace
import json
from pathlib import Path
from typing import Any, Callable

import independent as cold
import model


HERE = Path(__file__).resolve().parent
EXPECTED = HERE / "expected-findings.json"


class GateFailure(RuntimeError):
    """The B1 result, independent agreement, or frozen classification drifted."""


@dataclass(frozen=True)
class Finding:
    name: str
    outcome: str
    code: str
    detail: str


def _finding(name: str, outcome: str, code: str, detail: str) -> Finding:
    return Finding(name, outcome, code, detail)


def _alter_body(value: dict[str, Any]) -> None:
    value["body"] = value["body"] + "00"


def _mutate(candidate: dict[str, Any], name: str) -> None:
    values = candidate["values"]
    binding = values["PublicBindingView"]
    strategy = values["StrategyDecisionView"]
    coin = values["PublicCoinView"]
    effect = values["EffectView"]
    claims = values["ClaimReductionView"]
    execution = values["ExecutionView"]

    operations: dict[str, Callable[[], None]] = {
        "source-digest-substitution": lambda: candidate.__setitem__(
            "source_digest", "00" * 32
        ),
        "schema-field-removal": lambda: candidate["schemas"]["PublicBindingView"][
            "fields"
        ].pop(),
        "catalog-schema-substitution": lambda: candidate["catalog"][
            "PublicBindingView"
        ].__setitem__("schema_digest", "11" * 32),
        "manifest-leaf-omission": lambda: candidate["requested_manifests"][
            "PublicBindingView"
        ].pop(),
        "manifest-coordinate-duplication": lambda: candidate["requested_manifests"][
            "PublicBindingView"
        ].append(
            copy.deepcopy(candidate["requested_manifests"]["PublicBindingView"][-1])
        ),
        "manifest-cross-view-replay": lambda: candidate["requested_manifests"][
            "PublicBindingView"
        ][0].__setitem__("view", "EffectView"),
        "core-id-substitution": lambda: _alter_body(binding[0]),
        "scope-path-omission": lambda: binding[1][0][3].clear(),
        "binding-scope-substitution": lambda: _alter_body(binding[2][0][1]),
        "binding-value-type-substitution": lambda: _alter_body(binding[2][0][4]),
        "decision-occurrence-substitution": lambda: _alter_body(strategy[1][0][1]),
        "decision-guard-substitution": lambda: _alter_body(strategy[1][0][3]),
        "decision-prior-omission": lambda: strategy[1][1][5].clear(),
        "guaranteed-read-omission": lambda: strategy[3].pop(),
        "guaranteed-read-phantom": lambda: strategy[3].append(
            copy.deepcopy(strategy[3][-1])
        ),
        "guaranteed-read-type-substitution": lambda: _alter_body(strategy[3][0][2]),
        "legal-move-type-substitution": lambda: _alter_body(strategy[4][0][1]["value"]),
        "pc-edge-omission": lambda: coin[1][1].pop(),
        "pc-edge-reversal": lambda: coin[1][1][0].update(
            {0: coin[1][1][0][1], 1: coin[1][1][0][0]}
        ),
        "pc-class-substitution": lambda: coin[1][3][0][1].__setitem__("case", 1),
        "pc-topological-reordering": lambda: coin[1][2].__setitem__(
            slice(0, 2), [coin[1][2][1], coin[1][2][0]]
        ),
        "pc-sink-omission": lambda: coin[1][4].pop(),
        "pc-acceptance-sink-omission": lambda: coin[1][5].pop(),
        "pc-eligibility-substitution": lambda: coin.__setitem__(2, False),
        "challenge-backlink-substitution": lambda: _alter_body(coin[4][0][1]),
        "challenge-domain-substitution": lambda: _alter_body(coin[4][0][4]),
        "occurrence-guard-substitution": lambda: _alter_body(effect[1][4][2]),
        "occurrence-output-type-substitution": lambda: _alter_body(effect[1][3][4][0]),
        "value-predecessor-omission": lambda: effect[2][4][2].pop(),
        "message-backlink-substitution": lambda: _alter_body(effect[3][0][0]),
        "check-algorithm-substitution": lambda: _alter_body(effect[5][0][1]),
        "check-input-reordering": lambda: effect[5][0][3].__setitem__(
            slice(0, 2), [effect[5][0][3][1], effect[5][0][3][0]]
        ),
        "terminal-verdict-substitution": lambda: effect[6][0][1].__setitem__("case", 1),
        "terminal-backlink-substitution": lambda: _alter_body(effect[6][0][5]),
        "phantom-claim": lambda: claims[1].append(None),
        "execution-protocol-id-substitution": lambda: _alter_body(execution[0]),
        "resolver-occurrence-substitution": lambda: _alter_body(execution[4][0][1]),
        "resolver-domain-substitution": lambda: _alter_body(execution[4][0][3]),
        "runtime-output-arity-substitution": lambda: execution[6][0][0][1].clear(),
        "runtime-output-type-substitution": lambda: _alter_body(
            execution[6][0][3][1][0]
        ),
        "execution-law-substitution": lambda: execution[5].__setitem__(
            "name", "core-admission-v0"
        ),
        "run-view-law-substitution": lambda: execution[9].__setitem__(
            "name", "execution-and-replay-v0"
        ),
        "unsupported-oracle-insertion": lambda: effect[4].append(None),
        "unsupported-extension-insertion": lambda: effect[7].append(None),
    }
    try:
        operation = operations[name]
    except KeyError as error:  # pragma: no cover - gate author error
        raise AssertionError(f"unknown B1 mutation {name}") from error
    operation()


MUTATIONS: tuple[tuple[str, str, str], ...] = (
    (
        "source-digest-substitution",
        "F0V2B1-R-SOURCE",
        "another grammar source cannot be substituted",
    ),
    (
        "schema-field-removal",
        "F0V2B1-R-SCHEMA",
        "a compiled body cannot omit one source field",
    ),
    (
        "catalog-schema-substitution",
        "F0V2B1-R-CATALOG",
        "the source-bound schema digest is exact",
    ),
    (
        "manifest-leaf-omission",
        "F0V2B1-R-MANIFEST-OMISSION",
        "a complete manifest cannot omit an active leaf",
    ),
    (
        "manifest-coordinate-duplication",
        "F0V2B1-R-MANIFEST-DUPLICATE",
        "a complete manifest is coordinate-unique",
    ),
    (
        "manifest-cross-view-replay",
        "F0V2B1-R-MANIFEST-VIEW",
        "a coordinate cannot be replayed under another owner view",
    ),
    (
        "core-id-substitution",
        "F0V2B1-R-CORE-ID",
        "all five Core views retain the admitted Core identity",
    ),
    (
        "scope-path-omission",
        "F0V2B1-R-SCOPE-PATH",
        "the root scope path is nonempty and owner-derived",
    ),
    (
        "binding-scope-substitution",
        "F0V2B1-R-BINDING-SCOPE",
        "binding scope is owner-derived",
    ),
    (
        "binding-value-type-substitution",
        "F0V2B1-R-BINDING-TYPE",
        "binding type is derived from its exact ValueRef",
    ),
    (
        "decision-occurrence-substitution",
        "F0V2B1-R-DECISION-BACKLINK",
        "a decision ref is its exact occurrence ordinal",
    ),
    (
        "decision-guard-substitution",
        "F0V2B1-R-DECISION-GUARD",
        "the complete occurrence Guard is retained",
    ),
    (
        "decision-prior-omission",
        "F0V2B1-R-DECISION-PRIOR",
        "prior decision refs are complete",
    ),
    (
        "guaranteed-read-omission",
        "F0V2B1-R-READ-OMISSION",
        "the bounded guaranteed-read map is complete",
    ),
    (
        "guaranteed-read-phantom",
        "F0V2B1-R-READ-PHANTOM",
        "caller-authored duplicate reads do not form",
    ),
    (
        "guaranteed-read-type-substitution",
        "F0V2B1-R-READ-TYPE",
        "each read carries its owner-derived ValueType",
    ),
    (
        "legal-move-type-substitution",
        "F0V2B1-R-MOVE-TYPE",
        "legal move type follows the exact message declaration",
    ),
    (
        "pc-edge-omission",
        "F0V2B1-R-PC-EDGE-OMISSION",
        "the retained PCGraph edge table is complete",
    ),
    (
        "pc-edge-reversal",
        "F0V2B1-R-PC-EDGE-DIRECTION",
        "PCGraph dependency direction is exact",
    ),
    (
        "pc-class-substitution",
        "F0V2B1-R-PC-CLASS",
        "PCClass is recomputed in topological order",
    ),
    (
        "pc-topological-reordering",
        "F0V2B1-R-PC-TOPOLOGY",
        "the retained Kahn order cannot be reordered",
    ),
    (
        "pc-sink-omission",
        "F0V2B1-R-PC-SINK",
        "the bounded public-coin sink set is complete",
    ),
    (
        "pc-acceptance-sink-omission",
        "F0V2B1-R-PC-ACCEPTANCE",
        "the bounded acceptance sink set is complete",
    ),
    (
        "pc-eligibility-substitution",
        "F0V2B1-R-PC-ELIGIBILITY",
        "eligibility is derived from retained classes and sinks",
    ),
    (
        "challenge-backlink-substitution",
        "F0V2B1-R-CHALLENGE-BACKLINK",
        "the Challenge occurrence backlink is exact",
    ),
    (
        "challenge-domain-substitution",
        "F0V2B1-R-CHALLENGE-DOMAIN",
        "the Challenge domain reference is exact",
    ),
    (
        "occurrence-guard-substitution",
        "F0V2B1-R-OCCURRENCE-GUARD",
        "the occurrence schedule retains complete guards",
    ),
    (
        "occurrence-output-type-substitution",
        "F0V2B1-R-OUTPUT-TYPE",
        "occurrence output types are owner-derived",
    ),
    (
        "value-predecessor-omission",
        "F0V2B1-R-VALUE-PREDECESSOR",
        "the Check output retains all direct value predecessors",
    ),
    (
        "message-backlink-substitution",
        "F0V2B1-R-MESSAGE-BACKLINK",
        "message declaration backlinks are exact",
    ),
    (
        "check-algorithm-substitution",
        "F0V2B1-R-CHECK-ALGORITHM",
        "the Check algorithm ID is exact",
    ),
    (
        "check-input-reordering",
        "F0V2B1-R-CHECK-INPUTS",
        "ordered Check inputs cannot be permuted",
    ),
    (
        "terminal-verdict-substitution",
        "F0V2B1-R-TERMINAL-VERDICT",
        "terminal verdicts are owner-derived",
    ),
    (
        "terminal-backlink-substitution",
        "F0V2B1-R-TERMINAL-BACKLINK",
        "terminal occurrence backlinks are exact",
    ),
    (
        "phantom-claim",
        "F0V2B1-R-PHANTOM-CLAIM",
        "the bounded empty claim family cannot be caller-populated",
    ),
    (
        "execution-protocol-id-substitution",
        "F0V2B1-R-PROTOCOL-ID",
        "ExecutionView retains the admitted Fresh Protocol ID",
    ),
    (
        "resolver-occurrence-substitution",
        "F0V2B1-R-RESOLVER-BACKLINK",
        "Fresh resolver occurrence is owner-derived",
    ),
    (
        "resolver-domain-substitution",
        "F0V2B1-R-RESOLVER-DOMAIN",
        "Fresh resolver domain is exact",
    ),
    (
        "runtime-output-arity-substitution",
        "F0V2B1-R-RUNTIME-ARITY",
        "completed-record typing retains every occurrence arity",
    ),
    (
        "runtime-output-type-substitution",
        "F0V2B1-R-RUNTIME-TYPE",
        "completed-record typing retains exact output types",
    ),
    (
        "execution-law-substitution",
        "F0V2B1-R-EXECUTION-LAW",
        "generated execution uses its fixed profile law",
    ),
    (
        "run-view-law-substitution",
        "F0V2B1-R-RUN-VIEW-LAW",
        "run-view issuance uses its fixed profile law",
    ),
    (
        "unsupported-oracle-insertion",
        "F0V2B1-R-ORACLE-OUTSIDE-SLICE",
        "B1 cannot invent an Oracle row",
    ),
    (
        "unsupported-extension-insertion",
        "F0V2B1-R-EXTENSION-OUTSIDE-SLICE",
        "B1 cannot invent a module-extension row",
    ),
)


def _reject_reference(candidate: object, handles: tuple[object, object]) -> str:
    try:
        model.observe(candidate, *handles)
    except model.BoundedError as error:
        return f"BoundedError: {error}"
    except Exception as error:  # pragma: no cover - implementation defect
        raise GateFailure(
            f"reference path raised unexpected {type(error).__name__}: {error}"
        ) from error
    raise GateFailure("reference path accepted a forbidden B1 mutation")


def _reject_cold(candidate: object, handles: tuple[object, object]) -> str:
    try:
        cold.observe(candidate, *handles)
    except cold.ColdError as error:
        return f"ColdError: {error}"
    except Exception as error:  # pragma: no cover - implementation defect
        raise GateFailure(
            f"cold path raised unexpected {type(error).__name__}: {error}"
        ) from error
    raise GateFailure("cold path accepted a forbidden B1 mutation")


def _owner_mutation_diagnostics() -> dict[str, dict[str, str]]:
    diagnostics: dict[str, dict[str, str]] = {}

    core, protocol = model.admitted_handles()
    package = model.build_candidate(core, protocol)
    core.core = replace(
        core.core,
        public_inputs=(*core.core.public_inputs, model.owner.InputDecl(model.owner.Z3)),
    )
    diagnostics["retained-core-body-mutation"] = {
        "reference": _reject_reference_with_handles(package, core, protocol)
    }
    cold_core, cold_protocol = cold._admit()
    cold_core.core = replace(
        cold_core.core,
        public_inputs=(
            *cold_core.core.public_inputs,
            cold.owner.InputDecl(cold.owner.Z3),
        ),
    )
    try:
        cold._derive(cold_core, cold_protocol)
    except cold.ColdError as error:
        diagnostics["retained-core-body-mutation"]["cold"] = f"ColdError: {error}"
    else:  # pragma: no cover - implementation defect
        raise GateFailure("cold path accepted a mutated retained Core")

    core, protocol = model.admitted_handles()
    package = model.build_candidate(core, protocol)
    _other_core, other_protocol = model.admitted_handles()
    protocol.core_handle = other_protocol.core_handle
    diagnostics["protocol-core-handle-substitution"] = {
        "reference": _reject_reference_with_handles(package, core, protocol)
    }
    cold_core, cold_protocol = cold._admit()
    _cold_other_core, cold_other_protocol = cold._admit()
    cold_protocol.core_handle = cold_other_protocol.core_handle
    try:
        cold._derive(cold_core, cold_protocol)
    except cold.ColdError as error:
        diagnostics["protocol-core-handle-substitution"]["cold"] = f"ColdError: {error}"
    else:  # pragma: no cover - implementation defect
        raise GateFailure("cold path accepted a substituted Protocol Core handle")
    return diagnostics


def _reject_reference_with_handles(
    candidate: object, core: object, protocol: object
) -> str:
    try:
        model.observe(candidate, core, protocol)
    except model.BoundedError as error:
        return f"BoundedError: {error}"
    except Exception as error:  # pragma: no cover - implementation defect
        raise GateFailure(
            f"reference owner mutation raised unexpected {type(error).__name__}: {error}"
        ) from error
    raise GateFailure("reference path accepted a mutated retained owner handle")


def _load_expected() -> dict[str, Any]:
    try:
        value = json.loads(EXPECTED.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise GateFailure("cannot read frozen F0-V2B1 findings") from error
    if type(value) is not dict:
        raise GateFailure("frozen F0-V2B1 findings have the wrong shape")
    return value


def _projection() -> tuple[dict[str, Any], dict[str, Any]]:
    reference_handles = model.admitted_handles()
    cold_handles = cold._admit()
    reference_candidate = model.build_candidate(*reference_handles)
    cold_candidate = cold.build_candidate(*cold_handles)
    if reference_candidate != cold_candidate:
        raise GateFailure("the two source compilers or owner derivations disagree")
    reference = model.observe(reference_candidate, *reference_handles)
    independent = cold.observe(reference_candidate, *cold_handles)
    if reference != independent:
        raise GateFailure(
            "reference and independent B1 evidence disagree:\n"
            + json.dumps(
                {"reference": reference, "independent": independent},
                indent=2,
                sort_keys=True,
            )
        )

    findings = [
        _finding(
            "bounded-schema-source",
            "Affirmative",
            "F0V2B1-A-SOURCE",
            "one finite source contract names all six bounded normalized schemas",
        ),
        _finding(
            "recursive-iterative-schema-agreement",
            "Affirmative",
            "F0V2B1-A-SCHEMA-AGREEMENT",
            "recursive and worklist compilers expand identical schemas",
        ),
        _finding(
            "independent-owner-identity-agreement",
            "Affirmative",
            "F0V2B1-A-OWNER-IDENTITY",
            "separately admitted owner models produce identical Core and Protocol IDs",
        ),
        _finding(
            "independent-six-view-derivation",
            "Affirmative",
            "F0V2B1-A-DERIVATION-AGREEMENT",
            "algorithmic and finite-oracle derivations produce identical six-view values",
        ),
        _finding(
            "six-owner-view-bodies",
            "Affirmative",
            "F0V2B1-A-SIX-VIEWS",
            "all five Core views and Fresh ExecutionView form",
        ),
        _finding(
            "exact-complete-manifests",
            "Affirmative",
            "F0V2B1-A-MANIFESTS",
            "both paths enumerate the same 329 active leaves",
        ),
        _finding(
            "owner-only-view-inputs",
            "Affirmative",
            "F0V2B1-A-OWNER-ONLY",
            "formation receives admitted handles and no caller-authored view fields",
        ),
        _finding(
            "bounded-decision-read-map",
            "Affirmative",
            "F0V2B1-A-DECISION-READS",
            "two decisions and seven guaranteed reads are independently reproduced",
        ),
        _finding(
            "retained-bounded-pcgraph",
            "Affirmative",
            "F0V2B1-A-PCGRAPH",
            "the 21-node 27-edge graph, order, classes, sinks, and eligibility agree",
        ),
        _finding(
            "effect-value-backlinks",
            "Affirmative",
            "F0V2B1-A-EFFECT-VALUE",
            "six occurrences and five value producers retain exact types and backlinks",
        ),
        _finding(
            "fresh-runtime-description",
            "Affirmative",
            "F0V2B1-A-RUNTIME-SCHEMA",
            "one resolver and all six occurrence and two terminal record descriptions agree",
        ),
        _finding(
            "explicit-bounded-empty-families",
            "Affirmative",
            "F0V2B1-A-EMPTY-FAMILIES",
            "B2-only families are represented by max-zero sequences",
        ),
        _finding(
            "constructor-complete-owner-derivation",
            "CannotAnswer",
            "F0V2B1-C-CONSTRUCTOR-COVERAGE",
            "oracles, private and derived values, scopes, claims, reductions, joint sharing, verifier messages, and modules await B2",
        ),
        _finding(
            "general-pcgraph-sink-and-transfer-coverage",
            "CannotAnswer",
            "F0V2B1-C-PCGRAPH-GENERAL",
            "the bounded graph does not exercise private, invalid, Oracle, reduction, or module transfers",
        ),
        _finding(
            "target-profile-publication-and-migration",
            "CannotAnswer",
            "F0V2B1-C-TARGET-MIGRATION",
            "the candidate source is not published into the Interaction profile",
        ),
        _finding(
            "live-owner-implementation-correspondence",
            "CannotAnswer",
            "F0V2B1-C-LIVE-IMPLEMENTATION",
            "Python owner handles are bounded research fixtures, not the zkc implementation",
        ),
        _finding(
            "proper-subset-read-closure",
            "CannotAnswer",
            "F0V2B1-C-PARTIAL-CLOSURE",
            "question-relative transitive closure remains F1-R1C2 work",
        ),
    ]
    mutation_diagnostics: dict[str, dict[str, str]] = {}
    for mutation, code, detail in MUTATIONS:
        candidate = copy.deepcopy(reference_candidate)
        _mutate(candidate, mutation)
        mutation_diagnostics[mutation] = {
            "reference": _reject_reference(candidate, reference_handles),
            "cold": _reject_cold(candidate, cold_handles),
        }
        findings.append(_finding(mutation, "Refused", code, detail))
    owner_diagnostics = _owner_mutation_diagnostics()
    findings.extend(
        (
            _finding(
                "retained-core-body-mutation",
                "Refused",
                "F0V2B1-R-RETAINED-CORE-MUTATION",
                "a process-local bearer cannot retain authority after its Core body changes",
            ),
            _finding(
                "protocol-core-handle-substitution",
                "Refused",
                "F0V2B1-R-PROTOCOL-CORE-HANDLE",
                "Fresh Protocol authority is paired with one exact admitted Core handle",
            ),
        )
    )
    evidence_control = {
        "source_digest": reference["source_digest"],
        "views": reference["views"],
        "total_leaf_count": reference["total_leaf_count"],
        "owner": reference["owner"],
        "explicit_empty_families": reference["explicit_empty_families"],
    }
    projection = {
        "aggregate": {
            "outcome": "Affirmative",
            "code": "F0V2B1-A-BOUNDED-NORMALIZED-DERIVATION",
        },
        "evidence_control": evidence_control,
        "cases": [
            {"name": row.name, "outcome": row.outcome, "code": row.code}
            for row in findings
        ],
    }
    diagnostics = {
        "mutations": mutation_diagnostics,
        "owner_mutations": owner_diagnostics,
    }
    return projection, {
        "findings": [asdict(row) for row in findings],
        "evidence": reference,
        "diagnostics": diagnostics,
    }


def run_gate() -> dict[str, Any]:
    projection, details = _projection()
    expected = _load_expected()
    if projection != expected:
        raise GateFailure(
            "F0-V2B1 frozen projection drifted:\n"
            + json.dumps(
                {"expected": expected, "observed": projection},
                indent=2,
                sort_keys=True,
            )
        )
    return {
        "format": "zkc.formal-source-view-bodies-f0v2b1.v0",
        "aggregate": projection["aggregate"],
        "cases": details["findings"],
        "evidence": details["evidence"],
        "diagnostics": details["diagnostics"],
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--emit-expected", action="store_true")
    arguments = parser.parse_args()
    if arguments.emit_expected:
        projection, _details = _projection()
        print(json.dumps(projection, indent=2))
        return 0
    result = run_gate()
    if arguments.check:
        print(
            "[formal-source-view-bodies-f0v2b1] "
            f"{len(result['cases'])}/{len(result['cases'])} findings; "
            f"{result['aggregate']['outcome']}/{result['aggregate']['code']}; "
            f"{result['evidence']['total_leaf_count']} active leaves"
        )
    else:
        print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
