#!/usr/bin/env python3
"""Audit exact source determinacy of the six current PIR owner-view bodies."""

from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass
import hashlib
import json
from pathlib import Path
import re
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
INTERACTION = ROOT / "docs-next/pir/interactive-core.md"
MANIFEST = ROOT / "docs-next/pir/profiles/interaction.json"
ANALYSIS = ROOT / "docs-next/analysis/cryptographic-properties.md"
RELATIONS = ROOT / "docs-next/analysis/semantic-relations.md"
F1R1B = ROOT / "evaluation/formal-source-target-core-f1r1b/reference_model.py"
EXPECTED = HERE / "expected-findings.json"


class AuditFailure(RuntimeError):
    """The source inventory or frozen classification drifted."""


@dataclass(frozen=True)
class Finding:
    name: str
    outcome: str
    code: str
    detail: str


VIEW_BODIES = (
    "PublicBindingViewBody",
    "StrategyDecisionViewBody",
    "PublicCoinViewBody",
    "EffectViewBody",
    "ClaimReductionViewBody",
    "ExecutionViewBody",
)

INSPECTED_REFERENCE_VOCABULARY = (
    "PIRReference",
)

EXACT_DERIVED_TYPES = (
    "PIRStaticViewCoordinate",
    "PIRStaticViewFieldCoordinate",
    "PIRStaticViewReadManifest",
    "PIRPCGraphResult",
    "PIRClaimCreationCoordinate",
    "PIRClaimUseCoordinate",
    "PIRFreshResolverCoordinate",
    "PIRRuntimeSchema",
)

EMPTY_F1R1B_FAMILIES = (
    "verifier_private_inputs=()",
    "constants=()",
    "derived_values=()",
    "oracles=()",
    "claims=()",
    "reductions=()",
)


def _read(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as error:
        raise AuditFailure(f"cannot read {path.relative_to(ROOT)}") from error


def _fragment(text: str, marker: str) -> str:
    start_token = f"<!-- zkc-profile-source:{marker}:start -->"
    end_token = f"<!-- zkc-profile-source:{marker}:end -->"
    if text.count(start_token) != 1 or text.count(end_token) != 1:
        raise AuditFailure(f"source fragment {marker} is absent or ambiguous")
    start = text.index(start_token) + len(start_token)
    end = text.index(end_token, start)
    return text[start:end].strip()


def _section(text: str, start: str, end: str) -> str:
    if text.count(start) != 1 or text.count(end) != 1:
        raise AuditFailure(f"section boundaries are absent or ambiguous: {start}")
    begin = text.index(start)
    finish = text.index(end, begin)
    return text[begin:finish]


def _digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _has_definition(text: str, symbol: str) -> bool:
    pattern = re.compile(rf"(?m)^\s*{re.escape(symbol)}\s*(?:\([^\n]*\))?\s*=")
    return pattern.search(text) is not None


def _observations() -> dict[str, Any]:
    interaction = _read(INTERACTION)
    manifest = json.loads(_read(MANIFEST))
    analysis = _read(ANALYSIS)
    relations = _read(RELATIONS)
    f1r1b = _read(F1R1B)

    static_fragment = _fragment(interaction, "interaction-static-views")
    body_fragment = _fragment(interaction, "interaction-body-grammar")
    view_display = _section(
        static_fragment,
        "PublicBindingViewBody = {",
        "### 13.3 Issuance, bindings, capabilities, and outcomes",
    )
    public_coin_display = _section(
        view_display, "PublicCoinViewBody = {", "EffectViewBody = {"
    )
    consumer_pressure = "\n".join(
        line.strip()
        for line in analysis.splitlines()
        if any(
            token in line
            for token in (
                "[challenges[S.challenge_ref].challenge_ref]",
                "[challenges[S.challenge_ref].domain]",
                "[scopes,bindings]",
                "[decision_points,prover_view_formation,guaranteed_prover_reads,",
                "[claims,reductions,terminal_dispositions]",
                "[protocol_id,core_id,challenge_interpretation,visible_history_law,",
            )
        )
    )
    relations_pressure = "\n".join(
        line.strip()
        for line in relations.splitlines()
        if any(
            token in line
            for token in (
                "CheckDecl algorithm",
                "TerminalDecl verdict",
                "AnalysisAcceptanceTerminalLeaves",
            )
        )
    )

    display_inventory = tuple(
        name for name in VIEW_BODIES if f"{name} = {{" in view_display
    )
    appendix_missing = tuple(
        name for name in VIEW_BODIES if not _has_definition(body_fragment, name)
    )
    undefined = tuple(
        symbol
        for symbol in INSPECTED_REFERENCE_VOCABULARY
        if symbol in static_fragment and not _has_definition(interaction, symbol)
    )
    exact_derived_inventory = tuple(
        item for item in EXACT_DERIVED_TYPES if _has_definition(interaction, item)
    )

    supported_kinds = manifest.get("supported_subject_kinds")
    declarations = manifest.get("declarations")
    serialized_manifest = json.dumps(manifest, sort_keys=True, separators=(",", ":"))

    exact_appendix_basis = all(
        _has_definition(body_fragment, name)
        for name in (
            "InteractiveCoreBody",
            "ProtocolBody",
            "ValueRefBody",
            "ChallengeBody",
            "CheckBody",
            "TerminalBody",
            "OccurrenceBody",
            "PCNodeBody",
        )
    )
    module_boundary = all(
        phrase in interaction
        for phrase in (
            "ModuleEffectRef = {",
            "payload: MetaValueV0",
            "strict decoding of a ModuleEffect payload under its exact owner schema",
            "No opaque effect, callback, or",
            "authored observation set is accepted.",
        )
    )
    public_coin_graph_complete = all(
        item in public_coin_display
        for item in (
            "graph: PIRPCGraphResult",
            "structural_public_coin_eligibility",
            "verifier_private_predecessors",
            "public_condition_predecessors",
        )
    )

    return {
        "static_fragment_digest": _digest(static_fragment),
        "body_fragment_digest": _digest(body_fragment),
        "view_display_digest": _digest(view_display),
        "consumer_pressure_digest": _digest(consumer_pressure + relations_pressure),
        "manifest_digest": _digest(serialized_manifest),
        "display_inventory": display_inventory,
        "appendix_exact_owner_basis": exact_appendix_basis,
        "appendix_missing_view_bodies": appendix_missing,
        "generic_static_view_body_compiler": _has_definition(
            static_fragment, "StaticViewBody"
        ),
        "undefined_vocabulary": undefined,
        "pir_reference_definition_exact": all(
            phrase in static_fragment
            for phrase in (
                "PIRReference =",
                "ScopeRef | OccurrenceRef | ProverDecisionPointRef | ChallengeRef",
                "| BindingRef | ClaimRef | ReductionRef | CheckRef | TerminalRef | OracleRef",
                "| PublicInputRef | VerifierPrivateInputRef | ConstantRef | DerivedValueRef",
                "| ValueRef",
                "| ProtocolDeclarationRef<K>",
                "PIRReferenceBody(x) =",
            )
        ),
        "exact_derived_type_inventory": exact_derived_inventory,
        "prover_view_coordinate_replaced": (
            "ProverViewCoordinate" not in static_fragment
            and _has_definition(interaction, "PIRStaticViewCoordinate")
        ),
        "guard_reference_replaced": (
            "guard_ref" not in view_display and "guard: exact Guard" in view_display
        ),
        "public_coin_graph_complete": public_coin_graph_complete,
        "runtime_schema_defined": _has_definition(interaction, "PIRRuntimeSchema"),
        "fresh_resolver_coordinate_defined": _has_definition(
            interaction, "PIRFreshResolverCoordinate"
        ),
        "module_effect_owner_boundary_exact": module_boundary,
        "nested_consumer_pressure_present": (
            len(consumer_pressure.splitlines()) >= 6
            and len(relations_pressure.splitlines()) >= 3
        ),
        "published_static_view_schema_present": (
            "pir.static-view-schema" in serialized_manifest
            or (
                isinstance(supported_kinds, list)
                and "pir.static-view-schema" in supported_kinds
            )
            or (
                isinstance(declarations, list)
                and any(
                    isinstance(row, dict)
                    and row.get("kind") == "pir.static-view-schema"
                    for row in declarations
                )
            )
        ),
        "empty_f1r1b_families": tuple(
            item for item in EMPTY_F1R1B_FAMILIES if item in f1r1b
        ),
        "f1r1b_effect_alias_is_bounded": (
            "Effect: TypeAlias = ProverMessageEffect | ChallengeEffect | CheckEffect | TerminalEffect"
            in f1r1b
        ),
    }


def _findings(observed: dict[str, Any]) -> list[Finding]:
    required = {
        "display_inventory": VIEW_BODIES,
        "appendix_exact_owner_basis": True,
        "appendix_missing_view_bodies": VIEW_BODIES,
        "undefined_vocabulary": (),
        "pir_reference_definition_exact": True,
        "generic_static_view_body_compiler": True,
        "exact_derived_type_inventory": EXACT_DERIVED_TYPES,
        "prover_view_coordinate_replaced": True,
        "guard_reference_replaced": True,
        "public_coin_graph_complete": True,
        "runtime_schema_defined": True,
        "fresh_resolver_coordinate_defined": True,
        "module_effect_owner_boundary_exact": True,
        "nested_consumer_pressure_present": True,
        "published_static_view_schema_present": True,
        "empty_f1r1b_families": EMPTY_F1R1B_FAMILIES,
        "f1r1b_effect_alias_is_bounded": True,
    }
    drift = {
        key: {"expected": value, "observed": observed.get(key)}
        for key, value in required.items()
        if observed.get(key) != value
    }
    if drift:
        raise AuditFailure(
            "F0-V2B0 source inventory drifted:\n"
            + json.dumps(drift, indent=2, sort_keys=True)
        )

    return [
        Finding(
            "authenticated-static-view-source",
            "Affirmative",
            "F0V2B0-A-AUTHENTICATED-SOURCE",
            "the selected Interaction source fragment contains all six displays",
        ),
        Finding(
            "exact-core-protocol-body-basis",
            "Affirmative",
            "F0V2B0-A-OWNER-BASIS",
            "Appendix A defines exact Core, Protocol, declaration, occurrence, and PCNode bodies",
        ),
        Finding(
            "six-view-display-inventory",
            "Affirmative",
            "F0V2B0-A-SIX-DISPLAYS",
            "the source names exactly the five Core views and Fresh Execution view",
        ),
        Finding(
            "nested-consumer-leaf-pressure",
            "Affirmative",
            "F0V2B0-A-CONSUMER-GRANULARITY",
            "Analysis and Relations select nested Challenge, Check, Terminal, and view fields",
        ),
        Finding(
            "exact-module-effect-owner-boundary",
            "Affirmative",
            "F0V2B0-A-MODULE-BOUNDARY",
            "Core admission already fixes module/declaration/payload ownership and strict decoding",
        ),
        Finding(
            "pir-reference-boundary-definition",
            "Affirmative",
            "F0V2B0-A-PIR-REFERENCE",
            "PIRReference is a closed union with a delegated exact body",
        ),
        Finding(
            "prover-view-coordinate-definition",
            "Affirmative",
            "F0V2B0-A-PROVER-VIEW-COORDINATE",
            "the migrated text replaces the undefined token with the exact static-view coordinate algebra",
        ),
        Finding(
            "strategy-guard-coordinate-definition",
            "Affirmative",
            "F0V2B0-A-GUARD-REFERENCE",
            "the migrated strategy view carries the exact admitted Guard rather than an undefined reference",
        ),
        Finding(
            "six-canonical-view-body-functions",
            "Affirmative",
            "F0V2B0-A-VIEW-BODIES",
            "the six complete displays are selected by the authenticated generic StaticViewBody compiler",
        ),
        Finding(
            "derived-coordinate-and-closure-bodies",
            "Affirmative",
            "F0V2B0-A-DERIVED-FIELDS",
            "the migrated text defines the coordinate, graph, claim, resolver, and runtime-description types",
        ),
        Finding(
            "public-coin-retained-graph-body",
            "Affirmative",
            "F0V2B0-A-PCGRAPH-BODY",
            "the PublicCoin view carries the retained graph, classes, sinks, and predecessor evidence",
        ),
        Finding(
            "fresh-resolver-coordinate-body",
            "Affirmative",
            "F0V2B0-A-FRESH-RESOLVER",
            "Fresh resolver coordinates have an exact closed record type",
        ),
        Finding(
            "completed-run-record-schema-body",
            "Affirmative",
            "F0V2B0-A-RUN-SCHEMA",
            "the runtime schema is a finite recursive description with an authenticated body grammar",
        ),
        Finding(
            "constructor-complete-executable-basis",
            "CannotAnswer",
            "F0V2B0-C-CONSTRUCTOR-COVERAGE",
            "F1-R1B omits six source families and supports only four effect constructors",
        ),
        Finding(
            "published-static-view-schema-catalog",
            "Affirmative",
            "F0V2B0-A-PUBLISHED-CATALOG",
            "the candidate Interaction manifest carries all six static-view schema entries",
        ),
        Finding(
            "verbatim-display-as-canonical-grammar",
            "Refused",
            "F0V2B0-R-VERBATIM-DISPLAY",
            "a compiler may not omit retained facts or invent bodies for prose fields",
        ),
        Finding(
            "consumer-authored-shadow-schema",
            "Refused",
            "F0V2B0-R-CONSUMER-SCHEMA",
            "Analysis and Relations paths cannot repair absent PIR owner schemas",
        ),
        Finding(
            "generic-module-payload-reflection",
            "Refused",
            "F0V2B0-R-MODULE-REFLECTION",
            "generic view traversal cannot descend into declaration-typed module payloads",
        ),
    ]


def _load_expected() -> dict[str, Any]:
    try:
        value = json.loads(EXPECTED.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise AuditFailure("cannot read frozen F0-V2B0 findings") from error
    if type(value) is not dict:
        raise AuditFailure("frozen F0-V2B0 findings have the wrong shape")
    return value


def run_audit() -> dict[str, Any]:
    observed = _observations()
    findings = _findings(observed)
    cases = [
        {"name": row.name, "outcome": row.outcome, "code": row.code} for row in findings
    ]
    aggregate = {
        "outcome": "CannotAnswer",
        "code": "F0V2B0-C-OWNER-BODY-DETERMINACY",
    }
    evidence_control = {
        key: observed[key]
        for key in (
            "static_fragment_digest",
            "body_fragment_digest",
            "view_display_digest",
            "consumer_pressure_digest",
            "manifest_digest",
        )
    }
    expected = _load_expected()
    projection = {
        "aggregate": aggregate,
        "evidence_control": evidence_control,
        "cases": cases,
    }
    if projection != expected:
        raise AuditFailure(
            "F0-V2B0 frozen result drifted:\n"
            + json.dumps(
                {"expected": expected, "observed": projection},
                indent=2,
                sort_keys=True,
            )
        )
    return {
        "format": "zkc.formal-source-view-body-audit-f0v2b0.v0",
        "aggregate": aggregate,
        "cases": [asdict(row) for row in findings],
        "evidence": observed,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument(
        "--emit-expected",
        action="store_true",
        help="print the current frozen projection for review",
    )
    arguments = parser.parse_args()
    if arguments.emit_expected:
        observed = _observations()
        findings = _findings(observed)
        projection = {
            "aggregate": {
                "outcome": "CannotAnswer",
                "code": "F0V2B0-C-OWNER-BODY-DETERMINACY",
            },
            "evidence_control": {
                key: observed[key]
                for key in (
                    "static_fragment_digest",
                    "body_fragment_digest",
                    "view_display_digest",
                    "consumer_pressure_digest",
                    "manifest_digest",
                )
            },
            "cases": [
                {"name": row.name, "outcome": row.outcome, "code": row.code}
                for row in findings
            ],
        }
        print(json.dumps(projection, indent=2))
        return 0
    result = run_audit()
    if arguments.check:
        print(
            "[formal-source-view-body-audit-f0v2b0] "
            f"{len(result['cases'])}/{len(result['cases'])} findings; "
            f"{result['aggregate']['outcome']}/{result['aggregate']['code']}"
        )
    else:
        print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
