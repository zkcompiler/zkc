#!/usr/bin/env python3
"""Check one mixed-challenge, multi-binding end-to-end pressure subject."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from types import ModuleType
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
MODEL = HERE / "model.py"
EXPECTED = HERE / "expected-findings.json"
CORE_PAGE = ROOT / "docs-next/pir/interactive-core.md"
FS_PAGE = ROOT / "docs-next/pir/fiat-shamir.md"
INTERFACE_PAGE = ROOT / "docs-next/pir/interfaces-and-plans.md"
ANALYSIS_PAGE = ROOT / "docs-next/analysis/cryptographic-properties.md"
ANALYSIS_MODEL_PAGE = ROOT / "docs-next/analysis/analysis-model.md"
ANALYSIS_PROFILE = ROOT / "docs-next/analysis/profiles/cryptographic-property.json"
PROVIDER_PACKET = (
    ROOT
    / "docs-next/notes/semantic-revalidation-and-redesign/formal-assurance-research"
    / "f2o2-provider-carrier-decision-2026-09-03.md"
)

AGGREGATE_OUTCOME = "Affirmative"
AGGREGATE_CODE = "F0V4-A-END-TO-END-COMPOSITION"


class CheckFailure(RuntimeError):
    """The finite composition, owner source, or frozen evidence drifted."""


@dataclass(frozen=True)
class Finding:
    name: str
    outcome: str
    code: str

    def value(self) -> list[str]:
        return [self.name, self.outcome, self.code]


def _load(name: str, path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise CheckFailure(f"cannot load {path.relative_to(ROOT)}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _require(condition: bool, detail: str) -> None:
    if not condition:
        raise CheckFailure(detail)


def _digest(value: Any) -> str:
    return hashlib.sha256(
        json.dumps(
            value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
        ).encode("ascii")
    ).hexdigest()


def _source_gate() -> dict[str, Any]:
    core = CORE_PAGE.read_text(encoding="utf-8")
    fs = FS_PAGE.read_text(encoding="utf-8")
    interface = INTERFACE_PAGE.read_text(encoding="utf-8")
    analysis = ANALYSIS_PAGE.read_text(encoding="utf-8")
    analysis_model = ANALYSIS_MODEL_PAGE.read_text(encoding="utf-8")
    analysis_profile = json.loads(ANALYSIS_PROFILE.read_text(encoding="utf-8"))
    provider_packet = PROVIDER_PACKET.read_text(encoding="utf-8")

    required_core = (
        "ProtocolOutcomeLane(P) =",
        "entries         = every SessionContext or PublicParameter binding b of P",
        "run_established = every SessionContext or PublicParameter binding b of P",
        "requires\n`run_established` to be empty as its own premise",
        "what a Fresh challenge is drawn from is bound to that\ncoordinate by Analysis as a named premise",
    )
    required_fs = (
        "SamplingInputTypes(c) =",
        "The admitted acceptance ABI is exactly",
        "ChallengeNamespaceOctets(T, c, i)",
        "state update is committed after the length check and before acceptance",
        "AdmitTranscriptConstruction(candidate, AdmittedCore)",
    )
    required_interface = (
        "one `CoreTerminal(t)` entry exists for every and only `TerminalRef`",
        "a canonical-framed FS Protocol has exactly one interpretation-failure entry",
        "for every\nchallenge, a transport entry whose destination is `ExternalApplication` for\nevery occurrence whose value is an operand of that challenge's",
        "including the occurrence of every prior joint member",
    )
    required_analysis = (
        "AnalysisPIRFreshSourceSlotFragment = CanonicalSeq",
        "AFKCanonicalFramedAdditionalSourceSlotCatalog = CanonicalConcat",
        "both entry sequences must be\nbyte-identical and contain exactly every `PublicParameter` and `SessionContext`",
        "retains the\ntruth and exact PIR-to-experiment correspondence of the Fresh uniform independent\nchallenge distribution as explicit premises",
        "### 3.2 Named premises of the relation-bound Fresh question",
        "FreshPublicCoinDistributionPremise(",
        "ProviderOutcomeCarrierPremise(",
        "with the mass of `Unmodelled` lanes and of missing runs left where it\nis",
        "never by\nrenormalizing over the lanes the provider models",
    )
    if any(token not in core for token in required_core):
        raise CheckFailure("interactive Core owner clauses drifted")
    if any(token not in fs for token in required_fs):
        raise CheckFailure("canonical-framed owner clauses drifted")
    if any(token not in interface for token in required_interface):
        raise CheckFailure("Interface owner clauses drifted")
    if any(token not in analysis for token in required_analysis):
        raise CheckFailure("cryptographic-property owner clauses drifted")
    premise_grammar = analysis_model[
        analysis_model.index("AnalysisNamedPremiseKind =") :
        analysis_model.index("AnalysisReadPurposeRequirement =")
    ]
    _require(
        all(
            token in premise_grammar
            for token in (
                "AnalysisNamedPremiseRequirement =",
                "AnalysisProviderOutcomeCarrierMapBody",
                "FreshChallengeOnly",
                "RebindRequired",
                "HypothesisNodeRequirement",
                "AffirmativeJudgmentCapabilityRequirement",
                "ExactQuantifiedWitnessRequirement",
            )
        ),
        "Analysis premise-requirement grammar drifted",
    )
    _require(
        "IntakeAnalysisNamedPremises(" in analysis_model,
        "Analysis named-premise intake drifted",
    )
    property_section_three = analysis[
        analysis.index("## 3. Relation-bound Fresh special soundness") :
        analysis.index("## 4. Classical adaptive Fiat--Shamir experiment")
    ]
    _require(
        "analysis.distribution-profile" in analysis_profile["supported_subject_kinds"]
        and "AnalysisDistributionProfileId(" not in property_section_three,
        "the Boolean Fresh distribution declaration boundary changed",
    )
    _require(
        "**Authority:** None." in provider_packet
        and "map `Accepted -> Image(true)`, `Rejected ->\n   Image(false)`"
        in provider_packet
        and "OperationalNoncompletion -> Unmodelled" in provider_packet,
        "provider carrier decision packet drifted",
    )
    return {
        "interactive_core_sha256": hashlib.sha256(CORE_PAGE.read_bytes()).hexdigest(),
        "fiat_shamir_sha256": hashlib.sha256(FS_PAGE.read_bytes()).hexdigest(),
        "interfaces_and_plans_sha256": hashlib.sha256(
            INTERFACE_PAGE.read_bytes()
        ).hexdigest(),
        "cryptographic_properties_sha256": hashlib.sha256(
            ANALYSIS_PAGE.read_bytes()
        ).hexdigest(),
        "analysis_model_sha256": hashlib.sha256(
            ANALYSIS_MODEL_PAGE.read_bytes()
        ).hexdigest(),
        "analysis_property_profile_sha256": hashlib.sha256(
            ANALYSIS_PROFILE.read_bytes()
        ).hexdigest(),
        "provider_carrier_packet_sha256": hashlib.sha256(
            PROVIDER_PACKET.read_bytes()
        ).hexdigest(),
        "provider_carrier_packet_authority": "None",
        "named_premise_owner_constructor_present": True,
        "provider_map_section_present": True,
        "uniform_boolean_fresh_profile_declared": False,
    }


def _compact_setup(evidence: dict[str, Any]) -> dict[str, Any]:
    return {
        subject: {
            interpretation: {
                "view_id": view["view_id"],
                "body_sha256": view["body_sha256"],
                "entry_sequence_sha256": view["entry_sequence_sha256"],
                "entry_binding_refs": [item["binding_ref"] for item in view["entries"]],
                "run_established": view["run_established"],
            }
            for interpretation, view in pair.items()
        }
        for subject, pair in evidence.items()
    }


def _evidence_control(observed: dict[str, Any], source: dict[str, Any]) -> dict[str, Any]:
    runtime = observed["runtime"]
    sampling_failure = runtime["fiat_shamir"]["selected_sampling_failure"]
    presentation = runtime["fiat_shamir"]["sampling_failure_presentation"]
    return {
        "question": observed["question"],
        "source": source,
        "admission": observed["admission"],
        "subjects": observed["subjects"],
        "interaction_view_sha256": observed["interaction_view_sha256"],
        "canonical_view_sha256": observed["canonical_view_sha256"],
        "analysis_read_join": observed["analysis_read_join"],
        "public_setup": _compact_setup(observed["public_setup"]),
        "fixed_setup": observed["fixed_setup"],
        "interface": observed["interface"],
        "interface_negative": observed["interface_negative"],
        "runtime": {
            "fresh": runtime["fresh"],
            "fiat_shamir": {
                key: value
                for key, value in runtime["fiat_shamir"].items()
                if key
                not in {
                    "selected_sampling_failure",
                    "sampling_failure_presentation",
                }
            },
            "sampling_failure_variant": sampling_failure["variant"],
            "sampling_failure_case": sampling_failure["record"]["case"],
            "sampling_failure_completion_fields": sorted(
                presentation["completion_fields"]
            ),
            "sampling_failure_derived_draws_sha256": presentation[
                "derived_draws_sha256"
            ],
        },
        "analysis_boundary": observed["analysis_boundary"],
        "analysis_requirement_sequence_sha256": _digest(
            observed["analysis_boundary"]["premise_requirement_sequence"]
        ),
        "provider_map": observed["provider_map"],
    }


def evaluate() -> tuple[list[Finding], dict[str, Any]]:
    source = _source_gate()
    model = _load("_zkc_end_to_end_pressure_model", MODEL)
    observed = model.evidence()

    _require(observed["question"] == model.QUESTION, "exact question drifted")
    admission = observed["admission"]
    _require(
        all(item["outcome"] == "Affirmative" for item in admission.values()),
        "one owner admission stage did not close",
    )
    baseline = observed["subjects"]["baseline"]
    _require(
        baseline["occurrence_count"] == 10
        and baseline["binding_classes"] == ["STATEMENT", "SESSION_CONTEXT"]
        and baseline["binding_scopes"] == [1, 1]
        and baseline["binding_sources"] == ["PublicInput(0)", "PublicInput(0)"]
        and baseline["challenge_type_names"] == ["Boolean", "RootNat(2)"]
        and baseline["challenge_correlations"]
        == ["IndependentCorrelation", "IndependentCorrelation"]
        and baseline["challenge_condition_occurrences"] == [2, 2]
        and baseline["challenge_positions"] == [3, 4]
        and baseline["draw_bounds"] == [[8, 1], [8, 2]]
        and baseline["decoder_result_types_distinct"]
        and baseline["guarded_verifier_occurrence"] == 1
        and baseline["terminal_occurrences"] == [8, 9]
        and baseline["terminal_precedence"] == "first-active"
        and baseline["public_coin_eligible"],
        "mixed subject shape drifted",
    )
    _require(
        observed["subjects"]["run_variant"]["binding_sources"]
        == ["PublicInput(0)", "OccurrenceOutput(0,0)"],
        "run-established setup variant drifted",
    )
    _require(
        len(observed["interaction_view_sha256"]) == 6,
        "six Interaction views were not issued",
    )
    _require(
        len(observed["canonical_view_sha256"]) == 4,
        "four canonical-framed views were not issued",
    )
    _require(
        observed["analysis_read_join"]["slot_count"] == 13,
        "Analysis owner-read join is incomplete",
    )
    setup = observed["public_setup"]
    _require(
        setup["baseline"]["fresh"]["run_established"] == []
        and [item["binding_ref"] for item in setup["baseline"]["fresh"]["entries"]]
        == [1]
        and setup["run_variant"]["fresh"]["entries"] == []
        and setup["run_variant"]["fresh"]["run_established"] == [1],
        "public-setup partition drifted",
    )
    _require(
        observed["fixed_setup"]["baseline"]["outcome"] == "Affirmative"
        and observed["fixed_setup"]["run_variant"]["outcome"] == "Refused",
        "fixed-setup formation partition drifted",
    )
    _require(
        observed["interface"]["outcome"] == "Affirmative"
        and observed["interface"]["transport_occurrences"] == list(range(7)),
        "complete Interface did not admit",
    )
    _require(
        observed["interface_negative"]
        == {
            "outcome": "Refused",
            "code": "F0V4-R-INTERFACE-REPLAY-INPUT",
            "admission_item": 6,
            "missing_occurrences": [2],
            "transport_occurrences": [0, 1, 3, 4, 5, 6],
        },
        "missing replay-input transport did not refuse at item 6",
    )
    fresh = observed["runtime"]["fresh"]
    _require(
        fresh["run_count"] == 486
        and fresh["replay_match_count"] == 486
        and fresh["lane_counts"]
        == {
            "Accepted": 81,
            "Rejected": 405,
            "Aborted": 0,
            "InterpretationFailed": 0,
            "StrategyStopped": 0,
            "OperationalNoncompletion": 0,
        },
        "Fresh exhaustive execution or replay drifted",
    )
    fs = observed["runtime"]["fiat_shamir"]
    _require(
        fs["run_count"] == 81
        and fs["replay_match_count"] == 81
        and fs["lane_counts"]
        == {
            "Accepted": 21,
            "Rejected": 42,
            "Aborted": 0,
            "InterpretationFailed": 18,
            "StrategyStopped": 0,
            "OperationalNoncompletion": 0,
        },
        "Fiat-Shamir finite execution or replay drifted",
    )
    _require(
        fs["selected_sampling_failure"]["variant"] == "InterpretationFailure"
        and fs["sampling_failure_presentation"]["replay_from_presented_values"]
        and fs["sampling_failure_presentation"]["replay_operand_occurrences"] == [2]
        and fs["sampling_failure_presentation"]["unpresented_later_value_mutations"]
        == 9
        and sorted(fs["sampling_failure_presentation"]["completion_fields"])
        == [
            "challenge",
            "domain_payload",
            "final_state",
            "prefix_receipt_count",
            "prefix_state",
        ],
        "sampling-failure completion presentation drifted",
    )
    boundary = observed["analysis_boundary"]
    chain = boundary["named_premise_chain"]
    _require(
        boundary["fresh_law_leaf_count"] == 2
        and boundary["unique_fresh_law_coordinate_count"] == 2
        and boundary["fixture_fresh_law_matches"] == [1]
        and boundary["fixture_fresh_law_unmatched"] == [0]
        and not boundary["fixture_subject_matches_current"]
        and len(boundary["premise_requirement_sequence"]) == 8
        and len(boundary["canonical_requirement_slots"]) == 8
        and set(boundary["canonical_requirement_slots"])
        == {
            "challenge-law-0",
            "challenge-law-1",
            "outcome-carrier",
            "relation-predicate",
            "witness-type",
            "prover-private-state",
            "honest-commit",
            "honest-respond",
        }
        and boundary["fixture_rebind_required"]
        == [
            "relation-predicate",
            "witness-type",
            "prover-private-state",
            "honest-commit",
            "honest-respond",
        ]
        and boundary["missing"]
        == [
            "exact uniform Boolean distribution profile",
            "exact-subject relation and Plan rebind",
            "provider declaration",
        ],
        "Analysis premise boundary drifted",
    )
    _require(
        boundary["owner_boundary"]["named_requirement_variant_present"]
        and boundary["owner_boundary"][
            "cryptographic_properties_section_3_2_present"
        ]
        and boundary["z3_distribution_profile"]["support"] == [0, 1, 2]
        and boundary["z3_distribution_profile"]["point_mass"] == [1, 3]
        and boundary["z3_distribution_profile"]["profile_id"].startswith(
            "zkcidv0:analysis.distribution-profile:"
        )
        and boundary["z3_distribution_profile"]["premise_id"].startswith(
            "zkcidv0:analysis.named-premise:"
        )
        and not boundary["boolean_distribution_profile"]["declared"]
        and boundary["boolean_distribution_profile"]["profile_id"] is None
        and boundary["provider_requirement"]["formed"]
        and not boundary["provider_requirement"]["premise_formed"]
        and "published provider declaration"
        in boundary["provider_requirement"]["formation_error"],
        "Analysis premise formation drifted",
    )
    _require(
        chain["question_requirement_count"] == 8
        and chain["supplied_binding_count"] == 1
        and len(chain["supplied_premise_ids"]) == 1
        and set(chain["missing_slots"])
        == {
            "challenge-law-0",
            "outcome-carrier",
            "relation-predicate",
            "witness-type",
            "prover-private-state",
            "honest-commit",
            "honest-respond",
        }
        and chain["intake_outcome"] == "CannotAnswer"
        and chain["intake_code"] == "F0V2D2-C-MISSING-BINDING-KEY"
        and chain["first_unformed_stage"] == "analysis.goal"
        and all(
            chain[key] is None
            for key in (
                "goal_id",
                "hypothesis_context_id",
                "proposition_id",
                "support_instantiation_id",
                "judgment_record_id",
            )
        )
        and set(chain["rebind_probes"])
        == {
            "relation-predicate",
            "witness-type",
            "prover-private-state",
            "honest-commit",
            "honest-respond",
        }
        and all(
            item
            == {
                "outcome": "Refused",
                "code": "F0V2D2-R-REBIND-REQUIRED-SCOPE",
            }
            for item in chain["rebind_probes"].values()
        ),
        "named-premise intake stop or downstream non-formation drifted",
    )
    provider = observed["provider_map"]
    _require(
        provider["six_lane_map"]
        == {
            "Accepted": "Image(true)",
            "Rejected": "Image(false)",
            "Aborted": "Unmodelled",
            "InterpretationFailed": "Unmodelled",
            "StrategyStopped": "Unmodelled",
            "OperationalNoncompletion": "Unmodelled",
        }
        and provider["accepted_mass"] == [7, 27]
        and provider["transported_true_mass"] == [7, 27]
        and provider["unmodelled_mass"] == [2, 9]
        and not provider["renormalized"]
        and provider["finite_measure_clause_holds"]
        and not provider["provider_declaration_published"],
        "finite provider map or measure clause drifted",
    )

    findings = [
        Finding("exact-question", "Affirmative", "F0V4-A-EXACT-QUESTION"),
        Finding("core-admission", "Affirmative", "F0V4-A-CORE-ADMISSION"),
        Finding(
            "fresh-protocol-admission",
            "Affirmative",
            "F0V4-A-FRESH-PROTOCOL-ADMISSION",
        ),
        Finding(
            "construction-admission",
            "Affirmative",
            "F0V4-A-CONSTRUCTION-ADMISSION",
        ),
        Finding(
            "fiat-shamir-protocol-admission",
            "Affirmative",
            "F0V4-A-FS-PROTOCOL-ADMISSION",
        ),
        Finding(
            "checked-same-core-construction",
            "Affirmative",
            "F0V4-A-CHECKED-SAME-CORE",
        ),
        Finding(
            "six-interaction-static-views",
            "Affirmative",
            "F0V4-A-SIX-INTERACTION-VIEWS",
        ),
        Finding(
            "four-canonical-framed-views",
            "Affirmative",
            "F0V4-A-FOUR-CANONICAL-VIEWS",
        ),
        Finding(
            "analysis-read-catalog-join",
            "Affirmative",
            "F0V4-A-ANALYSIS-READ-JOIN",
        ),
        Finding(
            "two-public-setup-variants",
            "Affirmative",
            "F0V4-A-PUBLIC-SETUP-VIEWS",
        ),
        Finding(
            "fixed-setup-baseline",
            "Affirmative",
            "F0V4-A-FIXED-SETUP-FORMATION",
        ),
        Finding(
            "fixed-setup-run-established-variant",
            "Refused",
            "F0V4-R-FIXED-SETUP-RUN-ESTABLISHED",
        ),
        Finding(
            "complete-interface-admission",
            "Affirmative",
            "F0V4-A-INTERFACE-ADMISSION",
        ),
        Finding(
            "missing-replay-operand-transport",
            "Refused",
            "F0V4-R-INTERFACE-REPLAY-INPUT",
        ),
        Finding(
            "fresh-exhaustive-execution",
            "Affirmative",
            "F0V4-A-FRESH-EXECUTION",
        ),
        Finding(
            "fresh-independent-replay",
            "Affirmative",
            "F0V4-A-FRESH-REPLAY",
        ),
        Finding(
            "fiat-shamir-finite-execution",
            "Affirmative",
            "F0V4-A-FS-EXECUTION",
        ),
        Finding(
            "fiat-shamir-independent-replay",
            "Affirmative",
            "F0V4-A-FS-REPLAY",
        ),
        Finding(
            "sampling-failure-completion-presentation",
            "Affirmative",
            "F0V4-A-SAMPLING-FAILURE-PRESENTATION",
        ),
        Finding(
            "fresh-law-leaf-coordinates",
            "Affirmative",
            "F0V4-A-FRESH-LAW-COORDINATES",
        ),
        Finding(
            "boolean-distribution-profile",
            "CannotAnswer",
            "F0V4-C-BOOLEAN-DISTRIBUTION-PROFILE",
        ),
        Finding(
            "relation-and-plan-fixture-coordinates",
            "Affirmative",
            "F0V4-A-RELATION-PLAN-COORDINATES",
        ),
        Finding(
            "exact-subject-relation-and-plan-premises",
            "CannotAnswer",
            "F0V4-C-RELATION-PLAN-REBIND",
        ),
        Finding(
            "named-premise-owner-formation",
            "Affirmative",
            "F0V4-A-NAMED-PREMISE-OWNER-CONTRACT",
        ),
        Finding(
            "named-premise-intake-boundary",
            "Affirmative",
            "F0V4-A-NAMED-PREMISE-INTAKE-BOUNDARY",
        ),
        Finding(
            "provider-declaration",
            "CannotAnswer",
            "F0V4-C-PROVIDER-DECLARATION",
        ),
        Finding(
            "finite-six-lane-provider-map",
            "Affirmative",
            "F0V4-A-SIX-LANE-PROVIDER-MAP",
        ),
        Finding(
            "finite-measure-preservation",
            "Affirmative",
            "F0V4-A-MEASURE-PRESERVATION",
        ),
        Finding("end-to-end-composition", AGGREGATE_OUTCOME, AGGREGATE_CODE),
    ]
    finding_values = [item.value() for item in findings]
    report = {
        "aggregate": {
            "outcome": AGGREGATE_OUTCOME,
            "code": AGGREGATE_CODE,
        },
        "finding_codes": finding_values,
        "findings_sha256": _digest(finding_values),
        "evidence_control": _evidence_control(observed, source),
    }
    return findings, report


def _read_expected() -> dict[str, Any]:
    try:
        value = json.loads(EXPECTED.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise CheckFailure("cannot read frozen expected findings") from error
    if type(value) is not dict:
        raise CheckFailure("frozen expected findings root differs")
    return value


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    findings, report = evaluate()
    if args.check and report != _read_expected():
        print(
            json.dumps(
                {"expected": _read_expected(), "observed": report},
                indent=2,
                sort_keys=True,
            )
        )
        return 1
    counts: dict[str, int] = {}
    for finding in findings:
        counts[finding.outcome] = counts.get(finding.outcome, 0) + 1
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(
            f"{AGGREGATE_OUTCOME}/{AGGREGATE_CODE} "
            f"findings={len(findings)} outcomes={json.dumps(counts, sort_keys=True)}"
        )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (CheckFailure, OSError, ValueError) as error:
        print(f"F0V4-CHECK-FAIL: {error}", file=sys.stderr)
        raise SystemExit(1)
