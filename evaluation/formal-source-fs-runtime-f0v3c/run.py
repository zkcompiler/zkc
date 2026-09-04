#!/usr/bin/env python3
"""Check the admitted finite canonical-framed execution subjects."""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import asdict, dataclass
import hashlib
import json
from pathlib import Path
import sys
from typing import Any

import executor
import model
import replay
import views


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
EXPECTED_FINDINGS = HERE / "expected-findings.json"
EXPECTED_RUNS = HERE / "expected-runs.json"
EXPECTED_VECTORS = HERE / "derivation-vectors.json"
EXPECTED_ONE_SHOT_RUNS = HERE / "expected-runs-one-shot.json"
EXPECTED_ONE_SHOT_VECTORS = HERE / "derivation-vectors-one-shot.json"
FS_PAGE = ROOT / "docs-next/pir/fiat-shamir.md"
CORE_PAGE = ROOT / "docs-next/pir/interactive-core.md"


class CheckFailure(RuntimeError):
    """The finite package, owner source, or frozen evidence drifted."""


@dataclass(frozen=True)
class Finding:
    name: str
    outcome: str
    code: str
    detail: str


def _wire(value: Any) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("ascii")


def _digest(value: Any) -> str:
    return hashlib.sha256(_wire(value)).hexdigest()


def _read_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise CheckFailure(f"cannot read {path.relative_to(ROOT)}") from error


def _source_gate() -> dict[str, Any]:
    fs = FS_PAGE.read_text(encoding="utf-8")
    core = CORE_PAGE.read_text(encoding="utf-8")
    required = (
        "this profile fixes\nits declaration body: exactly the companion page's",
        "one nonempty semantic symbol and no other",
        "a declaration with any other shape is `Malformed`",
        'ProtocolDeclarationRef<"pir.fs-application-domain">',
        "ChallengeNamespaceOctets(T, c, i)",
        "FSSamplingFailureReceipt = {",
        "FS replay recomputes initialization, every frame, namespace",
        "CanonicalFramedExecutionViewBody = {",
    )
    if any(token not in fs for token in required):
        raise CheckFailure("a required canonical-framed owner clause drifted")
    companion_clause = "NominalProtocolDeclarationBody = MetaRecord {"
    if companion_clause not in core:
        raise CheckFailure("the companion nominal declaration body drifted")
    return {
        "fiat_shamir_sha256": hashlib.sha256(FS_PAGE.read_bytes()).hexdigest(),
        "interactive_core_sha256": hashlib.sha256(CORE_PAGE.read_bytes()).hexdigest(),
        "owner_coordinate": (
            "docs-next/pir/fiat-shamir.md Section 2 and "
            "docs-next/pir/interactive-core.md Section 2"
        ),
    }


def _case_summary(result: executor.ExecutionResult) -> list[Any]:
    return [
        result.case.name,
        result.lane,
        executor.record_digest(result.record),
        _digest(result.transcript_prefix),
        result.derived,
    ]


def _draw_result(result: executor.ExecutionResult) -> dict[str, Any]:
    body = result.record["record"]
    if result.lane == "InterpretationFailed":
        receipt = body["interpretation_receipt"]["receipt"]
        return {
            "kind": "exhaustion",
            "draw_count": len(receipt["draws"]),
        }
    receipt = body["challenge_receipts"][0]["receipt"]
    return {
        "kind": "value",
        "value": result.derived["value"],
        "draw_count": len(receipt["draws"]),
    }


def _vectors(subject: model.Subject, results: list[executor.ExecutionResult]) -> dict[str, Any]:
    by_prefix: dict[tuple[int, tuple[str, ...]], executor.ExecutionResult] = {}
    for result in results:
        key = (result.case.statement, result.transcript_prefix)
        previous = by_prefix.setdefault(key, result)
        if previous.derived != result.derived:
            raise CheckFailure("one exact transcript prefix derived two results")
    fixed_frames = results[0].transcript_prefix[:4]
    statement_frames: dict[str, str] = {}
    commitment_frames: dict[str, str] = {}
    entries = []
    for (statement, prefix), result in sorted(
        by_prefix.items(), key=lambda item: (item[0][0], item[0][1])
    ):
        if prefix[:4] != fixed_frames:
            raise CheckFailure("the finite prefix basis is not common")
        statement_frames.setdefault(str(statement), prefix[4])
        commitment_frames.setdefault(str(result.case.commitment), prefix[5])
        entries.append(
            {
                "input": {
                    "challenge": 0,
                    "statement": statement,
                    "commitment": result.case.commitment,
                    "transcript_prefix_sha256": _digest(prefix),
                },
                "output": _draw_result(result),
            }
        )
    if len(entries) != 9:
        raise CheckFailure("finite derivation domain is not the expected nine prefixes")
    return {
        "format": "zkc.formal-source-fs-runtime.derivation-vectors.v1",
        "core_id": model.identifier_text(subject.construction.core_id),
        "transcript_construction_id": model.identifier_text(
            subject.construction.identifier
        ),
        "application_domain_status": "owner-determined",
        "prefix_encoding": {
            "ordered_parts": [
                "fixed_frames",
                "statement_frames[statement]",
                "commitment_frames[commitment]",
            ],
            "fixed_frames": list(fixed_frames),
            "statement_frames": statement_frames,
            "commitment_frames": commitment_frames,
        },
        "challenge_value_type": model.canonical_value_json(
            model.k1.admit_value(model.Z3, model.k1.Nat(0))
        )["value_type"],
        "sampling_failure_type": model.k1.encode_datum(
            model.k1.semantic_failure_type_datum(
                subject.construction.sampling_exhausted_failure
            )
        ).hex(),
        "sampling_failure_payload": model.canonical_value_json(
            model.k1.admit_value(
                subject.construction.sampling_exhausted_failure.payload_type,
                model.k1.DatumRecord(
                    (
                        (0, model.k1.Nat(0)),
                        (
                            1,
                            model.k1.Nat(
                                subject.construction.challenge_rules[0].maximum_draws
                            ),
                        ),
                    )
                ),
            )
        ),
        "entries": entries,
    }


def _run_corpus(subject: model.Subject) -> tuple[list[executor.ExecutionResult], int]:
    results: list[executor.ExecutionResult] = []
    replay_matches = 0
    for case in executor.all_cases():
        generated = executor.execute(subject, case)
        replay_lane, replay_transitions = replay.replay(
            subject, asdict(case), generated.record
        )
        if replay_lane != generated.lane:
            raise CheckFailure(f"replay lane mismatch for {case.name}")
        if replay_transitions != generated.transition_receipts:
            raise CheckFailure(f"replay transition mismatch for {case.name}")
        replay_matches += 1
        results.append(generated)
    return results, replay_matches


def _mutation_gate(
    subject: model.Subject, result: executor.ExecutionResult
) -> int:
    cases = []
    extra = dict(result.record)
    extra["surplus"] = None
    cases.append(extra)
    missing = json.loads(json.dumps(result.record))
    del missing["record"]["protocol_id"]
    cases.append(missing)
    wrong_variant = json.loads(json.dumps(result.record))
    wrong_variant["variant"] = "InterpretationFailure"
    cases.append(wrong_variant)
    killed = 0
    for mutation in cases:
        try:
            replay.replay(subject, asdict(result.case), mutation)
        except replay.ReplayMismatch:
            killed += 1
    if killed != len(cases):
        raise CheckFailure("replay accepted a record field-set mutation")
    return killed


def _expected_runs(results: list[executor.ExecutionResult]) -> dict[str, Any]:
    return {
        "format": "zkc.formal-source-fs-runtime.expected-runs.v1",
        "record_fields": [
            "case_name",
            "outcome_lane",
            "completed_record_sha256",
            "transcript_prefix_sha256",
            "derived_result",
        ],
        "records": [_case_summary(result) for result in results],
    }


def _subject_evidence(
    subject: model.Subject,
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    if subject.admission_outcome != "Affirmative":
        raise CheckFailure(f"{subject.name} subject is not owner-admitted")
    view_digests, missing_view_coordinates = views.validate_against_predecessor(
        subject
    )
    execution_view_digest = None
    if not missing_view_coordinates:
        execution_view_digest = _digest(views.execution_view(subject))
    results, replay_matches = _run_corpus(subject)
    if len(results) != 54 or replay_matches != 54:
        raise CheckFailure(f"the {subject.name} corpus or replay count drifted")

    lanes = Counter(result.lane for result in results)
    lane_counts = {
        lane: lanes.get(lane, 0)
        for lane in (
            "Accepted",
            "Rejected",
            "Aborted",
            "InterpretationFailed",
            "StrategyStopped",
            "OperationalNoncompletion",
        )
    }
    if sum(lane_counts.values()) != 54:
        raise CheckFailure(f"the {subject.name} lane partition is not total")

    mutation_kills = _mutation_gate(subject, results[0])
    vectors = _vectors(subject, results)
    runs = _expected_runs(results)
    algorithm_preimages = {
        algorithm.algorithm_kind.value: {
            "id": model.identifier_text(algorithm.identity),
            "preimage_sha256": hashlib.sha256(
                model.k1.algorithm_preimage(algorithm)
            ).hexdigest(),
            "evaluation_contract": model.identifier_text(
                model.EVALUATION_CONTRACT.identity
            ),
        }
        for algorithm in subject.algorithms
    }
    controls = {
        "name": subject.name,
        "core_id": model.identifier_text(subject.construction.core_id),
        "fresh_protocol_id": model.identifier_text(
            subject.admitted_fresh_protocol.protocol_id
        ),
        "transcript_construction_id": model.identifier_text(
            subject.construction.identifier
        ),
        "fs_protocol_id": model.identifier_text(subject.fs_protocol.identifier),
        "canonical_framed_profile_digest": subject.construction.profile_id.digest.hex(),
        "application_module_id": model.identifier_text(
            subject.application_module.identity
        ),
        "portable_algorithms": algorithm_preimages,
        "checked_conclusion": subject.checked.conclusion,
        "occurrence_map_count": len(subject.checked.occurrence_map),
        "value_map_count": len(subject.checked.value_map),
        "challenge_map_count": len(subject.checked.challenge_map),
        "maximum_draws": subject.construction.challenge_rules[0].maximum_draws,
        "run_count": len(results),
        "honest_run_count": len(executor.honest_cases()),
        "verifier_input_count": len(executor.verifier_cases()),
        "replay_match_count": replay_matches,
        "replay_mutation_kills": mutation_kills,
        "lane_counts": lane_counts,
        "sampling_exhaustions": lane_counts["InterpretationFailed"],
        "derivation_vector_count": len(vectors["entries"]),
        "expected_runs_sha256": _digest(runs),
        "derivation_vectors_sha256": _digest(vectors),
        "construction_view_sha256": view_digests,
        "underdetermined_challenge_view_coordinates": list(
            missing_view_coordinates
        ),
        "execution_view_sha256": execution_view_digest,
    }
    return controls, runs, vectors


def evaluate() -> tuple[
    dict[str, Any],
    dict[str, Any],
    dict[str, Any],
    dict[str, Any],
    dict[str, Any],
]:
    source = _source_gate()
    retrying = model.make_subject("retrying")
    one_shot = model.make_subject("one-shot")
    retrying_controls, retrying_runs, retrying_vectors = _subject_evidence(
        retrying
    )
    one_shot_controls, one_shot_runs, one_shot_vectors = _subject_evidence(
        one_shot
    )
    if one_shot_controls["sampling_exhaustions"] != 0:
        raise CheckFailure("the always-accept one-shot construction exhausted")
    portable_projection = views.validate_portable_projection_suite()
    controls = {
        **source,
        "portable_projection_suite": portable_projection,
        "subjects": {
            "retrying": retrying_controls,
            "one_shot": one_shot_controls,
        },
    }

    findings = [
        Finding(
            "admission",
            "Affirmative",
            "F0V3C-A-OWNER-ADMISSION",
            one_shot.admission_detail,
        ),
        Finding(
            "retrying-execution",
            "Affirmative",
            "F0V3C-A-FINITE-EXECUTION",
            "all 54 retrying runs completed in the six-lane partition, including "
            f"{retrying_controls['sampling_exhaustions']} measured sampling exhaustions",
        ),
        Finding(
            "one-shot-execution",
            "Affirmative",
            "F0V3C-A-ONE-SHOT-EXECUTION",
            "all 54 always-accept one-shot runs completed without sampling exhaustion",
        ),
        Finding(
            "replay",
            "Affirmative",
            "F0V3C-A-INDEPENDENT-REPLAY",
            "the independent path matched 108 records and transitions and rejected three exact-field mutations for each subject",
        ),
        Finding(
            "views",
            "CannotAnswer",
            "F0V3C-C-UNFRAMED-CHALLENGE-POSITION",
            "the repaired owner body requires the challenge occurrence's frame_schedule position, but each Schnorr challenge is Always with no condition frame and therefore has no frame_schedule entry; the three determined construction values validate under both predecessor compilers",
        ),
        Finding(
            "portable-view-pressure",
            "Affirmative",
            "F0V3C-A-REPAIRED-VIEW-PROJECTION",
            "one admitted two-binding, two-challenge Core projects two ordered rules with distinct decoder result types and draw bounds, two binding atoms at one opening, and one symbolic earlier-draw entry",
        ),
        Finding(
            "outcome-partition",
            "Affirmative",
            "F0V3C-A-SIX-LANE-PARTITION",
            "both measured six-lane partitions are total and exclusive",
        ),
        Finding(
            "derivation-function",
            "Affirmative",
            "F0V3C-A-DERIVATION-VECTORS",
            "each subject exports nine exact finite transcript-prefix derivations, with the one-shot table total on values",
        ),
        Finding(
            "aggregate",
            "CannotAnswer",
            "F0V3C-C-FS-RUNTIME",
            "the bounded execution, replay, partition, derivation, and repaired pressure projections close, but the owner text does not determine the Schnorr challenge-transition or execution-view frame coordinate",
        ),
    ]
    frozen_findings = {
        "aggregate": {"outcome": "CannotAnswer", "code": "F0V3C-C-FS-RUNTIME"},
        "cases": [
            {"name": item.name, "outcome": item.outcome, "code": item.code}
            for item in findings
        ],
        "evidence_control": controls,
    }
    return (
        frozen_findings,
        retrying_runs,
        retrying_vectors,
        one_shot_runs,
        one_shot_vectors,
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument(
        "--emit",
        choices=(
            "findings",
            "retrying-runs",
            "retrying-vectors",
            "one-shot-runs",
            "one-shot-vectors",
            "all",
        ),
    )
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    findings, runs, vectors, one_shot_runs, one_shot_vectors = evaluate()
    outputs = {
        "findings": findings,
        "retrying-runs": runs,
        "retrying-vectors": vectors,
        "one-shot-runs": one_shot_runs,
        "one-shot-vectors": one_shot_vectors,
    }
    if args.write:
        for path, value in (
            (EXPECTED_FINDINGS, findings),
            (EXPECTED_RUNS, runs),
            (EXPECTED_VECTORS, vectors),
            (EXPECTED_ONE_SHOT_RUNS, one_shot_runs),
            (EXPECTED_ONE_SHOT_VECTORS, one_shot_vectors),
        ):
            path.write_text(
                json.dumps(value, indent=2, sort_keys=True) + "\n",
                encoding="utf-8",
            )
    if args.emit:
        selected: Any = (
            outputs if args.emit == "all" else outputs[args.emit]
        )
        print(json.dumps(selected, indent=2, sort_keys=True))
        return 0
    if args.check:
        expected = (
            (_read_json(EXPECTED_FINDINGS), findings, "expected findings"),
            (_read_json(EXPECTED_RUNS), runs, "expected runs"),
            (_read_json(EXPECTED_VECTORS), vectors, "derivation vectors"),
            (
                _read_json(EXPECTED_ONE_SHOT_RUNS),
                one_shot_runs,
                "one-shot expected runs",
            ),
            (
                _read_json(EXPECTED_ONE_SHOT_VECTORS),
                one_shot_vectors,
                "one-shot derivation vectors",
            ),
        )
        for frozen, observed, label in expected:
            if frozen != observed:
                raise CheckFailure(f"{label} drifted")
    print(
        "CannotAnswer/F0V3C-C-FS-RUNTIME "
        f"runs={len(runs['records']) + len(one_shot_runs['records'])} "
        f"vectors={len(vectors['entries']) + len(one_shot_vectors['entries'])}"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except CheckFailure as error:
        print(f"F0V3C-CHECK-FAIL: {error}", file=sys.stderr)
        raise SystemExit(1)
