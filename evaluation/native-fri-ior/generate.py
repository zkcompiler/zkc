#!/usr/bin/env python3
"""Owner-local construction check for the frozen public FRI/IOR artifacts."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any, TypeVar

from friiormodel.classical import (
    build_honest_classical_case,
    verify_committed_fiat_shamir as verify_classical_fiat_shamir,
    verify_committed_fresh as verify_classical_fresh,
    verify_native_trace as verify_classical_native,
)
from friiormodel.classical_fixtures import (
    parse_classical_owner_generation,
    parse_classical_replay_policy,
)
from friiormodel.commitment import CommitmentTree, build_commitment
from friiormodel.committed import verify_committed_fri
from friiormodel.fixtures import (
    MAX_FIXTURE_BYTES,
    LoadedFixture,
    bind_repository_root,
    load_fixture,
    parse_expected_projection,
    parse_private_generation,
    parse_public_inputs,
    parse_public_native_vector,
    parse_public_proof,
    parse_relation_initial_oracle,
    parse_replay_policy,
)
from friiormodel.constructions import (
    CheckedCommittedToWorkFreshRun,
    CheckedConstructionComposition,
    CheckedNativeToCommittedFreshRun,
    compose_checked_constructions,
    generate_committed_to_work_fresh,
    generate_native_to_committed_fresh,
)
from friiormodel.generation import (
    CheckedNativeToCommittedExecution,
    PrivateFriGenerationMaterial,
    generate_honest_native_to_committed_execution,
)
from friiormodel.relations import (
    CheckedFriRelationGrounding,
    RelationStatementOccurrence,
    canonical_relation_grounding_request,
    check_fri_relation_grounding,
)
from friiormodel.field import Fp, Fp2
from friiormodel.native import DeclaredStrategyDependency, LogicalOracle, NativeFriTrace
from friiormodel.profile import D0, D1, DEFAULT_VALIDATION_LIMITS, EXACT_PROFILE
from friiormodel.proof import (
    CommittedFriPublicInputs,
    OccurrenceSelector,
    OpeningTableEntry,
    PublicFriProof,
)
from friiormodel.report import (
    PUBLIC_CASES,
    _build_public_report_from_loaded,
    _verify_public_report_from_loaded,
    _source_basis,
    build_public_report,
    canonical_pretty_json,
    expected_projection,
    verify_public_report,
)
from friiormodel.provenance import (
    artifact_content_id,
    canonical_json_content_id,
    load_bounded_json_bytes,
)
from friiormodel.subjects import CHECKED_FIAT_SHAMIR_CONSTRUCTION
from friiormodel.terms import (
    CheckResult,
    ModelFailure,
    OutcomeClass,
    ResourceCounter,
)
from friiormodel.transcript import (
    CANONICAL_CONSTRUCTION_PLAN,
    FiatShamirTranscript,
    construct_fiat_shamir_transcript,
    derive_fiat_shamir_transcript,
)


DEFAULT_ROOT = Path(__file__).resolve().parents[2]
PUBLIC_STATEMENT = {
    "schema": "zkc.fri-ior.statement.v1",
    "profile": "f97-binary-two-round",
    "initial_oracle_role": "relation-supplied",
}
PUBLIC_APPLICATION_CONTEXT = {
    "application": "native-fri-ior-validation",
    "case": "primary",
    "suffix": 71394,
}

ReceiptT = TypeVar("ReceiptT")

_OWNER_RESULT_CONTRACTS = {
    "concrete_fiat_shamir_execution": (
        CheckedNativeToCommittedExecution,
        "FRI-IOR-GENERATION-100",
        "generation:concrete-construction-check",
    ),
    "native_to_committed_fresh": (
        CheckedNativeToCommittedFreshRun,
        "FRI-IOR-CONSTRUCTION-101",
        "constructions:native-to-committed-fresh",
    ),
    "committed_to_work_fresh": (
        CheckedCommittedToWorkFreshRun,
        "FRI-IOR-CONSTRUCTION-103",
        "constructions:committed-to-work-fresh",
    ),
    "construction_composition": (
        CheckedConstructionComposition,
        "FRI-IOR-CONSTRUCTION-104",
        "constructions:composition",
    ),
    "relation_grounding": (
        CheckedFriRelationGrounding,
        "FRI-IOR-RELATION-102",
        "relations:fri-grounding",
    ),
}
_NEGATIVE_RESULT_CONTRACTS = {
    "authenticated-fold-inconsistency": "FRI-IOR-COMMITTED-020",
    "fold-consistent-terminal-degree-excess": "FRI-IOR-COMMITTED-022",
}
_EXACT_CLASSICAL_OWNER_RESULT_CODES = {
    "native": "FRI-IOR-CLASSICAL-NATIVE-100",
    "fresh": "FRI-IOR-CLASSICAL-COMMITTED-100",
    "fiat_shamir": "FRI-IOR-CLASSICAL-COMMITTED-100",
}


def _require_receipt(
    admission: object,
    attribute: str,
    label: str,
    expected_type: type[ReceiptT],
    expected_code: str,
    expected_boundary: str,
) -> tuple[ReceiptT, CheckResult]:
    result = getattr(admission, "result", None)
    receipt = getattr(admission, attribute, None)
    if not isinstance(result, CheckResult):
        raise RuntimeError(f"{label} refused: missing-result")
    if result.outcome is not OutcomeClass.AFFIRMATIVE or receipt is None:
        raise RuntimeError(f"{label} refused: {result.code}")
    if (
        result.code != expected_code
        or result.boundary != expected_boundary
        or not isinstance(receipt, expected_type)
        or result.subject != receipt.identity
    ):
        raise RuntimeError(
            f"{label} returned an unbound or unexpected receipt: {result.code}"
        )
    return receipt, result


def _configured_public_inputs() -> CommittedFriPublicInputs:
    """Form the fixed public case without treating its output fixture as input."""

    return CommittedFriPublicInputs(
        EXACT_PROFILE,
        CANONICAL_CONSTRUCTION_PLAN,
        PUBLIC_STATEMENT,
        PUBLIC_APPLICATION_CONTEXT,
    )


def _owner_material(root: Path) -> PrivateFriGenerationMaterial:
    loaded = load_fixture(
        root,
        "evaluation/native-fri-ior/cases/owner-generation-input.json",
        "owner_generation_input",
    )
    private = parse_private_generation(loaded.value)
    return PrivateFriGenerationMaterial(
        private.coefficients,
        private.initial_layer_salts,
        private.first_fold_layer_salts,
    )


def _dependency_term(
    dependency: DeclaredStrategyDependency | None,
) -> dict[str, Any] | None:
    if dependency is None:
        return None
    return {
        "subject": dependency.subject,
        "authored_at": dependency.authored_at,
        "declared_read_set": list(dependency.declared_read_set),
    }


def _oracle_fixture_term(oracle: LogicalOracle) -> dict[str, Any]:
    return {
        "name": oracle.name,
        "domain": oracle.domain.name,
        "origin": oracle.origin.value,
        "publication_mode": oracle.publication_mode.value,
        "entries": [
            {"point": entry.point.value, "value": entry.value.to_term()}
            for entry in oracle.entries
        ],
        "declared_strategy_dependency": _dependency_term(
            oracle.declared_strategy_dependency
        ),
    }


def _native_vector_term(trace: NativeFriTrace) -> dict[str, Any]:
    return {
        "schema": "zkc.native-fri-ior.public-native-vector.v1",
        "disclosure": {
            "classification": "declassified-validation-only-complete-trace",
            "permitted_consumers": ["native-execution", "relations-grounding"],
            "forbidden_consumer": "committed-verifier",
            "establishes_confidentiality": False,
        },
        "profile": trace.profile.to_term(),
        "initial_oracle": _oracle_fixture_term(trace.initial_oracle),
        "first_challenge": {
            "name": trace.first_challenge.name,
            "value": trace.first_challenge.value.to_term(),
        },
        "prover_oracle": _oracle_fixture_term(trace.prover_oracle),
        "second_challenge": {
            "name": trace.second_challenge.name,
            "value": trace.second_challenge.value.to_term(),
        },
        "terminal": {
            "coefficients": [
                coefficient.to_term() for coefficient in trace.terminal.coefficients
            ],
            "declared_strategy_dependency": _dependency_term(
                trace.terminal.declared_strategy_dependency
            ),
        },
        "query_draws": [
            {
                "ordinal": draw.ordinal,
                "initial_domain_index": draw.initial_domain_index,
            }
            for draw in trace.query_draws
        ],
        "events": [
            {
                "index": event.index,
                "kind": event.kind.value,
                "subject": event.subject,
            }
            for event in trace.events
        ],
        "structural_chain": trace.structural_chain.to_term(),
        "native_trace_id": trace.identity.to_term(),
    }


def _fold_coefficients(
    coefficients: tuple[Fp2, ...], challenge: Fp2
) -> tuple[Fp2, ...]:
    if len(coefficients) % 2:
        raise RuntimeError("fixture coefficient count must be even")
    return tuple(
        coefficients[index] + challenge * coefficients[index + 1]
        for index in range(0, len(coefficients), 2)
    )


def _require_transcript(candidate: object, label: str) -> FiatShamirTranscript:
    if not isinstance(candidate, FiatShamirTranscript):
        code = candidate.code if isinstance(candidate, CheckResult) else "wrong-carrier"
        raise RuntimeError(f"{label} refused: {code}")
    return candidate


def _proof_from_trees(
    tree0: CommitmentTree,
    tree1: CommitmentTree,
    transcript: FiatShamirTranscript,
) -> PublicFriProof:
    keys = tuple(
        sorted(
            {
                key
                for occurrence in transcript.query_occurrences
                for key in (
                    (0, occurrence.initial_domain_index % (D0.order // 2)),
                    (1, occurrence.initial_domain_index % (D1.order // 2)),
                )
            }
        )
    )
    opening_table = tuple(
        OpeningTableEntry(
            layer,
            (tree0 if layer == 0 else tree1).open_pair(pair_index),
        )
        for layer, pair_index in keys
    )
    table_index = {entry.key: index for index, entry in enumerate(opening_table)}
    selectors = tuple(
        OccurrenceSelector(
            occurrence.ordinal,
            table_index[(0, occurrence.initial_domain_index % (D0.order // 2))],
            table_index[(1, occurrence.initial_domain_index % (D1.order // 2))],
        )
        for occurrence in transcript.query_occurrences
    )
    return PublicFriProof(
        tree0.cap,
        tree1.cap,
        transcript.terminal_coefficients,
        transcript.grinding_nonce,
        opening_table,
        selectors,
    )


def _proof_for_terminal(
    public_inputs: CommittedFriPublicInputs,
    tree0: CommitmentTree,
    tree1: CommitmentTree,
    terminal: tuple[Fp2, ...],
) -> tuple[PublicFriProof, FiatShamirTranscript]:
    transcript = _require_transcript(
        construct_fiat_shamir_transcript(
            public_inputs.transcript_plan,
            public_inputs.statement,
            public_inputs.application_context,
            tree0.cap,
            tree1.cap,
            terminal,
            ResourceCounter(DEFAULT_VALIDATION_LIMITS),
        ),
        "negative-fixture transcript construction",
    )
    return _proof_from_trees(tree0, tree1, transcript), transcript


def _negative_proof_terms(
    public_inputs: CommittedFriPublicInputs,
    material: PrivateFriGenerationMaterial,
    trace: NativeFriTrace,
    positive_proof: PublicFriProof,
) -> dict[str, Any]:
    tree0 = build_commitment(
        D0,
        tuple(entry.value for entry in trace.initial_oracle.entries),
        material.initial_layer_salts,
    )
    first_fold_values = [entry.value for entry in trace.prover_oracle.entries]
    first_fold_values[0] = first_fold_values[0] + Fp2(Fp(1), Fp(0))
    inconsistent_tree1 = build_commitment(
        D1,
        tuple(first_fold_values),
        material.first_fold_layer_salts,
    )
    provisional = _require_transcript(
        construct_fiat_shamir_transcript(
            public_inputs.transcript_plan,
            public_inputs.statement,
            public_inputs.application_context,
            tree0.cap,
            inconsistent_tree1.cap,
            (Fp2.zero(),),
            ResourceCounter(DEFAULT_VALIDATION_LIMITS),
        ),
        "inconsistent-fold provisional transcript construction",
    )
    first_fold_coefficients = _fold_coefficients(
        material.coefficients, provisional.beta0
    )
    inconsistent_terminal = _fold_coefficients(
        first_fold_coefficients, provisional.beta1
    )
    inconsistent_proof, _ = _proof_for_terminal(
        public_inputs,
        tree0,
        inconsistent_tree1,
        inconsistent_terminal,
    )

    terminal = positive_proof.terminal_coefficients
    if len(terminal) != 2:
        raise RuntimeError("the exact positive terminal must have two coefficients")
    one = Fp2(Fp(1), Fp(0))
    zero = Fp2.zero()
    excessive_terminal = (terminal[0] - one, terminal[1], zero, zero, one)
    positive_tree1 = build_commitment(
        D1,
        tuple(entry.value for entry in trace.prover_oracle.entries),
        material.first_fold_layer_salts,
    )
    excessive_proof, _ = _proof_for_terminal(
        public_inputs,
        tree0,
        positive_tree1,
        excessive_terminal,
    )
    cases = {
        "authenticated-fold-inconsistency": inconsistent_proof,
        "fold-consistent-terminal-degree-excess": excessive_proof,
    }
    for name, proof in cases.items():
        result = verify_committed_fri(
            public_inputs,
            proof,
            ResourceCounter(DEFAULT_VALIDATION_LIMITS),
        )
        if (
            result.outcome is not OutcomeClass.REFUSED
            or result.code != _NEGATIVE_RESULT_CONTRACTS[name]
        ):
            raise RuntimeError(
                f"negative fixture {name} reached {result.outcome.value}/{result.code}"
            )
    return {
        "schema": "zkc.native-fri-ior.public-negative-proofs.v1",
        "cases": {name: proof.to_term() for name, proof in cases.items()},
        "nonclaims": [
            "these examples do not establish completeness of the refusal taxonomy"
        ],
    }


def build_frozen_fixture_candidates(root: Path) -> dict[str, dict[str, Any]]:
    """Construct all derived fixtures without reading their frozen outputs."""

    root = bind_repository_root(root)
    material = _owner_material(root)
    public_inputs = _configured_public_inputs()
    policy = parse_replay_policy(
        load_fixture(
            root,
            "evaluation/native-fri-ior/cases/replay-policy.json",
            "replay_policy",
        ).value
    )
    concrete_execution, _ = _require_receipt(
        generate_honest_native_to_committed_execution(
            material,
            public_inputs,
            policy,
        ),
        "checked_execution",
        "concrete Fiat--Shamir generation",
        *_OWNER_RESULT_CONTRACTS["concrete_fiat_shamir_execution"],
    )
    proof = concrete_execution.public_artifacts.proof
    trace = concrete_execution.candidate.source_trace
    earlier = {
        "public-inputs.json": public_inputs.to_term(),
        "public-proof.json": proof.to_term(),
        "public-native-vector.json": _native_vector_term(trace),
        "public-negative-proofs.json": _negative_proof_terms(
            public_inputs,
            material,
            trace,
            proof,
        ),
    }
    return {**earlier, **build_exact_classical_frozen_fixture_candidates(root)}


def build_exact_classical_frozen_fixture_candidates(
    root: Path,
) -> dict[str, dict[str, Any]]:
    """Generate the exact public packet solely from its owner-authored input."""

    root = bind_repository_root(root)
    owner = parse_classical_owner_generation(
        load_fixture(
            root,
            (
                "evaluation/native-fri-ior/cases/"
                "exact-classical-owner-generation-input.json"
            ),
            "exact_classical_owner_generation_input",
        ).value
    )
    case = build_honest_classical_case(
        source_coefficients=owner.source_coefficients,
        salt_seed=owner.salt_seed,
    )
    return {
        "exact-classical-public-inputs.json": (
            case.fiat_shamir_run.public_inputs.to_term()
        ),
        "exact-classical-public-proof.json": case.fiat_shamir_run.proof.to_term(),
    }


_DERIVED_PUBLIC_CASES = {
    "public_inputs": "public-inputs.json",
    "public_proof": "public-proof.json",
    "public_native_vector": "public-native-vector.json",
    "negative_proofs": "public-negative-proofs.json",
    "exact_classical_public_inputs": "exact-classical-public-inputs.json",
    "exact_classical_public_proof": "exact-classical-public-proof.json",
}


def _loaded_candidate_fixture(
    role: str, relative_path: str, value: dict[str, Any]
) -> LoadedFixture:
    raw = canonical_pretty_json(value)
    parsed = load_bounded_json_bytes(raw, maximum=MAX_FIXTURE_BYTES)
    if parsed != value:
        raise RuntimeError("derived fixture changed under bounded JSON replay")
    return LoadedFixture(
        role,
        relative_path,
        artifact_content_id(raw),
        canonical_json_content_id(value),
        parsed,
        raw,
    )


def _candidate_public_fixture_set(
    root: Path, candidates: dict[str, dict[str, Any]]
) -> dict[str, LoadedFixture]:
    """Combine derived terms with separately authored public report inputs."""

    if set(candidates) != set(_DERIVED_PUBLIC_CASES.values()):
        raise RuntimeError("derived fixture candidate set is incomplete")
    loaded: dict[str, LoadedFixture] = {}
    for role, relative_path in PUBLIC_CASES.items():
        derived_name = _DERIVED_PUBLIC_CASES.get(role)
        loaded[role] = (
            _loaded_candidate_fixture(role, relative_path, candidates[derived_name])
            if derived_name is not None
            else load_fixture(root, relative_path, role)
        )
    return loaded


def _write_fixture(root: Path, name: str, value: dict[str, Any]) -> None:
    cases = root / "evaluation/native-fri-ior/cases"
    target = cases / name
    temporary = cases / f".{name}.new"
    temporary.write_bytes(canonical_pretty_json(value))
    temporary.replace(target)


def refreeze_frozen_fixtures(root: Path) -> dict[str, object]:
    """Refreeze reviewed vectors after two deterministic in-memory derivations.

    Each file replacement is atomic.  The corpus is intentionally not described
    as crash-atomic: Git remains the recovery boundary if the authoring process
    is interrupted between replacements.  The non-mutating checker below is the
    normal verification path.
    """

    root = bind_repository_root(root)
    # This relation-side operand is deliberately not generated from the
    # construction trace.  It must already exist as a separately maintained
    # owner-local source and pass its strict authority parser.
    parse_relation_initial_oracle(
        load_fixture(
            root,
            "evaluation/native-fri-ior/cases/owner-relation-input.json",
            "owner_relation_input",
        ).value
    )
    first = build_frozen_fixture_candidates(root)
    second = build_frozen_fixture_candidates(root)
    if {name: canonical_pretty_json(value) for name, value in first.items()} != {
        name: canonical_pretty_json(value) for name, value in second.items()
    }:
        raise RuntimeError("two fresh fixture derivations were not byte deterministic")
    loaded = _candidate_public_fixture_set(root, first)
    report = _build_public_report_from_loaded(root, loaded)
    if not _verify_public_report_from_loaded(root, report, loaded):
        raise RuntimeError("candidate public report did not verify")
    owner_summary = _build_owner_local_report_from_terms(
        root,
        first["public-inputs.json"],
        first["public-proof.json"],
        first["public-native-vector.json"],
        first["exact-classical-public-inputs.json"],
        first["exact-classical-public-proof.json"],
    )
    expected = {
        "schema": "zkc.native-fri-ior.expected-report-projection.v3",
        "authority": "regression-golden-not-semantic-or-provenance-authority",
        "projection": expected_projection(report),
    }
    parse_expected_projection(expected)
    for name, value in first.items():
        _write_fixture(root, name, value)
    _write_fixture(root, "expected-results.json", expected)
    return owner_summary


def check_frozen_fixtures(root: Path) -> dict[str, object]:
    """Re-derive every reviewed vector and golden without changing the checkout."""

    root = bind_repository_root(root)
    first = build_frozen_fixture_candidates(root)
    second = build_frozen_fixture_candidates(root)
    encoded_first = {
        name: canonical_pretty_json(value) for name, value in first.items()
    }
    encoded_second = {
        name: canonical_pretty_json(value) for name, value in second.items()
    }
    if encoded_first != encoded_second:
        raise RuntimeError("two fresh fixture derivations were not byte deterministic")
    for name, expected_bytes in encoded_first.items():
        frozen = load_fixture(
            root,
            f"evaluation/native-fri-ior/cases/{name}",
            f"frozen_{name.removesuffix('.json').replace('-', '_')}",
        )
        if frozen.raw != expected_bytes:
            raise RuntimeError(f"reviewed fixture is stale: {name}")

    report = build_public_report(root)
    if not verify_public_report(root, report):
        raise RuntimeError("public report rebuilt from reviewed fixtures did not verify")
    expected = parse_expected_projection(
        load_fixture(
            root,
            "evaluation/native-fri-ior/cases/expected-results.json",
            "expected_results",
        ).value
    )
    if expected_projection(report) != expected["projection"]:
        raise RuntimeError("reviewed report projection is stale")
    return build_owner_local_report(root)


def _build_exact_classical_owner_summary(
    root: Path,
    public_inputs_value: object,
    public_proof_value: object,
) -> dict[str, object]:
    """Reconstruct the exact packet without exporting owner generation values."""

    owner_fixture = load_fixture(
        root,
        (
            "evaluation/native-fri-ior/cases/"
            "exact-classical-owner-generation-input.json"
        ),
        "exact_classical_owner_generation_input",
    )
    policy_fixture = load_fixture(
        root,
        "evaluation/native-fri-ior/cases/exact-classical-replay-policy.json",
        "exact_classical_replay_policy",
    )
    owner = parse_classical_owner_generation(owner_fixture.value)
    limits = parse_classical_replay_policy(policy_fixture.value)
    case = build_honest_classical_case(
        source_coefficients=owner.source_coefficients,
        salt_seed=owner.salt_seed,
    )
    if case.fiat_shamir_run.public_inputs.to_term() != public_inputs_value:
        raise RuntimeError(
            "exact classical owner generation differs from frozen public inputs"
        )
    if case.fiat_shamir_run.proof.to_term() != public_proof_value:
        raise RuntimeError(
            "exact classical owner generation differs from frozen public proof"
        )
    checked = {
        "native": verify_classical_native(case.native_trace, limits),
        "fresh": verify_classical_fresh(
            case.fresh_run.public_inputs,
            case.fresh_run.proof,
            case.fresh_run.fold_challenges,
            case.fresh_run.query_indices,
            limits,
        ),
        "fiat_shamir": verify_classical_fiat_shamir(
            case.fiat_shamir_run.public_inputs,
            case.fiat_shamir_run.proof,
            limits,
        ),
    }
    for name, result in checked.items():
        if (
            result.outcome is not OutcomeClass.AFFIRMATIVE
            or result.code != _EXACT_CLASSICAL_OWNER_RESULT_CODES[name]
        ):
            raise RuntimeError(
                f"exact classical {name} owner check refused: {result.code}"
            )
    return {
        "outcome": "Affirmative",
        "public_inputs_id": case.fiat_shamir_run.public_inputs.identity.to_term(),
        "public_proof_id": case.fiat_shamir_run.proof.identity.to_term(),
        "checked_results": {
            name: result.code for name, result in checked.items()
        },
        "generation_input_binding": {
            "path": owner_fixture.relative_path,
            "artifact_content_id": str(owner_fixture.artifact_id),
            "canonical_content_id": str(owner_fixture.canonical_id),
            "authority": "owner-generation-input-not-public-report-input",
        },
        "validation_source_basis_id": _source_basis(
            root,
            "exact-classical-owner-generation",
            ("classical.py", "classical_fixtures.py", "../generate.py"),
        ),
        "scope": "one-deterministically-regenerated-exact-classical-control",
        "nonclaims": [
            "source-theorem-correspondence",
            "fri-proximity-or-security-theorem",
            "commitment-binding",
            "fiat-shamir-security",
            "secure-or-confidential-owner-randomness",
        ],
    }


def _build_owner_local_report_from_terms(
    root: Path,
    public_inputs_value: object,
    public_proof_value: object,
    public_native_vector_value: object,
    exact_classical_public_inputs_value: object,
    exact_classical_public_proof_value: object,
) -> dict[str, object]:
    """Check owner-local capabilities against one explicit public candidate set."""

    root = bind_repository_root(root)
    private_fixture = load_fixture(
        root,
        "evaluation/native-fri-ior/cases/owner-generation-input.json",
        "owner_generation_input",
    )
    policy_fixture = load_fixture(
        root,
        "evaluation/native-fri-ior/cases/replay-policy.json",
        "replay_policy",
    )
    relation_fixture = load_fixture(
        root,
        "evaluation/native-fri-ior/cases/owner-relation-input.json",
        "owner_relation_input",
    )
    private = parse_private_generation(private_fixture.value)
    frozen_public_inputs = parse_public_inputs(public_inputs_value)
    public_inputs = _configured_public_inputs()
    if public_inputs.to_term() != frozen_public_inputs.to_term():
        raise RuntimeError(
            "configured public case differs from the frozen public inputs"
        )
    expected_proof = parse_public_proof(public_proof_value)
    expected_native_trace = parse_public_native_vector(public_native_vector_value)
    relation_initial_oracle = parse_relation_initial_oracle(relation_fixture.value)
    limits = parse_replay_policy(policy_fixture.value)
    material = PrivateFriGenerationMaterial(
        private.coefficients,
        private.initial_layer_salts,
        private.first_fold_layer_salts,
    )

    concrete_execution, concrete_result = _require_receipt(
        generate_honest_native_to_committed_execution(material, public_inputs, limits),
        "checked_execution",
        "concrete Fiat--Shamir generation",
        *_OWNER_RESULT_CONTRACTS["concrete_fiat_shamir_execution"],
    )
    generated = concrete_execution.public_artifacts
    generated_native_trace = concrete_execution.candidate.source_trace
    if (
        generated.public_inputs.to_term() != public_inputs.to_term()
        or generated.proof.to_term() != expected_proof.to_term()
    ):
        raise RuntimeError(
            "owner-local generation differs from the frozen public artifacts"
        )
    if generated_native_trace != expected_native_trace:
        raise RuntimeError(
            "owner-local generation differs from the frozen public native vector"
        )

    transcript = derive_fiat_shamir_transcript(
        public_inputs.transcript_plan,
        public_inputs.statement,
        public_inputs.application_context,
        expected_proof.cap0,
        expected_proof.cap1,
        expected_proof.terminal_coefficients,
        expected_proof.grinding_nonce,
        ResourceCounter(limits),
    )
    if not isinstance(transcript, FiatShamirTranscript):
        raise RuntimeError(f"Fiat--Shamir reconstruction refused: {transcript.code}")
    ordered_draws = tuple(
        occurrence.initial_domain_index for occurrence in transcript.query_occurrences
    )
    commitment_receipt, commitment_result = _require_receipt(
        generate_native_to_committed_fresh(
            material,
            public_inputs.statement,
            public_inputs.application_context,
            transcript.beta0,
            transcript.beta1,
            ordered_draws,
            limits,
        ),
        "checked_receipt",
        "native-to-committed Fresh construction",
        *_OWNER_RESULT_CONTRACTS["native_to_committed_fresh"],
    )
    grinding_receipt, grinding_result = _require_receipt(
        generate_committed_to_work_fresh(
            commitment_receipt,
            transcript.work_seed,
            expected_proof.grinding_nonce,
            limits,
        ),
        "checked_receipt",
        "committed-to-work Fresh construction",
        *_OWNER_RESULT_CONTRACTS["committed_to_work_fresh"],
    )
    composition_receipt, composition_result = _require_receipt(
        compose_checked_constructions(
            commitment_receipt,
            grinding_receipt,
            CHECKED_FIAT_SHAMIR_CONSTRUCTION,
            concrete_execution,
            limits,
        ),
        "checked_receipt",
        "construction composition",
        *_OWNER_RESULT_CONTRACTS["construction_composition"],
    )

    statement = RelationStatementOccurrence(
        public_inputs.profile.identity,
        0,
        public_inputs.statement,
    )
    grounding_request = canonical_relation_grounding_request(
        statement,
        relation_initial_oracle,
        commitment_receipt,
        composition_receipt,
        public_inputs,
        expected_proof,
    )
    grounding_receipt, grounding_result = _require_receipt(
        check_fri_relation_grounding(
            grounding_request,
            relation_initial_oracle,
            commitment_receipt,
            composition_receipt,
            public_inputs,
            expected_proof,
            limits,
        ),
        "checked_grounding",
        "relation grounding",
        *_OWNER_RESULT_CONTRACTS["relation_grounding"],
    )

    exact_classical = _build_exact_classical_owner_summary(
        root,
        exact_classical_public_inputs_value,
        exact_classical_public_proof_value,
    )

    return {
        "schema": "zkc.native-fri-ior.owner-local-construction-check.v2",
        "outcome": "Affirmative",
        "public_inputs_id": generated.public_inputs.identity.to_term(),
        "public_proof_id": generated.proof.identity.to_term(),
        "native_trace_id": generated_native_trace.identity.to_term(),
        "checked_results": {
            "concrete_fiat_shamir_execution": concrete_result.code,
            "native_to_committed_fresh": commitment_result.code,
            "committed_to_work_fresh": grinding_result.code,
            "construction_composition": composition_result.code,
            "relation_grounding": grounding_result.code,
        },
        "checked_capability_ids": {
            "concrete_fiat_shamir_execution": concrete_execution.identity.to_term(),
            "native_to_committed_fresh": commitment_receipt.identity.to_term(),
            "committed_to_work_fresh": grinding_receipt.identity.to_term(),
            "construction_composition": composition_receipt.identity.to_term(),
            "relation_grounding": grounding_receipt.identity.to_term(),
        },
        "semantic_result_ids": {
            "relation_grounding": grounding_receipt.semantic_grounding_id.to_term(),
            "relation_occurrence_map": grounding_receipt.occurrence_map_identity.to_term(),
        },
        "relation_input_binding": {
            "path": relation_fixture.relative_path,
            "artifact_content_id": str(relation_fixture.artifact_id),
            "canonical_content_id": str(relation_fixture.canonical_id),
            "authority": (
                "separately-loaded-owner-input; does-not-establish-independent-provenance"
            ),
        },
        "exact_classical_control": exact_classical,
        "scope": "one-owner-local-finite-execution-and-live-capability-chain",
        "nonclaims": [
            "general-commitment-compiler-correctness",
            "fri-proximity-or-security-theorem",
            "fiat-shamir-security-theorem",
            "outer-computation-relation",
            "statement-to-oracle-predicate-satisfaction",
            "independent-provenance-of-the-separately-supplied-relation-oracle",
        ],
    }


def build_owner_local_report(root: Path) -> dict[str, object]:
    """Reconstruct every private construction capability without exporting it."""

    root = bind_repository_root(root)
    public = {
        role: load_fixture(root, PUBLIC_CASES[role], role).value
        for role in (
            "public_inputs",
            "public_proof",
            "public_native_vector",
            "exact_classical_public_inputs",
            "exact_classical_public_proof",
        )
    }
    return _build_owner_local_report_from_terms(
        root,
        public["public_inputs"],
        public["public_proof"],
        public["public_native_vector"],
        public["exact_classical_public_inputs"],
        public["exact_classical_public_proof"],
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=DEFAULT_ROOT)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument(
        "--refreeze-fixtures",
        action="store_true",
        help="rebuild derived public fixtures and freeze the report golden last",
    )
    mode.add_argument(
        "--check-fixtures",
        action="store_true",
        help="re-derive and compare all reviewed fixtures without writing files",
    )
    args = parser.parse_args(argv)
    try:
        if args.refreeze_fixtures:
            summary = refreeze_frozen_fixtures(args.root)
        elif args.check_fixtures:
            summary = check_frozen_fixtures(args.root)
        else:
            summary = build_owner_local_report(args.root)
        sys.stdout.write(
            json.dumps(summary, ensure_ascii=True, sort_keys=True, indent=2) + "\n"
        )
        return 0
    except (ModelFailure, OSError, RuntimeError) as error:
        sys.stderr.write(f"owner-local generation check failed: {error}\n")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
