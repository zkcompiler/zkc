"""Deterministic public report for the finite construction falsifier."""

from __future__ import annotations

from pathlib import Path
import re
from typing import Any

from .construction import (
    construction_id,
    core_id,
    finite_source_applicability,
    parse_construction,
    protocol_id,
)
from .diagnostics import CorrespondenceMismatch, MalformedInput
from .execution import (
    independent_replay,
    parse_public_inputs,
    parse_public_proof,
    project_instance,
    replay,
)
from .mutations import transition_mutation_kills
from .provenance import (
    load_fixture,
    source_manifest,
    validation_basis_id,
)
from .terms import canonical_json_bytes, evidence_id, framed_hash
from .transition import (
    RATE,
    absorb,
    squeeze,
    start,
)


REPORT_SCHEMA = "zkc.duplex-sponge-transcript.public-report.v1"
EXPECTED_SCHEMA = "zkc.duplex-sponge-transcript.expected-results.v1"
CONSTRUCTION_PATH = "evaluation/duplex-sponge-transcript/cases/construction.json"
PUBLIC_INPUT_PATH = "evaluation/duplex-sponge-transcript/cases/public-inputs.json"
PUBLIC_PROOF_PATH = "evaluation/duplex-sponge-transcript/cases/public-proof.json"
SOURCE_LEDGER_PATH = "evaluation/duplex-sponge-transcript/cases/source-ledger.json"
EXPECTED_PATH = "evaluation/duplex-sponge-transcript/cases/expected-results.json"

NONCLAIMS = (
    "cryptographic security of the toy hash or permutation",
    "realization of an ideal random function or ideal random permutation",
    "uniform salt generation",
    "duplex Fiat-Shamir soundness, knowledge soundness, or zero knowledge",
    "state-restoration security",
    "ROM, QROM, or UC security",
    "production ciphersuite or endpoint format",
    "durable PIR ABI or compiler implementation support",
)

LEDGER_ANCHORS = {
    "chiesa-orru-duplex-fiat-shamir-2025-536": {
        "kind": "ResearchPaper",
        "url": "https://eprint.iacr.org/2025/536",
        "status": "primary-source-correspondence-input-not-theorem-authority",
        "reviewed_role": (
            "Construction 3.3 transition semantics and Definitions 4.1-4.2 "
            "plus Construction 4.3 transform shape"
        ),
    },
    "cfrg-fiat-shamir-draft-03": {
        "kind": "InternetDraft",
        "url": (
            "https://www.ietf.org/archive/id/"
            "draft-irtf-cfrg-fiat-shamir-03.html"
        ),
        "status": "work-in-progress-comparison-input",
        "reviewed_role": (
            "strict parsing and operational comparison only; not "
            "duplex-construction source authority"
        ),
    },
}
LEDGER_BOUNDARY = {
    "alphabet": "Sigma5 with no field semantics",
    "provider": "deterministic finite transition provider",
    "security_claim": False,
    "source_authentication": False,
    "claim": (
        "finite state-transition, structural-admission, source-applicability, "
        "identity, and replay falsification only"
    ),
}


def _case(
    *,
    subject: str,
    basis: str,
    outcome: str,
    code: str,
    detail: str,
    evidence: Any,
) -> dict[str, Any]:
    payload = {
        "outcome": outcome,
        "code": code,
        "detail": detail,
        "evidence": evidence,
    }
    return {
        "subject": subject,
        "validation_basis_id": basis,
        **payload,
        "evidence_id": evidence_id(subject, basis, payload),
    }


def _edge_evidence(construction: Any, inputs: Any) -> dict[str, Any]:
    oracle = construction.provider_semantics.forward_oracle()
    initial = start(oracle, project_instance(construction, inputs))
    after_salt = absorb(oracle, initial, (2, 4)).state
    before_first_challenge = absorb(
        oracle, after_salt, (3, 1)
    ).state
    partial = squeeze(oracle, before_first_challenge, 2)
    zero = squeeze(oracle, partial.state, 0)
    empty = absorb(oracle, partial.state, ())
    after_empty = squeeze(oracle, empty.state, 1)
    overwritten = absorb(oracle, partial.state, (4,))
    one = squeeze(oracle, before_first_challenge, 1)
    then_three = squeeze(oracle, one.state, 3)
    four = squeeze(oracle, before_first_challenge, 4)
    fill_base = absorb(oracle, initial, (1, 2)).state
    filled = absorb(oracle, fill_base, (3,))
    after_full = absorb(oracle, filled.state, (4,))
    if zero.state != partial.state or zero.output or zero.permutation_calls != 0:
        raise CorrespondenceMismatch("zero squeeze was not the exact identity")
    if (
        empty.state.cells != partial.state.cells
        or empty.state.absorb_index != partial.state.absorb_index
    ):
        raise CorrespondenceMismatch("empty absorb changed cells or absorb index")
    if empty.state.squeeze_index != RATE or after_empty.permutation_calls != 1:
        raise CorrespondenceMismatch("empty absorb failed to reset squeeze state")
    if one.output + then_three.output != four.output or then_three.state != four.state:
        raise CorrespondenceMismatch("adjacent squeezes restarted instead of continuing")
    if overwritten.state.cells[0] != 4 or overwritten.permutation_calls != 0:
        raise CorrespondenceMismatch("partial-squeeze absorption was not overwrite mode")
    if filled.permutation_calls != 0 or filled.state.absorb_index != RATE:
        raise CorrespondenceMismatch("filled rate segment permuted eagerly")
    if after_full.permutation_calls != 1:
        raise CorrespondenceMismatch("next absorption did not permute a full rate segment")
    return {
        "zero_squeeze_state": zero.state.to_term(),
        "empty_absorb_state": empty.state.to_term(),
        "post_empty_squeeze": list(after_empty.output),
        "partial_overwrite_state": overwritten.state.to_term(),
        "adjacent_output": list(one.output + then_three.output),
        "concatenated_output": list(four.output),
        "filled_rate_state": filled.state.to_term(),
        "next_absorb_permutation_calls": after_full.permutation_calls,
    }


def validate_source_ledger(value: Any) -> None:
    if type(value) is not dict or set(value) != {"schema", "entries", "fixture_boundary"}:
        raise MalformedInput("source ledger has the wrong exact shape")
    if value["schema"] != "zkc.duplex-sponge-transcript.source-ledger.v1":
        raise MalformedInput("source-ledger schema differs")
    if type(value["entries"]) is not list or len(value["entries"]) != len(
        LEDGER_ANCHORS
    ):
        raise MalformedInput("source ledger must name its exact two metadata anchors")
    seen: dict[str, dict[str, Any]] = {}
    for entry in value["entries"]:
        if type(entry) is not dict or set(entry) != {
            "id",
            "kind",
            "title",
            "revision",
            "url",
            "sha256",
            "reviewed_role",
            "status",
        }:
            raise MalformedInput("source-ledger entry keys differ")
        if any(type(entry[key]) is not str or not entry[key] for key in entry):
            raise MalformedInput("source-ledger entry values must be nonempty strings")
        if re.fullmatch(r"[0-9a-f]{64}", entry["sha256"]) is None:
            raise MalformedInput("source-ledger digest must be lowercase SHA-256 hex")
        if entry["id"] in seen:
            raise MalformedInput("source-ledger identifiers must be unique")
        seen[entry["id"]] = entry
    if set(seen) != set(LEDGER_ANCHORS):
        raise MalformedInput("source-ledger anchor identifiers differ")
    for identifier, expected in LEDGER_ANCHORS.items():
        entry = seen[identifier]
        if any(entry[key] != value for key, value in expected.items()):
            raise MalformedInput("source-ledger anchor role or routing differs")
    if len(seen) != len(LEDGER_ANCHORS):
        raise MalformedInput("source-ledger identifiers must be unique")
    boundary = value["fixture_boundary"]
    if type(boundary) is not dict or boundary != LEDGER_BOUNDARY:
        raise MalformedInput(
            "source ledger must retain its exact inert-metadata boundary"
        )


def build_report(repo_root: Path) -> dict[str, Any]:
    construction_binding = load_fixture(
        repo_root, CONSTRUCTION_PATH, role="public-construction-declaration"
    )
    input_binding = load_fixture(
        repo_root, PUBLIC_INPUT_PATH, role="public-runtime-instance"
    )
    proof_binding = load_fixture(repo_root, PUBLIC_PROOF_PATH, role="public-proof")
    ledger_binding = load_fixture(repo_root, SOURCE_LEDGER_PATH, role="public-source-ledger")
    validate_source_ledger(ledger_binding.value)
    construction = parse_construction(construction_binding.value)
    inputs = parse_public_inputs(input_binding.value)
    proof = parse_public_proof(proof_binding.value, construction, inputs)
    applicability = finite_source_applicability(construction)
    record = replay(construction, inputs, proof)
    independent = independent_replay(construction, inputs, proof)
    if independent.to_term() != record.to_term():
        raise CorrespondenceMismatch("independent public replay differs")
    mutation_kills = transition_mutation_kills(
        construction,
        inputs,
        proof,
        record.challenges,
    )
    if not all(mutation_kills.values()):
        survivors = sorted(name for name, killed in mutation_kills.items() if not killed)
        raise CorrespondenceMismatch(
            f"source-law transition mutations survived: {', '.join(survivors)}"
        )
    manifest = source_manifest(repo_root)
    public_fixtures = (
        construction_binding,
        input_binding,
        proof_binding,
        ledger_binding,
    )
    basis = validation_basis_id(manifest, public_fixtures)
    core = core_id(construction.core)
    construction_subject = construction_id(construction)
    fresh = protocol_id(construction, "Fresh")
    duplex = protocol_id(construction, "DuplexSponge")
    if fresh == duplex:
        raise CorrespondenceMismatch("Fresh and duplex Protocol identities aliased")
    edges = _edge_evidence(construction, inputs)
    execution_subject = framed_hash(
        "zkc.duplex-sponge-transcript.execution",
        (
            duplex.encode("ascii"),
            canonical_json_bytes(inputs.semantic_term()),
            canonical_json_bytes(proof.to_term()),
        ),
    )
    cases = {
        "construction/structural-admission": _case(
            subject=construction_subject,
            basis=basis,
            outcome="Affirmative",
            code="DUPLEX-STRUCTURAL-CONSTRUCTION-ADMITTED",
            detail=(
                "closed construction, typed root binding, and exact total "
                "occurrence maps structurally admit"
            ),
            evidence={
                "core_id": core,
                "message_codec_count": len(construction.message_codecs),
                "challenge_decoder_count": len(construction.challenge_decoders),
                "non_claim": (
                    "generic PIR admission does not establish codec injectivity "
                    "or provider bijectivity"
                ),
            },
        ),
        "construction/finite-source-applicability": _case(
            subject=construction_subject,
            basis=basis,
            outcome="Affirmative",
            code="DUPLEX-FINITE-SOURCE-APPLICABLE",
            detail=(
                "the selected finite provider, codecs, and decoders satisfy "
                "the source-profile side conditions"
            ),
            evidence=applicability,
        ),
        "transition/source-edges": _case(
            subject=construction_subject,
            basis=basis,
            outcome="Affirmative",
            code="DUPLEX-TRANSITION-EDGES",
            detail=(
                "source-sensitive empty, zero, boundary, overwrite, and "
                "continuation edges reproduce"
            ),
            evidence=edges,
        ),
        "transition/source-law-mutations": _case(
            subject=construction_subject,
            basis=basis,
            outcome="Affirmative",
            code="DUPLEX-TRANSITION-MUTATIONS-KILLED",
            detail="source-law substitutions differ on frozen finite witnesses",
            evidence={
                "killed": sorted(mutation_kills),
                "survived": [],
                "non_claim": "not mutation completeness or cryptographic evidence",
            },
        ),
        "execution/public-replay": _case(
            subject=execution_subject,
            basis=basis,
            outcome="Affirmative",
            code="DUPLEX-PUBLIC-REPLAY",
            detail=(
                "public verifier derives every challenge from runtime "
                "instance, salt, and messages"
            ),
            evidence={
                "challenges": [
                    list(value) if type(value) is tuple else value
                    for value in record.challenges
                ],
                "trace_events": len(record.trace),
                "permutation_calls": record.total_permutation_calls,
            },
        ),
        "execution/independent-replay": _case(
            subject=execution_subject,
            basis=basis,
            outcome="Affirmative",
            code="DUPLEX-INDEPENDENT-REPLAY",
            detail="separately coded literal transition replay agrees exactly",
            evidence={"exact_record_equality": True},
        ),
        "identity/same-core-distinct-protocols": _case(
            subject=duplex,
            basis=basis,
            outcome="Affirmative",
            code="DUPLEX-SAME-CORE-SEPARATION",
            detail=(
                "Fresh and duplex interpretations retain one Core and "
                "distinct Protocol identities"
            ),
            evidence={
                "core_id": core,
                "fresh_protocol_id": fresh,
                "duplex_protocol_id": duplex,
            },
        ),
        "analysis/security-nonpromotion": _case(
            subject=duplex,
            basis=basis,
            outcome="CannotAnswer",
            code="DUPLEX-SECURITY-NOT-ESTABLISHED",
            detail=(
                "transition conformance and a toy bijection cannot establish "
                "a duplex Fiat-Shamir theorem"
            ),
            evidence={"missing": list(NONCLAIMS[:6])},
        ),
    }
    body = {
        "schema": REPORT_SCHEMA,
        "scope": {
            "claim": (
                "finite source-transition, structural-admission, and "
                "applicability falsification"
            ),
            "provider": "DeterministicTransitionConformanceOnly",
        },
        "semantic_roots": {
            "core_id": core,
            "construction_id": construction_subject,
            "fresh_protocol_id": fresh,
            "duplex_protocol_id": duplex,
        },
        "public_fixtures": [fixture.public_term() for fixture in public_fixtures],
        "source_manifest": list(manifest),
        "validation_basis_id": basis,
        "execution": record.to_term(),
        "cases": cases,
        "nonclaims": list(NONCLAIMS),
    }
    return {
        **body,
        "report_id": framed_hash(
            "zkc.duplex-sponge-transcript.report", (canonical_json_bytes(body),)
        ),
    }


def verify_report(report: Any, repo_root: Path) -> list[str]:
    expected_keys = {
        "schema",
        "scope",
        "semantic_roots",
        "public_fixtures",
        "source_manifest",
        "validation_basis_id",
        "execution",
        "cases",
        "nonclaims",
        "report_id",
    }
    if type(report) is not dict or set(report) != expected_keys:
        return ["public report keys differ"]
    if "overall_pass" in report:
        return ["public report must not carry an overall-pass assertion"]
    try:
        rebuilt = build_report(repo_root)
    except Exception as error:  # verification reports typed rebuild failures
        return [f"public report rebuild failed: {type(error).__name__}: {error}"]
    return [] if rebuilt == report else ["public report differs from exact rebuild"]


def expected_projection(report: dict[str, Any]) -> dict[str, Any]:
    return {
        "schema": EXPECTED_SCHEMA,
        "semantic_roots": report["semantic_roots"],
        "validation_basis_id": report["validation_basis_id"],
        "cases": {
            name: {
                "outcome": case["outcome"],
                "code": case["code"],
                "evidence_id": case["evidence_id"],
            }
            for name, case in report["cases"].items()
        },
        "execution_challenges": report["execution"]["challenges"],
        "execution_permutation_calls": report["execution"][
            "total_permutation_calls"
        ],
        "report_id": report["report_id"],
    }
