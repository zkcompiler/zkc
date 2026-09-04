"""Build and verify P01's public-only Phase B evidence artifact.

The report is reconstructed from exact public fixture bytes and the source
files loaded by this checkout. It publishes semantic subjects, exact artifact
content identities, validation-basis identities, and evidence-record identities
in distinct fields. It never opens the owner-local generation sidecar and it
accepts no expected-result oracle while it is being built.

This remains a finite executable witness. Public replay, exhaustive toy-field
enumeration, and a second byte reconstruction do not establish a cryptographic
security theorem or confidential prover-generation replay.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from pathlib import Path
import sys
from typing import Any, Mapping

from . import analysis as analysis_module
from . import diagnostics as diagnostics_module
from . import execution as execution_module
from . import independent as independent_module
from . import interface as interface_module
from . import provenance as provenance_module
from . import relations as relations_module
from . import semantic as semantic_module
from . import terms as terms_module
from .analysis import (
    ApplicabilityClaim,
    SchnorrTranscript,
    TranscriptFork,
    check_accepting_transcript,
    check_special_soundness_fork,
    exhaustive_shvzk_distribution_equality,
    exhaustive_special_soundness,
    probe_analysis_applicability,
)
from .diagnostics import classification_summary
from .execution import (
    CheckedPublicExecution,
    FreshChallengeBinding,
    PortableExecutionRecord,
    PublicInvocation,
    PublicReplayRequest,
    PublicResourcePlan,
    build_evaluator_basis,
    build_portable_execution,
    check_checked_public_execution,
    check_fresh_public_execution,
    issue_relations_checked_statement,
    public_trace_value,
    qualify_public_execution,
)
from .independent import reconstruct_fs_v3
from .interface import (
    DecodedFSProof,
    FSExternalInputs,
    FSVerificationRecord,
    admit_fs_proof_interface,
    canonical_fs_proof_interface,
    check_fs_execution_projection,
    check_fs_proof,
    decode_fs_proof,
    evaluate_fs_proof,
    fs_proof_artifact_id,
)
from .provenance import (
    ArtifactContentId,
    EvidenceRecordId,
    SourceDeclaration,
    SourceManifest,
    ValidationBasisId,
    artifact_content_id,
    bind_loaded_root,
    build_source_manifest,
    canonical_json_bytes,
    evidence_record_id,
    load_bounded_json_bytes,
    load_public_fixture,
    validate_source_manifest,
)
from .relations import (
    RelationExecutionGrounding,
    SchnorrRelationInstance,
    admit_instance,
    admit_relation,
    canonical_schnorr_relation,
    check_relation_execution_grounding,
    check_relation_honest_prover_correspondence,
    relation_execution_grounding_candidate,
    relation_honest_prover_candidate,
)
from .semantic import (
    CHALLENGE,
    COMMITMENT,
    RESPONSE,
    AlgebraProfile,
    ApplicationContextAuthority,
    OccurrenceActor,
    TranscriptConstruction,
    admit_algebra,
    admit_core,
    admit_protocol,
    admit_transcript_construction,
    canonical_core,
    canonical_honest_prover_contract,
    canonical_transcript_construction,
    check_public_coin_eligibility,
    checked_fs_factorization,
    make_fresh_protocol,
    make_fs_protocol,
)
from .terms import Outcome, Result, SEMANTIC_REGIME_ID


SCHEMA = "zkc.r2.p01.public-report.v3"
EXPECTED_PROJECTION_SCHEMA = "zkc.r2.p01.expected-projection.v3"
MAX_CASES = 64

_PUBLIC_INPUT_PATH = "evaluation/r2-p01-schnorr/cases/public-inputs.json"
_SOURCE_LEDGER_PATH = "evaluation/r2-p01-schnorr/cases/source-ledger.json"
_PUBLIC_INPUT_SCHEMA = "zkc.r2.p01.public-inputs.v3"
_PUBLIC_INPUT_DISCLOSURE = "PublicPortableReplayInput"
_APPLICATION_CONTEXT_AUTHORITY = ApplicationContextAuthority.APPLICATION.value
_FRESH_COIN_SOURCE = "FrozenPublicSupportPointNotSamplingEvidence"
_FRESH_COIN_SOURCE_NON_CLAIM = (
    "the frozen support point is not evidence that a challenge was sampled "
    "from the Fresh public-coin kernel"
)
_PUBLIC_INPUT_KEYS = frozenset(
    {
        "schema",
        "disclosure",
        "algebra",
        "application_context",
        "statement",
        "fresh_transcript",
        "fs_proof",
        "public_resource_plan",
        "non_claims",
    }
)
_NON_CLAIMS = (
    "CFRG conformance",
    "production security",
    "hardness",
    "ROM or QROM security",
    "proof of knowledge",
    "malicious-verifier zero knowledge",
    "confidential prover-generation replay",
)

_GENERAL_CLAIMS = (
    ApplicabilityClaim.GENERAL_SPECIAL_SOUNDNESS,
    ApplicabilityClaim.GENERAL_SHVZK,
    ApplicabilityClaim.GENERAL_HVZK,
    ApplicabilityClaim.KNOWLEDGE_SOUNDNESS,
    ApplicabilityClaim.FIAT_SHAMIR_ROM,
    ApplicabilityClaim.FIAT_SHAMIR_QROM,
)


def _json_value(value: Any) -> Any:
    """Return the normalized, bounded JSON representation of ``value``."""

    return load_bounded_json_bytes(canonical_json_bytes(value))


def _mapping(value: Any, where: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise ValueError(f"{where} must be an object")
    return value


def _exact_mapping(
    value: Any,
    expected_keys: frozenset[str],
    where: str,
) -> Mapping[str, Any]:
    mapping = _mapping(value, where)
    actual_keys = set(mapping)
    if actual_keys != expected_keys:
        missing = sorted(expected_keys - actual_keys)
        extra = sorted(actual_keys - expected_keys)
        raise ValueError(
            f"{where} keys differ (missing={missing}, extra={extra})"
        )
    return mapping


def _integer(value: Any, where: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"{where} must be an integer")
    return value


def _nonnegative_integer(value: Any, where: str) -> int:
    integer = _integer(value, where)
    if integer < 0:
        raise ValueError(f"{where} must be nonnegative")
    return integer


def _text(value: Any, where: str) -> str:
    if not isinstance(value, str) or not value:
        raise ValueError(f"{where} must be nonempty text")
    return value


def _exact_text(value: Any, expected: str, where: str) -> str:
    text = _text(value, where)
    if text != expected:
        raise ValueError(f"{where} differs from {expected!r}")
    return text


def _exact_non_claims(value: Any) -> tuple[str, ...]:
    if not isinstance(value, list) or any(
        not isinstance(item, str) or not item for item in value
    ):
        raise ValueError("non_claims must be a sequence of nonempty text")
    non_claims = tuple(value)
    if non_claims != _NON_CLAIMS:
        raise ValueError("non_claims differ from the closed Phase B claim boundary")
    return non_claims


def _require_result(value: Any, where: str) -> Result:
    if not isinstance(value, Result):
        raise RuntimeError(f"{where} did not return a judgment Result")
    return value


def _require_outcome(value: Result, expected: Outcome, where: str) -> Result:
    if value.outcome is not expected:
        raise RuntimeError(
            f"{where} returned {value.outcome.value}/{value.code}; "
            f"expected {expected.value}"
        )
    return value


def _require_value(value: Any, expected_type: type, where: str) -> Any:
    if isinstance(value, Result):
        raise RuntimeError(
            f"{where} returned {value.outcome.value}/{value.code}: {value.detail}"
        )
    if not isinstance(value, expected_type):
        raise RuntimeError(f"{where} returned {type(value).__name__}")
    return value


@dataclass(frozen=True)
class Case:
    """One exact public judgment and its evidence-record identity."""

    name: str
    result: Result
    validation_basis_id: ValidationBasisId
    operand_ids: Mapping[str, str]

    def evidence_preimage(self) -> dict[str, Any]:
        return {
            "case": self.name,
            "validation_basis_id": str(self.validation_basis_id),
            "operand_ids": dict(sorted(self.operand_ids.items())),
            "result": self.result.term(),
        }

    @property
    def evidence_id(self) -> EvidenceRecordId:
        return evidence_record_id("p01-public-case", self.evidence_preimage())

    def term(self) -> dict[str, Any]:
        return _json_value(
            {
                **self.result.term(),
                "validation_basis_id": str(self.validation_basis_id),
                "operand_ids": dict(sorted(self.operand_ids.items())),
                "evidence_id": str(self.evidence_id),
            }
        )


def _declaration(role: str, name: str, module: Any = None) -> SourceDeclaration:
    return SourceDeclaration(
        role,
        f"evaluation/r2-p01-schnorr/p01model/{name}.py"
        if name != "run"
        else "evaluation/r2-p01-schnorr/run.py",
        module,
    )


def _source_manifests(repo_root: Path) -> dict[str, SourceManifest]:
    report_module = sys.modules[__name__]
    package = _declaration(
        "package-initializer",
        "__init__",
        sys.modules[__package__],
    )
    terms = _declaration("closed-term", "terms", terms_module)
    provenance = _declaration("provenance", "provenance", provenance_module)
    semantic = _declaration("protocol-semantics", "semantic", semantic_module)
    execution = _declaration("public-execution", "execution", execution_module)
    relations = _declaration("relations", "relations", relations_module)
    declarations: dict[str, tuple[SourceDeclaration, ...]] = {
        "semantic": (package, terms, semantic),
        "execution": (package, terms, provenance, semantic, execution),
        "interface": (
            package,
            terms,
            provenance,
            semantic,
            execution,
            _declaration("proof-interface", "interface", interface_module),
        ),
        "relations": (package, terms, provenance, semantic, relations),
        "analysis": (
            package,
            terms,
            provenance,
            semantic,
            relations,
            _declaration("finite-analysis", "analysis", analysis_module),
        ),
        "independent": (
            package,
            terms,
            semantic,
            _declaration(
                "independent-reconstruction", "independent", independent_module
            ),
        ),
        "report-replay": (
            package,
            provenance,
            _declaration(
                "diagnostic-classification", "diagnostics", diagnostics_module
            ),
            _declaration("public-report", "report", report_module),
            # The runner is a script rather than an imported module. Its exact
            # bytes remain bound; copied-checkout tests establish import origin.
            _declaration("public-runner", "run"),
        ),
    }
    manifests = {
        name: build_source_manifest(
            repo_root,
            component=f"p01-{name}",
            declarations=component_declarations,
        )
        for name, component_declarations in declarations.items()
    }
    for manifest in manifests.values():
        validate_source_manifest(manifest, repo_root)
    return manifests


def _execution_term(checked: CheckedPublicExecution) -> dict[str, Any]:
    return {
        "invocation": {
            "id": str(checked.invocation.identity),
            **checked.invocation.term(),
        },
        "record": {"id": str(checked.record.identity), **checked.record.term()},
        "replay_request": {
            "id": str(checked.replay_request.identity),
            **checked.replay_request.term(),
        },
        "qualification": {"id": str(checked.identity), **checked.term()},
    }


def _grounding_term(
    grounding: RelationExecutionGrounding,
    checked: CheckedPublicExecution,
) -> dict[str, Any]:
    return {
        "id": str(grounding.identity),
        **grounding.term(),
        "public_execution_record_id": str(checked.record.identity),
        "identity_lanes": {
            "relation_and_instance": "SemanticIdentity",
            "statement_occurrence": "ArtifactContentId",
            "qualification_and_grounding": "EvidenceRecordId",
        },
    }


def _add_case(
    cases: list[Case],
    *,
    name: str,
    observed: Result,
    expected: Outcome,
    basis: ValidationBasisId,
    operands: Mapping[str, str],
) -> Result:
    checked = _require_outcome(_require_result(observed, name), expected, name)
    cases.append(Case(name, checked, basis, operands))
    if len(cases) > MAX_CASES:
        raise RuntimeError("public report exceeds its finite case bound")
    return checked


def build_report(repo_root: Path) -> dict[str, Any]:
    """Independently build one public evidence artifact.

    No expectations or confidential owner-local inputs are arguments to this
    function. Expected-result comparison is exclusively a runner operation
    performed after this function returns.
    """

    root = bind_loaded_root(repo_root)
    public_fixture = load_public_fixture(
        root,
        path=_PUBLIC_INPUT_PATH,
        role="p01-public-replay-inputs",
    )
    source_ledger = load_public_fixture(
        root,
        path=_SOURCE_LEDGER_PATH,
        role="p01-research-source-ledger",
    )
    fixture = _exact_mapping(
        public_fixture.value,
        _PUBLIC_INPUT_KEYS,
        "public-inputs fixture",
    )
    ledger = _mapping(source_ledger.value, "source-ledger fixture")
    _exact_text(fixture.get("schema"), _PUBLIC_INPUT_SCHEMA, "public-inputs.schema")
    disclosure = _exact_text(
        fixture.get("disclosure"),
        _PUBLIC_INPUT_DISCLOSURE,
        "public-inputs.disclosure",
    )
    if ledger.get("schema") != "zkc.r2.p01.source-ledger.v1":
        raise ValueError("source-ledger schema differs from Phase B")

    algebra = _exact_mapping(
        fixture.get("algebra"),
        frozenset({"p", "q", "generator", "challenge_size"}),
        "algebra",
    )
    profile = AlgebraProfile(
        p=_integer(algebra.get("p"), "algebra.p"),
        q=_integer(algebra.get("q"), "algebra.q"),
        generator=_integer(algebra.get("generator"), "algebra.generator"),
        challenge_size=_integer(
            algebra.get("challenge_size"), "algebra.challenge_size"
        ),
    )
    statement = _integer(fixture.get("statement"), "statement")
    application_context = _exact_mapping(
        fixture.get("application_context"),
        frozenset({"value", "authority"}),
        "application_context",
    )
    context = _text(
        application_context.get("value"),
        "application_context.value",
    )
    context_authority = _exact_text(
        application_context.get("authority"),
        _APPLICATION_CONTEXT_AUTHORITY,
        "application_context.authority",
    )
    fresh_fixture = _exact_mapping(
        fixture.get("fresh_transcript"),
        frozenset({"commitment", "challenge", "response", "coin_source"}),
        "fresh_transcript",
    )
    fresh_coin_source = _exact_text(
        fresh_fixture.get("coin_source"),
        _FRESH_COIN_SOURCE,
        "fresh_transcript.coin_source",
    )
    fs_fixture = _exact_mapping(
        fixture.get("fs_proof"),
        frozenset({"encoding_hex"}),
        "fs_proof",
    )
    resource_fixture = _exact_mapping(
        fixture.get("public_resource_plan"),
        frozenset(
            {
                "max_transcript_atoms",
                "max_hash_queries",
                "max_trace_events",
                "max_replay_executions",
            }
        ),
        "public_resource_plan",
    )
    public_resources = PublicResourcePlan(
        max_transcript_atoms=_nonnegative_integer(
            resource_fixture.get("max_transcript_atoms"),
            "public_resource_plan.max_transcript_atoms",
        ),
        max_hash_queries=_nonnegative_integer(
            resource_fixture.get("max_hash_queries"),
            "public_resource_plan.max_hash_queries",
        ),
        max_trace_events=_nonnegative_integer(
            resource_fixture.get("max_trace_events"),
            "public_resource_plan.max_trace_events",
        ),
        max_replay_executions=_nonnegative_integer(
            resource_fixture.get("max_replay_executions"),
            "public_resource_plan.max_replay_executions",
        ),
    )
    non_claims = _exact_non_claims(fixture.get("non_claims"))
    try:
        proof_bytes = bytes.fromhex(
            _text(fs_fixture.get("encoding_hex"), "fs_proof.encoding_hex")
        )
    except ValueError as error:
        raise ValueError("FS proof encoding is not canonical hexadecimal") from error

    manifests = _source_manifests(root)
    semantic_basis = manifests["semantic"].identity
    relations_basis = manifests["relations"].identity
    analysis_basis = manifests["analysis"].identity
    independent_basis = manifests["independent"].identity

    core = canonical_core(profile)
    honest_contract = canonical_honest_prover_contract(core, profile)
    construction = canonical_transcript_construction(core, profile)
    fresh_protocol, fresh = make_fresh_protocol(core, profile)
    fs_protocol = make_fs_protocol(core, construction, profile)
    if construction.application_authority.value != context_authority:
        raise RuntimeError(
            "admitted application-context authority differs from the FS construction"
        )
    evaluator_basis = build_evaluator_basis(
        root,
        (fresh_protocol.identity, fs_protocol.identity),
        public_resources,
    )
    execution_basis = evaluator_basis.identity
    interface_basis = manifests["interface"].identity

    cases: list[Case] = []
    _add_case(
        cases,
        name="semantic/algebra-admitted.v2",
        observed=admit_algebra(profile),
        expected=Outcome.AFFIRMATIVE,
        basis=semantic_basis,
        operands={"profile": profile.identity},
    )
    _add_case(
        cases,
        name="semantic/core-admitted.v2",
        observed=admit_core(core, profile),
        expected=Outcome.AFFIRMATIVE,
        basis=semantic_basis,
        operands={"core": core.identity, "profile": profile.identity},
    )
    _add_case(
        cases,
        name="semantic/public-coin-eligible.v3",
        observed=check_public_coin_eligibility(core, profile),
        expected=Outcome.AFFIRMATIVE,
        basis=semantic_basis,
        operands={"core": core.identity, "profile": profile.identity},
    )
    non_public_coin_core = replace(
        core,
        occurrences=tuple(
            replace(contract, actor=OccurrenceActor.PROVER)
            if contract.occurrence == CHALLENGE
            else contract
            for contract in core.occurrences
        ),
    )
    _add_case(
        cases,
        name="negative/semantic/prover-owned-challenge.v3",
        observed=check_public_coin_eligibility(non_public_coin_core, profile),
        expected=Outcome.SEMANTIC_NEGATIVE,
        basis=semantic_basis,
        operands={
            "candidate_core": non_public_coin_core.identity,
            "expected_core": core.identity,
        },
    )
    _add_case(
        cases,
        name="semantic/fresh-protocol-admitted.v2",
        observed=admit_protocol(fresh_protocol, core, profile, fresh=fresh),
        expected=Outcome.AFFIRMATIVE,
        basis=semantic_basis,
        operands={
            "core": core.identity,
            "protocol": fresh_protocol.identity,
            "realization": fresh.identity,
        },
    )
    _add_case(
        cases,
        name="semantic/fs-construction-admitted.v2",
        observed=admit_transcript_construction(
            construction, core, profile, source_fresh=fresh
        ),
        expected=Outcome.AFFIRMATIVE,
        basis=semantic_basis,
        operands={
            "construction": construction.identity,
            "source_fresh_protocol": fresh_protocol.identity,
        },
    )
    _add_case(
        cases,
        name="semantic/fs-protocol-admitted.v2",
        observed=admit_protocol(
            fs_protocol, core, profile, construction=construction
        ),
        expected=Outcome.AFFIRMATIVE,
        basis=semantic_basis,
        operands={
            "construction": construction.identity,
            "protocol": fs_protocol.identity,
        },
    )
    factorization = _add_case(
        cases,
        name="semantic/fresh-fs-factorization.v2",
        observed=checked_fs_factorization(
            fresh_protocol,
            fs_protocol,
            construction,
            core,
            profile,
            fresh,
        ),
        expected=Outcome.AFFIRMATIVE,
        basis=semantic_basis,
        operands={
            "fresh_protocol": fresh_protocol.identity,
            "fs_protocol": fs_protocol.identity,
            "construction": construction.identity,
        },
    )

    fresh_binding = FreshChallengeBinding(
        core.identity,
        fresh_protocol.identity,
        CHALLENGE,
        _integer(fresh_fixture.get("challenge"), "fresh_transcript.challenge"),
        public_fixture.artifact_id,
    )
    fresh_invocation = PublicInvocation(
        profile.identity,
        core.identity,
        fresh_protocol.identity,
        statement,
        None,
        fresh_binding,
    )
    fresh_record = _require_value(
        build_portable_execution(
            fresh_invocation,
            _integer(fresh_fixture.get("commitment"), "fresh_transcript.commitment"),
            _integer(fresh_fixture.get("response"), "fresh_transcript.response"),
            fresh_protocol,
            profile,
            core,
            fresh=fresh,
        ),
        PortableExecutionRecord,
        "Fresh public execution",
    )
    fresh_request = PublicReplayRequest(
        fresh_invocation,
        fresh_record,
        evaluator_basis.identity,
        public_fixture.artifact_id,
        public_resources,
    )
    fresh_checked = _require_value(
        qualify_public_execution(
            fresh_request,
            evaluator_basis,
            fresh_protocol,
            profile,
            core,
            fresh=fresh,
        ),
        CheckedPublicExecution,
        "Fresh public qualification",
    )
    _add_case(
        cases,
        name="execution/fresh-public-replay.v2",
        observed=check_checked_public_execution(fresh_checked),
        expected=Outcome.AFFIRMATIVE,
        basis=execution_basis,
        operands={
            "public_fixture": str(public_fixture.artifact_id),
            "record": str(fresh_record.identity),
            "qualification": str(fresh_checked.identity),
        },
    )
    _add_case(
        cases,
        name="execution/fresh-public-evaluation.v2",
        observed=check_fresh_public_execution(fresh_checked),
        expected=Outcome.AFFIRMATIVE,
        basis=execution_basis,
        operands={
            "record": str(fresh_record.identity),
            "qualification": str(fresh_checked.identity),
        },
    )

    proof_interface = canonical_fs_proof_interface(
        fs_protocol, construction, core, profile
    )
    _add_case(
        cases,
        name="interface/fs-abi-admitted.v2",
        observed=admit_fs_proof_interface(
            proof_interface, fs_protocol, construction, core, profile
        ),
        expected=Outcome.AFFIRMATIVE,
        basis=interface_basis,
        operands={
            "interface": proof_interface.identity,
            "protocol": fs_protocol.identity,
        },
    )
    decoded = _require_value(
        decode_fs_proof(
            proof_bytes, proof_interface, fs_protocol, construction, core, profile
        ),
        DecodedFSProof,
        "FS proof decoding",
    )
    fs_external = FSExternalInputs(context, statement)
    fs_invocation = PublicInvocation(
        profile.identity,
        core.identity,
        fs_protocol.identity,
        statement,
        context,
    )
    fs_record = _require_value(
        build_portable_execution(
            fs_invocation,
            decoded.commitment,
            decoded.response,
            fs_protocol,
            profile,
            core,
            construction=construction,
        ),
        PortableExecutionRecord,
        "FS public execution",
    )
    fs_request = PublicReplayRequest(
        fs_invocation,
        fs_record,
        evaluator_basis.identity,
        public_fixture.artifact_id,
        public_resources,
    )
    fs_checked = _require_value(
        qualify_public_execution(
            fs_request,
            evaluator_basis,
            fs_protocol,
            profile,
            core,
            construction=construction,
        ),
        CheckedPublicExecution,
        "FS public qualification",
    )
    _add_case(
        cases,
        name="execution/fs-public-replay.v2",
        observed=check_checked_public_execution(fs_checked),
        expected=Outcome.AFFIRMATIVE,
        basis=execution_basis,
        operands={
            "public_fixture": str(public_fixture.artifact_id),
            "record": str(fs_record.identity),
            "qualification": str(fs_checked.identity),
        },
    )
    resource_limited_request = replace(
        fs_request,
        resources=PublicResourcePlan(2, 1, 5, 1),
    )
    _add_case(
        cases,
        name="negative/execution/public-replay-resource-ceiling.v3",
        observed=qualify_public_execution(
            resource_limited_request,
            evaluator_basis,
            fs_protocol,
            profile,
            core,
            construction=construction,
        ),
        expected=Outcome.RESOURCE_EXCEEDED,
        basis=execution_basis,
        operands={
            "candidate_request": str(resource_limited_request.identity),
            "evaluator_basis": str(evaluator_basis.identity),
        },
    )
    fs_verification = _require_value(
        evaluate_fs_proof(
            proof_bytes,
            fs_external,
            proof_interface,
            evaluator_basis,
            fs_protocol,
            construction,
            core,
            profile,
        ),
        FSVerificationRecord,
        "FS proof verification record",
    )
    resource_limited_verifier_basis = build_evaluator_basis(
        root,
        (fs_protocol.identity,),
        PublicResourcePlan(0, 0, 0, 0),
    )
    _add_case(
        cases,
        name="negative/interface/proof-verification-resource-ceiling.v3",
        observed=check_fs_proof(
            proof_bytes,
            fs_external,
            proof_interface,
            resource_limited_verifier_basis,
            fs_protocol,
            construction,
            core,
            profile,
        ),
        expected=Outcome.RESOURCE_EXCEEDED,
        basis=interface_basis,
        operands={
            "candidate_basis": str(resource_limited_verifier_basis.identity),
            "proof_artifact": str(artifact_content_id(proof_bytes)),
        },
    )
    _add_case(
        cases,
        name="interface/fs-proof-accepted.v2",
        observed=check_fs_proof(
            proof_bytes,
            fs_external,
            proof_interface,
            evaluator_basis,
            fs_protocol,
            construction,
            core,
            profile,
        ),
        expected=Outcome.AFFIRMATIVE,
        basis=interface_basis,
        operands={
            "proof": str(fs_proof_artifact_id(proof_bytes)),
            "verification": str(fs_verification.identity),
            "verifier_basis": str(evaluator_basis.identity),
        },
    )
    _add_case(
        cases,
        name="interface/fs-execution-projection.v2",
        observed=check_fs_execution_projection(
            fs_checked, proof_interface, proof_bytes=proof_bytes
        ),
        expected=Outcome.AFFIRMATIVE,
        basis=interface_basis,
        operands={
            "execution_qualification": str(fs_checked.identity),
            "interface": proof_interface.identity,
            "proof": str(fs_proof_artifact_id(proof_bytes)),
        },
    )

    relation = canonical_schnorr_relation(profile)
    instance = SchnorrRelationInstance(relation.identity, statement)
    correspondence = relation_honest_prover_candidate(
        relation, core, honest_contract, profile
    )
    _add_case(
        cases,
        name="relations/relation-admitted.v2",
        observed=admit_relation(relation, profile),
        expected=Outcome.AFFIRMATIVE,
        basis=relations_basis,
        operands={"profile": profile.identity, "relation": relation.identity},
    )
    _add_case(
        cases,
        name="relations/instance-admitted.v2",
        observed=admit_instance(instance, relation, profile),
        expected=Outcome.AFFIRMATIVE,
        basis=relations_basis,
        operands={"instance": instance.identity, "relation": relation.identity},
    )
    _add_case(
        cases,
        name="relations/honest-prover-correspondence.v2",
        observed=check_relation_honest_prover_correspondence(
            correspondence, relation, core, honest_contract, profile
        ),
        expected=Outcome.AFFIRMATIVE,
        basis=relations_basis,
        operands={
            "correspondence": correspondence.identity,
            "honest_contract": honest_contract.identity,
            "relation": relation.identity,
        },
    )

    fresh_statement = _require_value(
        issue_relations_checked_statement(fresh_checked),
        relations_module.CheckedPublicExecutionStatement,
        "Fresh checked Statement export",
    )
    fs_statement = _require_value(
        issue_relations_checked_statement(fs_checked),
        relations_module.CheckedPublicExecutionStatement,
        "FS checked Statement export",
    )
    fresh_grounding = relation_execution_grounding_candidate(
        instance, relation, fresh_statement
    )
    fs_grounding = relation_execution_grounding_candidate(
        instance, relation, fs_statement
    )
    fresh_grounding_result = _add_case(
        cases,
        name="relations/fresh-execution-grounding.v2",
        observed=check_relation_execution_grounding(
            fresh_grounding, instance, relation, fresh_statement, profile
        ),
        expected=Outcome.AFFIRMATIVE,
        basis=relations_basis,
        operands={
            "grounding": str(fresh_grounding.identity),
            "qualification": str(fresh_checked.identity),
            "statement_event": str(fresh_statement.source_event_id),
        },
    )
    fs_grounding_result = _add_case(
        cases,
        name="relations/fs-execution-grounding.v2",
        observed=check_relation_execution_grounding(
            fs_grounding, instance, relation, fs_statement, profile
        ),
        expected=Outcome.AFFIRMATIVE,
        basis=relations_basis,
        operands={
            "grounding": str(fs_grounding.identity),
            "qualification": str(fs_checked.identity),
            "statement_event": str(fs_statement.source_event_id),
        },
    )

    fresh_transcript = SchnorrTranscript(
        instance.identity,
        statement,
        _integer(public_trace_value(fresh_record, COMMITMENT), "Fresh commitment"),
        _integer(public_trace_value(fresh_record, CHALLENGE), "Fresh challenge"),
        _integer(public_trace_value(fresh_record, RESPONSE), "Fresh response"),
    )
    fs_transcript = SchnorrTranscript(
        instance.identity,
        statement,
        _integer(public_trace_value(fs_record, COMMITMENT), "FS commitment"),
        _integer(public_trace_value(fs_record, CHALLENGE), "FS challenge"),
        _integer(public_trace_value(fs_record, RESPONSE), "FS response"),
    )
    fresh_transcript_result = _add_case(
        cases,
        name="analysis/fresh-public-transcript.v2",
        observed=check_accepting_transcript(
            fresh_transcript, instance, relation, profile
        ),
        expected=Outcome.AFFIRMATIVE,
        basis=analysis_basis,
        operands={
            "execution_qualification": str(fresh_checked.identity),
            "transcript": fresh_transcript.identity,
        },
    )
    fs_transcript_result = _add_case(
        cases,
        name="analysis/fs-public-transcript.v2",
        observed=check_accepting_transcript(
            fs_transcript, instance, relation, profile
        ),
        expected=Outcome.AFFIRMATIVE,
        basis=analysis_basis,
        operands={
            "execution_qualification": str(fs_checked.identity),
            "transcript": fs_transcript.identity,
        },
    )
    _add_case(
        cases,
        name="negative/analysis/equal-challenge-fork.v3",
        observed=check_special_soundness_fork(
            TranscriptFork(fresh_transcript, fresh_transcript),
            instance,
            relation,
            profile,
        ),
        expected=Outcome.SEMANTIC_NEGATIVE,
        basis=analysis_basis,
        operands={
            "left_transcript": fresh_transcript.identity,
            "right_transcript": fresh_transcript.identity,
        },
    )
    finite_special_soundness = _add_case(
        cases,
        name="analysis/exhaustive-special-soundness-algebra.v2",
        observed=exhaustive_special_soundness(profile),
        expected=Outcome.AFFIRMATIVE,
        basis=analysis_basis,
        operands={"profile": profile.identity, "relation": relation.identity},
    )
    finite_shvzk = _add_case(
        cases,
        name="analysis/exhaustive-shvzk-distribution.v2",
        observed=exhaustive_shvzk_distribution_equality(profile),
        expected=Outcome.AFFIRMATIVE,
        basis=analysis_basis,
        operands={"profile": profile.identity, "relation": relation.identity},
    )
    applicability: dict[str, Result] = {}
    for claim in _GENERAL_CLAIMS:
        observed = probe_analysis_applicability(claim, profile)
        applicability[claim.value] = observed
        _add_case(
            cases,
            name=f"analysis/theorem-refusal/{claim.value}.v2",
            observed=observed,
            expected=Outcome.REFUSED,
            basis=analysis_basis,
            operands={"profile": profile.identity},
        )

    independent = reconstruct_fs_v3(
        construction,
        p=profile.p,
        challenge_size=profile.challenge_size,
        application_context=context,
        statement=statement,
        commitment=decoded.commitment,
    )
    receipt = fs_record.challenge_receipt
    independent_agreement = (
        independent.query.hex() == receipt.query_hex
        and independent.challenge == receipt.challenge
        and len(receipt.reads) == 2
        and independent.statement_frame.hex() == receipt.reads[0].framed_hex
        and independent.commitment_frame.hex() == receipt.reads[1].framed_hex
    )
    if not independent_agreement:
        raise RuntimeError("independent FS byte reconstruction disagrees")
    independent_term = independent.public_term()
    independent_evidence = evidence_record_id(
        "p01-independent-fs-agreement",
        {
            "validation_basis_id": str(independent_basis),
            "construction_id": construction.identity,
            "execution_record_id": str(fs_record.identity),
            "reconstruction": independent_term,
        },
    )

    # Static and public-interface refusals. These are finite first-boundary
    # drivers, never intentionally malformed private capabilities.
    strong_fs_mutations: tuple[tuple[str, TranscriptConstruction], ...] = (
        ("statement-omitted", replace(construction, atoms=construction.atoms[1:])),
        ("commitment-omitted", replace(construction, atoms=construction.atoms[:1])),
        ("prefix-reordered", replace(construction, atoms=construction.atoms[::-1])),
        (
            "atom-codec-changed",
            replace(
                construction,
                atoms=(
                    replace(construction.atoms[0], codec="unsigned-minimal-be.v2"),
                    construction.atoms[1],
                ),
            ),
        ),
        (
            "challenge-namespace-changed",
            replace(construction, challenge_namespace="zkc/p01/other/challenge"),
        ),
        ("framing-changed", replace(construction, framing="concatenation.v1")),
        (
            "source-fresh-protocol-changed",
            replace(construction, source_fresh_protocol_id="sha256:" + "00" * 32),
        ),
        (
            "application-authority-changed",
            replace(
                construction,
                application_authority=ApplicationContextAuthority.PUBLIC_ENVIRONMENT,
            ),
        ),
    )
    for name, mutation in strong_fs_mutations:
        _add_case(
            cases,
            name=f"negative/fs/{name}.v2",
            observed=admit_transcript_construction(
                mutation, core, profile, source_fresh=fresh
            ),
            expected=(
                Outcome.MISMATCH
                if name == "source-fresh-protocol-changed"
                else Outcome.SEMANTIC_NEGATIVE
            ),
            basis=semantic_basis,
            operands={
                "candidate_construction": mutation.identity,
                "expected_construction": construction.identity,
            },
        )

    for name, malformed_proof in (
        ("proof-truncated", proof_bytes[:-1]),
        ("proof-trailing-byte", proof_bytes + b"\x00"),
        ("proof-field-outside-domain", b"\x00" + proof_bytes[1:]),
    ):
        observed = decode_fs_proof(
            malformed_proof,
            proof_interface,
            fs_protocol,
            construction,
            core,
            profile,
        )
        _add_case(
            cases,
            name=f"negative/interface/{name}.v2",
            observed=_require_result(observed, name),
            expected=(
                Outcome.SEMANTIC_NEGATIVE
                if name == "proof-field-outside-domain"
                else Outcome.MALFORMED
            ),
            basis=interface_basis,
            operands={
                "candidate_proof": str(artifact_content_id(malformed_proof)),
                "interface": proof_interface.identity,
            },
        )

    rejecting_proof = proof_bytes[:-1] + bytes([(proof_bytes[-1] + 1) % profile.q])
    _add_case(
        cases,
        name="negative/interface/rejecting-proof.v2",
        observed=check_fs_proof(
            rejecting_proof,
            fs_external,
            proof_interface,
            evaluator_basis,
            fs_protocol,
            construction,
            core,
            profile,
        ),
        expected=Outcome.SEMANTIC_NEGATIVE,
        basis=interface_basis,
        operands={
            "candidate_proof": str(artifact_content_id(rejecting_proof)),
            "interface": proof_interface.identity,
        },
    )

    different_instance = SchnorrRelationInstance(relation.identity, 9)
    mismatched_grounding = relation_execution_grounding_candidate(
        different_instance, relation, fresh_statement
    )
    _add_case(
        cases,
        name="negative/relations/statement-value-mismatch.v2",
        observed=check_relation_execution_grounding(
            mismatched_grounding,
            different_instance,
            relation,
            fresh_statement,
            profile,
        ),
        expected=Outcome.MISMATCH,
        basis=relations_basis,
        operands={
            "execution_qualification": str(fresh_checked.identity),
            "relation_instance": different_instance.identity,
            "statement_event": str(fresh_statement.source_event_id),
        },
    )

    case_terms = {
        case.name: case.term() for case in sorted(cases, key=lambda item: item.name)
    }
    diagnostic_closure = classification_summary()
    classifications = {
        declaration.code: declaration.classification.value
        for declaration in diagnostic_closure.declarations
    }
    executed_codes: dict[str, dict[str, Any]] = {}
    for case in sorted(cases, key=lambda item: item.name):
        classification = classifications.get(case.result.code)
        if classification is None:
            raise RuntimeError(
                f"executed case uses an unclassified diagnostic: {case.result.code}"
            )
        row = executed_codes.setdefault(
            case.result.code,
            {"classification": classification, "cases": []},
        )
        row["cases"].append(case.name)
    closure_preimage = {
        "validation_basis_id": str(manifests["report-replay"].identity),
        "classification_summary": diagnostic_closure.term(),
    }
    closure_evidence = evidence_record_id(
        "p01-diagnostic-classification-closure", closure_preimage
    )
    executed_preimage = {
        "validation_basis_id": str(manifests["report-replay"].identity),
        "case_evidence_ids": [str(case.evidence_id) for case in cases],
        "executed_codes": executed_codes,
    }
    executed_evidence = evidence_record_id(
        "p01-executed-public-case-drivers", executed_preimage
    )
    diagnostics_term = {
        "classification_closure": {
            "validation_basis_id": str(manifests["report-replay"].identity),
            "evidence_id": str(closure_evidence),
            "declared_code_count": diagnostic_closure.declared_count,
            "source_files": list(diagnostic_closure.source_files),
            "counts": {
                category.value: count
                for category, count in diagnostic_closure.counts
            },
            "meaning": (
                "every currently declared diagnostic has one explicit class; "
                "this is not reachability evidence"
            ),
        },
        "executed_public_cases": {
            "evidence_id": str(executed_evidence),
            "case_count": len(cases),
            "nonaffirmative_case_count": sum(
                case.result.outcome is not Outcome.AFFIRMATIVE for case in cases
            ),
            "distinct_executed_code_count": len(executed_codes),
            "codes": executed_codes,
            "meaning": "only the explicit public report cases were executed",
            "non_claim": (
                "no reachability is inferred for unexecuted constructible, "
                "internal, environmental, retired, or redundant codes"
            ),
        },
    }
    validation_bases = {
        name: manifest.term() for name, manifest in sorted(manifests.items())
    }
    validation_bases["public-evaluator"] = {
        "id": str(evaluator_basis.identity),
        **evaluator_basis.term(),
    }

    body = _json_value(
        {
            "schema": SCHEMA,
            "scope": {
                "witness": "P01 Schnorr/Sigma finite Phase B repair",
                "disclosure": "public-only",
                "claims": (
                    "exact loaded-source and public-fixture binding",
                    "Fresh and Fiat-Shamir public execution replay",
                    "FS proof-interface verification and execution projection",
                    "Relations grounding of the checked public Statement",
                    "complete finite-profile algebraic enumeration",
                    "second byte-level FS reconstruction",
                ),
                "non_claims": non_claims
                + (
                    "application-context source authenticity outside the frozen public fixture",
                    "hostile same-process capability isolation",
                ),
            },
            "public_inputs": {
                "replay_fixture": public_fixture.term(),
                "research_source_ledger": source_ledger.term(),
                "admitted_fixture_contract": {
                    "schema": _PUBLIC_INPUT_SCHEMA,
                    "disclosure": disclosure,
                    "application_context_authority": context_authority,
                    "fresh_challenge_source": {
                        "kind": fresh_coin_source,
                        "source_artifact_id": str(public_fixture.artifact_id),
                        "non_claim": _FRESH_COIN_SOURCE_NON_CLAIM,
                    },
                    "public_resource_plan": public_resources.term(),
                    "finite_analysis_scope_source": (
                        "derived from executed finite-analysis evidence"
                    ),
                },
                "application_context_authority": {
                    "declared_owner": context_authority,
                    "value_source_artifact_id": str(public_fixture.artifact_id),
                    "non_claim": "the fixture binding does not authenticate an external caller",
                },
            },
            "validation_bases": validation_bases,
            "semantic_roots": {
                "semantic_regime_id": SEMANTIC_REGIME_ID,
                "algebra_profile_id": profile.identity,
                "core_id": core.identity,
                "honest_prover_contract_id": honest_contract.identity,
                "fresh_realization_id": fresh.identity,
                "fresh_protocol_id": fresh_protocol.identity,
                "transcript_construction_id": construction.identity,
                "fs_protocol_id": fs_protocol.identity,
                "fs_proof_interface_id": proof_interface.identity,
                "relation_id": relation.identity,
                "relation_instance_id": instance.identity,
                "factorization_id": factorization.subject,
            },
            "public_executions": {
                "fresh": _execution_term(fresh_checked),
                "fiat_shamir": _execution_term(fs_checked),
            },
            "proof_interface": {
                "interface": {"id": proof_interface.identity, **proof_interface.term()},
                "proof_artifact_id": str(fs_proof_artifact_id(proof_bytes)),
                "proof_encoding_hex": proof_bytes.hex(),
                "external_inputs": {"id": str(fs_external.identity), **fs_external.term()},
                "verification": {
                    "id": str(fs_verification.identity),
                    **fs_verification.term(),
                },
            },
            "relations": {
                "relation": {"id": relation.identity, **relation.term()},
                "instance": {"id": instance.identity, **instance.term()},
                "honest_prover_correspondence": {
                    "id": correspondence.identity,
                    **correspondence.term(),
                },
                "fresh_grounding": _grounding_term(fresh_grounding, fresh_checked),
                "fs_grounding": _grounding_term(fs_grounding, fs_checked),
                "grounding_results": {
                    "fresh": fresh_grounding_result.term(),
                    "fiat_shamir": fs_grounding_result.term(),
                },
            },
            "finite_analysis": {
                "derived_scope": {
                    "authority": "ExecutedFiniteAnalysisEvidence",
                    "profile_id": profile.identity,
                    "special_soundness": {
                        "statement_count": finite_special_soundness.evidence[
                            "statement_count"
                        ],
                        "nonce_count_per_statement": finite_special_soundness.evidence[
                            "nonce_count_per_statement"
                        ],
                        "challenge_count_per_statement_nonce": (
                            finite_special_soundness.evidence[
                                "challenge_count_per_statement_nonce"
                            ]
                        ),
                        "accepting_transcript_count": finite_special_soundness.evidence[
                            "accepting_transcript_count"
                        ],
                        "unordered_distinct_challenge_fork_count": (
                            finite_special_soundness.evidence[
                                "unordered_distinct_challenge_fork_count"
                            ]
                        ),
                        "coverage": finite_special_soundness.evidence["coverage"],
                    },
                    "shvzk": {
                        "statement_count": finite_shvzk.evidence[
                            "statement_count"
                        ],
                        "challenge_count_per_statement": finite_shvzk.evidence[
                            "challenge_count_per_statement"
                        ],
                        "conditional_distribution_count": finite_shvzk.evidence[
                            "conditional_distribution_count"
                        ],
                        "support_points_per_distribution_per_side": (
                            finite_shvzk.evidence[
                                "support_points_per_distribution_per_side"
                            ]
                        ),
                        "total_samples_per_side": finite_shvzk.evidence[
                            "total_samples_per_side"
                        ],
                    },
                    "claim": "exact finite algebraic equality only",
                    "non_claims": (
                        finite_special_soundness.evidence["non_claim"],
                        finite_shvzk.evidence["non_claim"],
                    ),
                },
                "actual_transcripts": {
                    "fresh": {
                        "id": fresh_transcript.identity,
                        **fresh_transcript.term(),
                        "judgment": fresh_transcript_result.term(),
                    },
                    "fiat_shamir": {
                        "id": fs_transcript.identity,
                        **fs_transcript.term(),
                        "judgment": fs_transcript_result.term(),
                    },
                },
                "exhaustive_special_soundness": finite_special_soundness.term(),
                "exhaustive_shvzk": finite_shvzk.term(),
                "theorem_applicability": {
                    name: result.term()
                    for name, result in sorted(applicability.items())
                },
            },
            "independent_reconstruction": {
                "validation_basis_id": str(independent_basis),
                "evidence_id": str(independent_evidence),
                "agrees_with_fs_execution": independent_agreement,
                **independent_term,
            },
            "diagnostics": diagnostics_term,
            "cases": case_terms,
        }
    )
    report_id = evidence_record_id("p01-public-report", body)
    return {**body, "report_id": str(report_id)}


def expected_projection(report: Mapping[str, Any]) -> dict[str, Any]:
    """Return the stable post-build oracle surface consumed by the runner."""

    public_inputs = _mapping(report.get("public_inputs"), "report.public_inputs")
    replay_fixture = _mapping(
        public_inputs.get("replay_fixture"), "report public replay fixture"
    )
    source_ledger = _mapping(
        public_inputs.get("research_source_ledger"), "report source ledger"
    )
    return _json_value(
        {
            "schema": EXPECTED_PROJECTION_SCHEMA,
            "report_schema": report.get("schema"),
            "report_id": report.get("report_id"),
            "public_input_artifact_id": replay_fixture.get("artifact_content_id"),
            "source_ledger_artifact_id": source_ledger.get("artifact_content_id"),
            "cases": report.get("cases"),
        }
    )


def _parse_typed_id(value: Any, kind: type, where: str) -> None:
    if not isinstance(value, str):
        raise ValueError(f"{where} is not text")
    kind.parse(value)


def _verify_case(name: str, case: Any) -> list[str]:
    if not isinstance(case, Mapping):
        return [f"case is not an object: {name}"]
    required = {
        "outcome",
        "boundary",
        "code",
        "detail",
        "subject",
        "evidence",
        "validation_basis_id",
        "operand_ids",
        "evidence_id",
    }
    if set(case) != required:
        return [f"case envelope differs: {name}"]
    errors: list[str] = []
    try:
        _parse_typed_id(case["validation_basis_id"], ValidationBasisId, name)
        _parse_typed_id(case["evidence_id"], EvidenceRecordId, name)
        operands = _mapping(case["operand_ids"], f"{name}.operand_ids")
        if not all(
            isinstance(key, str) and isinstance(value, str)
            for key, value in operands.items()
        ):
            raise ValueError("operand IDs must be a text-to-text object")
        preimage = {
            "case": name,
            "validation_basis_id": case["validation_basis_id"],
            "operand_ids": dict(sorted(operands.items())),
            "result": {
                "outcome": case["outcome"],
                "boundary": case["boundary"],
                "code": case["code"],
                "detail": case["detail"],
                "subject": case["subject"],
                "evidence": case["evidence"],
            },
        }
        expected = evidence_record_id("p01-public-case", preimage)
        if str(expected) != case["evidence_id"]:
            errors.append(f"case evidence identity differs: {name}")
    except (TypeError, ValueError) as error:
        errors.append(f"case identity lane is malformed: {name}: {error}")
    return errors


def verify_report(report: Any, repo_root: Path) -> list[str]:
    """Strictly validate, re-identify, and independently rebuild ``report``."""

    if not isinstance(report, Mapping):
        return ["report is not an object"]
    required = {
        "schema",
        "scope",
        "public_inputs",
        "validation_bases",
        "semantic_roots",
        "public_executions",
        "proof_interface",
        "relations",
        "finite_analysis",
        "independent_reconstruction",
        "diagnostics",
        "cases",
        "report_id",
    }
    if set(report) != required:
        return ["report envelope keys differ"]
    errors: list[str] = []
    if report.get("schema") != SCHEMA:
        errors.append("report schema differs")
    try:
        _parse_typed_id(report.get("report_id"), EvidenceRecordId, "report_id")
        bases = _mapping(report.get("validation_bases"), "validation_bases")
        for name, basis in bases.items():
            _parse_typed_id(
                _mapping(basis, f"validation_bases.{name}").get("id"),
                ValidationBasisId,
                f"validation_bases.{name}.id",
            )
        public_inputs = _mapping(report.get("public_inputs"), "public_inputs")
        for name in ("replay_fixture", "research_source_ledger"):
            binding = _mapping(public_inputs.get(name), f"public_inputs.{name}")
            _parse_typed_id(
                binding.get("artifact_content_id"),
                ArtifactContentId,
                f"public_inputs.{name}.artifact_content_id",
            )
            _parse_typed_id(
                binding.get("canonical_json_content_id"),
                ArtifactContentId,
                f"public_inputs.{name}.canonical_json_content_id",
            )
        reconstruction = _mapping(
            report.get("independent_reconstruction"), "independent_reconstruction"
        )
        _parse_typed_id(
            reconstruction.get("validation_basis_id"),
            ValidationBasisId,
            "independent_reconstruction.validation_basis_id",
        )
        _parse_typed_id(
            reconstruction.get("evidence_id"),
            EvidenceRecordId,
            "independent_reconstruction.evidence_id",
        )
        if reconstruction.get("agrees_with_fs_execution") is not True:
            errors.append("independent reconstruction does not agree")
        diagnostics = _mapping(report.get("diagnostics"), "diagnostics")
        closure = _mapping(
            diagnostics.get("classification_closure"),
            "diagnostics.classification_closure",
        )
        executed = _mapping(
            diagnostics.get("executed_public_cases"),
            "diagnostics.executed_public_cases",
        )
        _parse_typed_id(
            closure.get("validation_basis_id"),
            ValidationBasisId,
            "diagnostics.classification_closure.validation_basis_id",
        )
        _parse_typed_id(
            closure.get("evidence_id"),
            EvidenceRecordId,
            "diagnostics.classification_closure.evidence_id",
        )
        _parse_typed_id(
            executed.get("evidence_id"),
            EvidenceRecordId,
            "diagnostics.executed_public_cases.evidence_id",
        )
    except (TypeError, ValueError) as error:
        errors.append(f"typed report lane is malformed: {error}")

    cases = report.get("cases")
    if not isinstance(cases, Mapping) or not (1 <= len(cases) <= MAX_CASES):
        errors.append("case map is absent or outside its finite bound")
    else:
        for name, case in sorted(cases.items()):
            errors.extend(_verify_case(name, case))

    body = dict(report)
    body.pop("report_id", None)
    try:
        expected_report_id = evidence_record_id("p01-public-report", body)
        if str(expected_report_id) != report.get("report_id"):
            errors.append("report evidence identity differs")
        serialized = canonical_json_bytes(report)
        if b'"overall_pass"' in serialized:
            errors.append("runtime verdict leaked into the public report")
        if b"private-generation.json" in serialized:
            errors.append("owner-local sidecar path leaked into the public report")
    except (TypeError, ValueError) as error:
        errors.append(f"report is outside canonical JSON: {error}")

    try:
        rebuilt = build_report(repo_root)
        if _json_value(report) != rebuilt:
            errors.append("exact public rebuild differs from the supplied report")
    except (OSError, RuntimeError, TypeError, ValueError) as error:
        errors.append(f"exact public rebuild failed: {error}")
    return errors


__all__ = [
    "EXPECTED_PROJECTION_SCHEMA",
    "MAX_CASES",
    "SCHEMA",
    "Case",
    "build_report",
    "expected_projection",
    "verify_report",
]
