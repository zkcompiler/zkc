"""Canonical, compact report for the repaired finite FRI-Grind R2 witness.

The report is an identity graph, not a second serialization of protocol traces
or relation schemas. Exact replay reconstructs the four qualified executions
and every relation judgment from the frozen public inputs. Report-local
manifests expose only bounded identity and accounting summaries.
"""

from __future__ import annotations

from dataclasses import replace
import hashlib
from pathlib import Path
import re
from typing import Any, Mapping

from .execution import (
    ExecutionRecord,
    QualifiedExecution,
    coupled_fresh_tape,
    execute,
    qualification_worst_case,
    qualify_execution,
    validate_terminal_law,
)
from .frigrind import (
    ApplicationContext,
    CoreDerivationKind,
    DEFAULT_RESOURCE_PLAN,
    ExecutionRequest,
    FixedNoncePlan,
    FreshTapeOrigin,
    MAX_QUALIFICATION_CAPS,
    Mutation,
    NonceSearchPlan,
    TerminalKind,
    admit_scenario,
    base_scenario,
    build_evaluator_basis,
    fresh_fri_scenario,
    fresh_grinding_scenario,
    grinding_applicability,
    load_fixture,
    load_external_fresh,
    load_invocation,
    mutate,
)
from .relations import (
    AnchorCapability,
    AnchorReadRequest,
    HybridFactorization,
    RelationRunEvidence,
    RelationShape,
    SubjectOrganization,
    ValidationProfile,
    check_anchor_authority,
    check_hybrid_factorization,
    check_typed_disposition_map,
    classify_projection,
    compare_full_observations,
    compare_mapped_values,
    compare_origins,
    compare_strategies,
    derive_hybrid_factorization,
    derive_relation_run_evidence,
    derive_relation_shape,
    derive_validation_profile,
    projection_loss_applicability,
    protocol_statement_occurrence,
    statement_correspondence,
)
from .terms import (
    CheckResult,
    OutcomeClass,
    SEMANTIC_REGIME_ID,
    semantic_id,
    supports_semantic_regime,
)


SCHEMA = "zkc.r2.protocol-model-report.v3"
REPORT_REPLAY_LAW = "r2.canonical-report-replay.v1"

REPORT_SOURCE_PATHS = (
    "evaluation/r2-protocol-model/r2model/relations.py",
    "evaluation/r2-protocol-model/r2model/report.py",
    "evaluation/r2-protocol-model/run.py",
)

EXECUTION_ROLES = (
    "fs_source",
    "external_fresh_support_point",
    "coupled_fresh_grinding",
    "coupled_fresh_no_grinding",
)
RELATION_NAMES = ("shared", "distinct")
MAX_REPORT_CASES = 64
MAX_REPORT_EVIDENCE = 64
MAX_REPORT_OPERANDS = 16
MAX_REPORT_SOURCES = 8
MAX_REPORT_TEXT_BYTES = 256

_CONTENT_ID = re.compile(r"sha256:[0-9a-f]{64}\Z")
_HEX_DIGEST = re.compile(r"[0-9a-f]{64}\Z")
_LOADED_REPO_ROOT = Path(__file__).resolve().parents[3]

_EXECUTION_MANIFEST_KEYS = {
    "manifest_id",
    "role",
    "interpretation",
    "core_id",
    "scenario_id",
    "construction_id",
    "input_bundle_id",
    "application_context_id",
    "evaluator_basis_id",
    "source_fixture_id",
    "source_package_id",
    "core_derivation",
    "request_id",
    "record_id",
    "qualification_id",
    "coin_tape_id",
    "coin_tape_origin",
    "dependency_qualification_ids",
    "disposition",
    "execution_usage",
    "qualification_usage",
}

_RUN_EVIDENCE_TERM_KEYS = {
    "relation_shape_id",
    "validation_profile_id",
    "fresh_qualification_id",
    "fs_qualification_id",
    "fresh_request_id",
    "fs_request_id",
    "fresh_record_id",
    "fs_record_id",
    "fresh_coin_tape_id",
    "fresh_dependency_qualification_ids",
    "fs_dependency_qualification_ids",
}

_PROFILE_TERM_KEYS = {
    "shape",
    "fresh_evaluator_basis",
    "fs_evaluator_basis",
    "fresh_core_derivation",
    "fs_core_derivation",
    "fresh_construction",
    "fs_construction",
    "fresh_qualification_law",
    "fs_qualification_law",
    "observation_policy",
    "origin_policy",
    "terminal_policy",
    "strategy_policy",
}

_EXECUTION_USAGE_KEYS = {
    "nonce_candidates",
    "transcript_events",
    "trace_events",
    "challenge_values",
    "sampler_attempts",
    "hash_queries",
}

_QUALIFICATION_USAGE_KEYS = {
    "dependency_executions",
    *_EXECUTION_USAGE_KEYS,
}


def _bounded_text(value: Any, limit: int = MAX_REPORT_TEXT_BYTES) -> bool:
    if not isinstance(value, str) or not value:
        return False
    try:
        return len(value.encode("utf-8")) <= limit
    except UnicodeEncodeError:
        return False


def _valid_id(value: Any) -> bool:
    return isinstance(value, str) and _CONTENT_ID.fullmatch(value) is not None


def _bound_repo_root(repo_root: Path) -> Path:
    """Bind file evidence to the checkout whose evaluator code is loaded.

    Python imports are resolved before a runner argument is interpreted.  A
    different data root therefore cannot truthfully name the implementation
    being executed; that checkout must invoke its own runner instead.
    """

    try:
        root = Path(repo_root).resolve()
    except (TypeError, OSError, RuntimeError) as error:
        raise ValueError("repository root is malformed") from error
    if root != _LOADED_REPO_ROOT:
        raise ValueError(
            "repository root differs from the checkout that loaded the evaluator"
        )
    return root


def _require_record(value: ExecutionRecord | CheckResult, label: str) -> ExecutionRecord:
    if isinstance(value, CheckResult):
        raise RuntimeError(f"{label}: {value.code}: {value.detail}")
    if not isinstance(value, ExecutionRecord):
        raise RuntimeError(f"{label}: evaluator returned the wrong record type")
    return value


def _require_qualified(
    value: QualifiedExecution | CheckResult,
    label: str,
) -> QualifiedExecution:
    if isinstance(value, CheckResult):
        raise RuntimeError(f"{label}: {value.code}: {value.detail}")
    if not isinstance(value, QualifiedExecution) or value.usage is None:
        raise RuntimeError(f"{label}: qualification returned the wrong type")
    return value


def _require_shape(value: RelationShape | CheckResult, label: str) -> RelationShape:
    if isinstance(value, CheckResult):
        raise RuntimeError(f"{label}: {value.code}: {value.detail}")
    return value


def _require_profile(
    value: ValidationProfile | CheckResult,
    label: str,
) -> ValidationProfile:
    if isinstance(value, CheckResult):
        raise RuntimeError(f"{label}: {value.code}: {value.detail}")
    return value


def _require_run_evidence(
    value: RelationRunEvidence | CheckResult,
    label: str,
) -> RelationRunEvidence:
    if isinstance(value, CheckResult):
        raise RuntimeError(f"{label}: {value.code}: {value.detail}")
    return value


def _require_hybrid(
    value: HybridFactorization | CheckResult,
    label: str,
) -> HybridFactorization:
    if isinstance(value, CheckResult):
        raise RuntimeError(f"{label}: {value.code}: {value.detail}")
    return value


def _replay_basis(repo_root: Path) -> dict[str, Any]:
    paths = tuple(Path(value) for value in REPORT_SOURCE_PATHS)
    sources = [
        {
            "path": str(path),
            "sha256": hashlib.sha256((repo_root / path).read_bytes()).hexdigest(),
        }
        for path in paths
    ]
    body = {"law": REPORT_REPLAY_LAW, "source_digests": sources}
    return {
        "id": semantic_id("r2.report-replay-basis.v1", body),
        **body,
    }


def _execution_manifest(role: str, qualified: QualifiedExecution) -> dict[str, Any]:
    if role not in EXECUTION_ROLES or qualified.usage is None:
        raise RuntimeError("execution manifest role or qualification differs")
    request = qualified.request
    record = qualified.record
    tape = request.coin_tape
    body = {
        "role": role,
        "interpretation": record.interpretation.value,
        "core_id": request.scenario.core.identity,
        "scenario_id": request.scenario.identity,
        "construction_id": request.scenario.construction.identity,
        "input_bundle_id": request.inputs.identity,
        "application_context_id": request.application_context.identity,
        "evaluator_basis_id": qualified.evaluator_basis.identity,
        "source_fixture_id": request.source_fixture_id,
        "source_package_id": request.source_package_id,
        "core_derivation": request.core_derivation.value,
        "request_id": request.identity,
        "record_id": record.identity,
        "qualification_id": qualified.identity,
        "coin_tape_id": tape.identity if tape is not None else None,
        "coin_tape_origin": tape.origin.value if tape is not None else None,
        "dependency_qualification_ids": [
            dependency.identity for dependency in qualified.dependencies
        ],
        "disposition": record.disposition.value,
        "execution_usage": record.usage.term(),
        "qualification_usage": qualified.usage.term(),
    }
    return {
        "manifest_id": semantic_id("r2.report-execution-manifest.v3", body),
        **body,
    }


def _relation_definition(
    name: str,
    shape: RelationShape,
    profile: ValidationProfile,
) -> dict[str, Any]:
    body = {
        "name": name,
        "shape": shape.summary(),
        "validation_profile": {
            "profile_id": profile.identity,
            "term": profile.term(),
        },
    }
    return {
        "definition_id": semantic_id("r2.report-relation-definition.v3", body),
        **body,
    }


def _relation_run(
    name: str,
    evidence: RelationRunEvidence,
    hybrid: HybridFactorization | None,
) -> dict[str, Any]:
    body = {
        "name": name,
        "run_evidence": {
            "run_evidence_id": evidence.identity,
            "term": evidence.term(),
        },
        "hybrid_factorization_id": hybrid.identity if hybrid is not None else None,
    }
    return {
        "run_manifest_id": semantic_id("r2.report-relation-run.v3", body),
        **body,
    }


def _add_case(
    cases: dict[str, dict[str, str]],
    evidence: dict[str, dict[str, Any]],
    *,
    name: str,
    law: str,
    subject_id: str,
    operand_ids: Mapping[str, str],
    result: CheckResult,
) -> None:
    if not _bounded_text(name) or name in cases:
        raise RuntimeError(f"duplicate or malformed report case: {name!r}")
    if not _bounded_text(law) or not _valid_id(subject_id):
        raise RuntimeError(f"{name}: malformed law or subject identity")
    if (
        not isinstance(operand_ids, Mapping)
        or not operand_ids
        or len(operand_ids) > MAX_REPORT_OPERANDS
        or any(not _bounded_text(role, 128) for role in operand_ids)
        or any(not _valid_id(value) for value in operand_ids.values())
    ):
        raise RuntimeError(f"{name}: malformed evidence operand map")
    if not isinstance(result, CheckResult):
        raise RuntimeError(f"{name}: checker returned the wrong result type")
    if result.outcome is OutcomeClass.CHECKER_FAILURE:
        raise RuntimeError(f"{name}: checker failure: {result.code}: {result.detail}")
    if result.subject and result.subject != subject_id:
        raise RuntimeError(f"{name}: checker subject differs from typed case subject")

    classification = {
        "outcome": result.outcome.value,
        "boundary": result.boundary,
        "code": result.code,
    }
    evidence_body = {
        "law": law,
        "subject_id": subject_id,
        "operand_ids": dict(operand_ids),
        "classification": classification,
    }
    evidence_id = semantic_id("r2.report-case-evidence.v1", evidence_body)
    if evidence_id in evidence:
        raise RuntimeError(f"{name}: evidence identity is already used by another case")
    evidence[evidence_id] = evidence_body
    cases[name] = {
        **classification,
        "subject_id": subject_id,
        "evidence_id": evidence_id,
    }


def _direct_mutation_portfolio(
    fs_scenario: Any,
) -> tuple[tuple[str, Any, CheckResult], ...]:
    direct = (
        Mutation.OMIT_STATEMENT,
        Mutation.DELAY_STATEMENT,
        Mutation.DUPLICATE_STATEMENT,
        Mutation.WRONG_STATEMENT_CODEC,
        Mutation.G1_WIRE_ONLY,
        Mutation.NONCE_WIRE_ONLY,
        Mutation.NAMESPACE_COLLISION,
        Mutation.VERIFIER_PRIVATE_DEPENDENCY,
        Mutation.G1_FUTURE_POW,
        Mutation.G1_FUTURE_QUERY,
        Mutation.ROUTE_ORDER,
        Mutation.MISSING_SAMPLER_CONTRACT,
        Mutation.UNSUPPORTED_SAMPLER,
    )
    result: list[tuple[str, Any, CheckResult]] = []
    for mutation in direct:
        scenario = mutate(fs_scenario, mutation)
        result.append((mutation.value, scenario, admit_scenario(scenario)))
    for mutation in (Mutation.POST_GRIND_ABSORB, Mutation.CONTINUE_AFTER_FAILED_POW):
        scenario = mutate(fs_scenario, mutation)
        result.append((mutation.value, scenario, grinding_applicability(scenario)))
    return tuple(result)


def _abort_execution(
    fs_qualified: QualifiedExecution,
) -> tuple[ExecutionRequest, ExecutionRecord]:
    winner = fs_qualified.record.prover_value("nonce")
    if winner > 0:
        request = replace(
            fs_qualified.request,
            nonce_search=NonceSearchPlan(0, winner),
        )
        return request, _require_record(
            execute(request, fs_qualified.evaluator_basis),
            "bounded FS abort",
        )
    for candidate in range(1, 1025):
        request = replace(
            fs_qualified.request,
            nonce_search=NonceSearchPlan(candidate, candidate + 1),
        )
        record = _require_record(
            execute(request, fs_qualified.evaluator_basis),
            "bounded FS abort search",
        )
        if record.disposition is TerminalKind.ABORT:
            return request, record
    raise RuntimeError("could not construct the bounded FS abort witness")


def build_report(repo_root: Path) -> dict[str, Any]:
    root = _bound_repo_root(repo_root)
    fixture = load_fixture(root)
    companion = load_fixture(root, companion=True)
    invocation = load_invocation(root)

    fs_scenario = base_scenario(fixture)
    fresh_grinding = fresh_grinding_scenario(fs_scenario)
    fresh_no_grinding = fresh_fri_scenario(fs_scenario)
    application_context = ApplicationContext(
        "zkc.r2.frigrind",
        "canonical-execution",
    )
    basis = build_evaluator_basis(
        root,
        {
            fs_scenario.construction.identity,
            fresh_grinding.construction.identity,
            fresh_no_grinding.construction.identity,
        },
    )
    source_fixture_id = f"sha256:{fixture.sha256}"
    source_package_id = invocation.identity

    fs_request = ExecutionRequest(
        fs_scenario,
        invocation.input_bundle,
        application_context,
        basis.identity,
        DEFAULT_RESOURCE_PLAN,
        CoreDerivationKind.FIXTURE_GRINDING_CORE,
        source_fixture_id,
        source_package_id,
        nonce_search=invocation.default_search,
    )
    fs_record = _require_record(execute(fs_request, basis), "FS execution")
    fs_qualified = _require_qualified(
        qualify_execution(fs_request, basis, fs_record),
        "FS qualification",
    )

    external_tape, external_nonce = load_external_fresh(
        root,
        fresh_grinding.core,
    )
    external_request = ExecutionRequest(
        fresh_grinding,
        invocation.input_bundle,
        application_context,
        basis.identity,
        DEFAULT_RESOURCE_PLAN,
        CoreDerivationKind.FIXTURE_GRINDING_CORE,
        source_fixture_id,
        source_package_id,
        fixed_nonce=external_nonce,
        coin_tape=external_tape,
    )
    external_record = _require_record(
        execute(external_request, basis),
        "external Fresh support-point execution",
    )
    external_qualified = _require_qualified(
        qualify_execution(external_request, basis, external_record),
        "external Fresh support-point qualification",
    )

    coupled_grinding_tape = coupled_fresh_tape(
        fs_qualified,
        fresh_grinding.core,
    )
    if isinstance(coupled_grinding_tape, CheckResult):
        raise RuntimeError(
            f"coupled grinding tape: {coupled_grinding_tape.code}: "
            f"{coupled_grinding_tape.detail}"
        )
    coupled_grinding_request = ExecutionRequest(
        fresh_grinding,
        invocation.input_bundle,
        application_context,
        basis.identity,
        DEFAULT_RESOURCE_PLAN,
        CoreDerivationKind.FIXTURE_GRINDING_CORE,
        source_fixture_id,
        source_package_id,
        fixed_nonce=FixedNoncePlan(fs_record.prover_value("nonce")),
        coin_tape=coupled_grinding_tape,
    )
    coupled_grinding_record = _require_record(
        execute(coupled_grinding_request, basis, (fs_qualified,)),
        "coupled Fresh grinding execution",
    )
    coupled_grinding_qualified = _require_qualified(
        qualify_execution(
            coupled_grinding_request,
            basis,
            coupled_grinding_record,
            (fs_qualified,),
        ),
        "coupled Fresh grinding qualification",
    )

    coupled_no_grinding_tape = coupled_fresh_tape(
        fs_qualified,
        fresh_no_grinding.core,
    )
    if isinstance(coupled_no_grinding_tape, CheckResult):
        raise RuntimeError(
            f"coupled no-grinding tape: {coupled_no_grinding_tape.code}: "
            f"{coupled_no_grinding_tape.detail}"
        )
    coupled_no_grinding_request = ExecutionRequest(
        fresh_no_grinding,
        invocation.input_bundle,
        application_context,
        basis.identity,
        DEFAULT_RESOURCE_PLAN,
        CoreDerivationKind.DROP_GRINDING_PROJECTION,
        source_fixture_id,
        source_package_id,
        coin_tape=coupled_no_grinding_tape,
    )
    coupled_no_grinding_record = _require_record(
        execute(coupled_no_grinding_request, basis, (fs_qualified,)),
        "coupled Fresh no-grinding execution",
    )
    coupled_no_grinding_qualified = _require_qualified(
        qualify_execution(
            coupled_no_grinding_request,
            basis,
            coupled_no_grinding_record,
            (fs_qualified,),
        ),
        "coupled Fresh no-grinding qualification",
    )

    qualified_by_role = {
        "fs_source": fs_qualified,
        "external_fresh_support_point": external_qualified,
        "coupled_fresh_grinding": coupled_grinding_qualified,
        "coupled_fresh_no_grinding": coupled_no_grinding_qualified,
    }
    executions = {
        role: _execution_manifest(role, qualified_by_role[role])
        for role in EXECUTION_ROLES
    }

    shared_shape = _require_shape(
        derive_relation_shape(
            fresh_grinding,
            fs_scenario,
            SubjectOrganization.SHARED_GRINDING_CORE,
        ),
        "shared relation shape",
    )
    shared_profile = _require_profile(
        derive_validation_profile(
            shared_shape,
            coupled_grinding_qualified,
            fs_qualified,
        ),
        "shared validation profile",
    )
    shared_run = _require_run_evidence(
        derive_relation_run_evidence(
            shared_shape,
            shared_profile,
            coupled_grinding_qualified,
            fs_qualified,
        ),
        "shared relation run evidence",
    )

    distinct_shape = _require_shape(
        derive_relation_shape(
            fresh_no_grinding,
            fs_scenario,
            SubjectOrganization.MAPPED_DISTINCT_CORES,
        ),
        "distinct relation shape",
    )
    distinct_profile = _require_profile(
        derive_validation_profile(
            distinct_shape,
            coupled_no_grinding_qualified,
            fs_qualified,
        ),
        "distinct validation profile",
    )
    distinct_run = _require_run_evidence(
        derive_relation_run_evidence(
            distinct_shape,
            distinct_profile,
            coupled_no_grinding_qualified,
            fs_qualified,
        ),
        "distinct relation run evidence",
    )
    hybrid = _require_hybrid(
        derive_hybrid_factorization(
            distinct_shape,
            distinct_profile,
            coupled_no_grinding_qualified,
            fs_qualified,
        ),
        "hybrid factorization",
    )

    definitions = {
        "shared": _relation_definition("shared", shared_shape, shared_profile),
        "distinct": _relation_definition("distinct", distinct_shape, distinct_profile),
    }
    relation_runs = {
        "shared": _relation_run("shared", shared_run, None),
        "distinct": _relation_run("distinct", distinct_run, hybrid),
    }
    relations = {"definitions": definitions, "runs": relation_runs}

    cases: dict[str, dict[str, str]] = {}
    evidence: dict[str, dict[str, Any]] = {}

    for name, scenario in (
        ("fs", fs_scenario),
        ("fresh-grinding", fresh_grinding),
        ("fresh-no-grinding", fresh_no_grinding),
    ):
        _add_case(
            cases,
            evidence,
            name=f"base/{name}-admission.v1",
            law="r2.closed-protocol-admission.v3",
            subject_id=scenario.identity,
            operand_ids={
                "core": scenario.core.identity,
                "construction": scenario.construction.identity,
                "scenario": scenario.identity,
            },
            result=admit_scenario(scenario),
        )
    _add_case(
        cases,
        evidence,
        name="base/grinding-applicability.v1",
        law="r2.grinding-shape-applicability.v1",
        subject_id=fs_scenario.identity,
        operand_ids={"scenario": fs_scenario.identity},
        result=grinding_applicability(fs_scenario),
    )

    relation_judgments = (
        ("typed-map", "r2.exact-typed-disposition-map.v3", check_typed_disposition_map),
        ("mapped-values", "r2.mapped-value-commutation.v3", compare_mapped_values),
        ("full-observations", "r2.full-observation-comparison.v3", compare_full_observations),
        ("origins", "r2.interpretation-sensitive-origin-comparison.v3", compare_origins),
        ("strategies", "r2.strategy-contract-relation.v3", compare_strategies),
    )
    for relation_name, shape, profile, run, fresh_qualified in (
        (
            "shared",
            shared_shape,
            shared_profile,
            shared_run,
            coupled_grinding_qualified,
        ),
        (
            "distinct",
            distinct_shape,
            distinct_profile,
            distinct_run,
            coupled_no_grinding_qualified,
        ),
    ):
        operands = {
            "relation_shape": shape.identity,
            "validation_profile": profile.identity,
            "relation_run": run.identity,
        }
        for judgment_name, law, checker in relation_judgments:
            _add_case(
                cases,
                evidence,
                name=f"relation/{relation_name}/{judgment_name}.v1",
                law=law,
                subject_id=shape.identity,
                operand_ids=operands,
                result=checker(shape, profile, fresh_qualified, fs_qualified),
            )

    hybrid_result = check_hybrid_factorization(
        hybrid,
        distinct_shape,
        distinct_profile,
        coupled_no_grinding_qualified,
        fs_qualified,
    )
    _add_case(
        cases,
        evidence,
        name="relation/distinct/hybrid-factorization.v1",
        law="r2.checked-hybrid-factorization.v3",
        subject_id=hybrid.identity,
        operand_ids={
            "factorization": hybrid.identity,
            "relation_shape": distinct_shape.identity,
            "validation_profile": distinct_profile.identity,
            "relation_run": distinct_run.identity,
        },
        result=hybrid_result,
    )

    for mutation_name, scenario, result in _direct_mutation_portfolio(fs_scenario):
        _add_case(
            cases,
            evidence,
            name=f"mutation/{mutation_name}.v1",
            law="r2.named-frigrind-mutation-classification.v3",
            subject_id=scenario.identity,
            operand_ids={
                "scenario": scenario.identity,
                "core": scenario.core.identity,
                "construction": scenario.construction.identity,
            },
            result=result,
        )

    abort_request, abort_record = _abort_execution(fs_qualified)
    _add_case(
        cases,
        evidence,
        name="execution/fs-search-exhaustion-abort-terminal.v1",
        law="r2.exact-terminal-law.v3",
        subject_id=abort_record.identity,
        operand_ids={
            "scenario": abort_request.scenario.identity,
            "request": abort_request.identity,
            "record": abort_record.identity,
        },
        result=validate_terminal_law(abort_request, abort_record),
    )

    over_budget_request = replace(
        fs_request,
        resources=replace(DEFAULT_RESOURCE_PLAN, max_nonce_candidates=1),
    )
    over_budget_result = execute(over_budget_request, basis)
    if not isinstance(over_budget_result, CheckResult):
        raise RuntimeError("pre-admission resource exhaustion unexpectedly executed")
    _add_case(
        cases,
        evidence,
        name="execution/pre-admission-resource-exhaustion.v1",
        law="r2.aggregate-execution-resource-admission.v3",
        subject_id=over_budget_request.identity,
        operand_ids={
            "request": over_budget_request.identity,
            "scenario": fs_scenario.identity,
            "evaluator_basis": basis.identity,
        },
        result=over_budget_result,
    )

    low_qualification_basis = build_evaluator_basis(
        root,
        {
            fs_scenario.construction.identity,
            fresh_grinding.construction.identity,
        },
        qualification_caps=replace(
            MAX_QUALIFICATION_CAPS,
            max_total_trace_events=1,
        ),
    )
    low_qualification_request = replace(
        external_request,
        evaluator_basis_id=low_qualification_basis.identity,
    )
    low_qualification_result = qualification_worst_case(
        low_qualification_request,
        low_qualification_basis,
    )
    if not isinstance(low_qualification_result, CheckResult):
        raise RuntimeError("qualification-cap exhaustion unexpectedly admitted")
    _add_case(
        cases,
        evidence,
        name="execution/qualification-cap-exhaustion.v1",
        law="r2.aggregate-qualification-resource-admission.v3",
        subject_id=low_qualification_request.identity,
        operand_ids={
            "request": low_qualification_request.identity,
            "evaluator_basis": low_qualification_basis.identity,
            "scenario": fresh_grinding.identity,
        },
        result=low_qualification_result,
    )

    protocol_statement = protocol_statement_occurrence(fs_qualified)
    if isinstance(protocol_statement, CheckResult):
        raise RuntimeError(
            f"protocol Statement occurrence: {protocol_statement.code}: "
            f"{protocol_statement.detail}"
        )
    _add_case(
        cases,
        evidence,
        name="bridge/statement-correspondence.v1",
        law="r2.grounded-pointwise-statement-correspondence.v3",
        subject_id=fs_qualified.identity,
        operand_ids={
            "protocol_qualification": fs_qualified.identity,
            "protocol_statement": protocol_statement.identity,
        },
        result=statement_correspondence(fs_qualified),
    )
    substituted_statement_result = CheckResult(
        OutcomeClass.NOT_EXERCISED,
        "scope:substituted-statement-influence",
        "R2-SCOPE-002",
        "substituted Statement influence is not exercised without an independently qualified relation-side operand",
        fs_qualified.identity,
    )
    _add_case(
        cases,
        evidence,
        name="scope/substituted-statement-influence-not-exercised.v1",
        law="r2.substituted-statement-influence-not-exercised.v1",
        subject_id=fs_qualified.identity,
        operand_ids={
            "protocol_qualification": fs_qualified.identity,
            "protocol_statement": protocol_statement.identity,
        },
        result=substituted_statement_result,
    )

    base_fixture_id = f"sha256:{fixture.sha256}"
    companion_fixture_id = f"sha256:{companion.sha256}"
    reference_request = AnchorReadRequest(
        "contract",
        AnchorCapability.REFERENCE_VALUE,
    )
    source_request = AnchorReadRequest(
        "contract",
        AnchorCapability.SEMANTIC_SOURCE_BYTES,
    )
    reference_request_id = semantic_id(
        "r2.anchor-read-request.v3",
        {
            "fixture": base_fixture_id,
            "label": reference_request.label,
            "capability": reference_request.capability.value,
        },
    )
    source_request_id = semantic_id(
        "r2.anchor-read-request.v3",
        {
            "fixture": base_fixture_id,
            "label": source_request.label,
            "capability": source_request.capability.value,
        },
    )
    base_projection = classify_projection(fixture)
    companion_projection = classify_projection(companion)
    projection_fact_id = semantic_id(
        "r2.report-projection-fact.v1",
        {
            "fixture": companion_fixture_id,
            "anchor": companion_projection.evidence.get("anchor"),
            "projected_limbs": companion_projection.evidence.get("projected_limbs"),
            "input_bits": companion_projection.evidence.get("input_bits"),
            "output_bits": companion_projection.evidence.get("output_bits"),
            "truncated_bits": companion_projection.evidence.get("truncated_bits"),
        },
    )
    for name, law, subject, operands, result in (
        (
            "base-projection",
            "r2.relation-anchor-projection.v3",
            base_fixture_id,
            {"fixture": base_fixture_id},
            base_projection,
        ),
        (
            "companion-projection",
            "r2.relation-anchor-projection.v3",
            companion_fixture_id,
            {"fixture": companion_fixture_id, "projection_fact": projection_fact_id},
            companion_projection,
        ),
        (
            "companion-projection-loss",
            "r2.projection-loss-applicability.v3",
            companion_fixture_id,
            {"fixture": companion_fixture_id, "projection_fact": projection_fact_id},
            projection_loss_applicability(companion),
        ),
        (
            "anchor-reference-read",
            "r2.anchor-reference-authority.v3",
            base_fixture_id,
            {"fixture": base_fixture_id, "request": reference_request_id},
            check_anchor_authority(fixture, reference_request),
        ),
        (
            "anchor-source-bytes-refusal",
            "r2.anchor-source-authority.v3",
            base_fixture_id,
            {"fixture": base_fixture_id, "request": source_request_id},
            check_anchor_authority(fixture, source_request),
        ),
    ):
        _add_case(
            cases,
            evidence,
            name=f"anchor/{name}.v1",
            law=law,
            subject_id=subject,
            operand_ids=operands,
            result=result,
        )

    external_scope = CheckResult(
        OutcomeClass.NOT_EXERCISED,
        "scope:fresh-distribution-evidence",
        "R2-SCOPE-001",
        "one external non-FS-derived support point does not exercise a distributional claim",
        external_qualified.identity,
    )
    assert external_tape.origin is FreshTapeOrigin.EXTERNAL_FIXTURE
    _add_case(
        cases,
        evidence,
        name="scope/external-fresh-support-point-only.v1",
        law="r2.external-non-fs-derived-fresh-support-point-only.v1",
        subject_id=external_qualified.identity,
        operand_ids={
            "qualification": external_qualified.identity,
            "request": external_request.identity,
            "coin_tape": external_tape.identity,
            "construction": fresh_grinding.construction.identity,
            "frozen_source": external_tape.source_id,
        },
        result=external_scope,
    )

    if len(cases) > MAX_REPORT_CASES or len(evidence) > MAX_REPORT_EVIDENCE:
        raise RuntimeError("canonical report exceeds its case or evidence bound")

    semantic_roots_body = {
        "source_fixture_id": source_fixture_id,
        "companion_fixture_id": companion_fixture_id,
        "source_package_id": source_package_id,
        "input_bundle_id": invocation.input_bundle.identity,
        "application_context_id": application_context.identity,
        "evaluator_basis_id": basis.identity,
        "core_ids": {
            "grinding": fs_scenario.core.identity,
            "no_grinding": fresh_no_grinding.core.identity,
        },
        "scenario_ids": {
            "fs_grinding": fs_scenario.identity,
            "fresh_grinding": fresh_grinding.identity,
            "fresh_no_grinding": fresh_no_grinding.identity,
        },
    }
    semantic_roots = {
        "semantic_roots_id": semantic_id(
            "r2.report-semantic-roots.v3",
            semantic_roots_body,
        ),
        **semantic_roots_body,
    }

    exercised = sorted({entry["outcome"] for entry in cases.values()})
    declared = [outcome.value for outcome in OutcomeClass]
    scope_body = {
        "authority": "none; finite executable semantic witness",
        "external_fresh_boundary": {
            "qualification_id": external_qualified.identity,
            "classification": "one external non-FS-derived Fresh support point",
            "does_not_establish": [
                "uniform sampling",
                "statistical independence",
                "honest preselection",
                "general strategy causality",
                "soundness",
            ],
        },
        "outcomes": {
            "declared": declared,
            "exercised": exercised,
            "unexercised": sorted(set(declared) - set(exercised)),
        },
        "open_obligations": [
            "independently qualified relation-side Statement operand",
            "native oracle and FRI semantics",
            "distributional and cryptographic property transport",
            "general strategy-parameterized execution semantics",
        ],
        "non_claims": [
            "no FRI correctness or soundness result",
            "no Fiat-Shamir security result",
            "no distributional Fresh-coin evidence",
            "no implementation conformance or final architecture selection",
        ],
    }
    scope = {
        "scope_id": semantic_id("r2.report-scope.v3", scope_body),
        "body": scope_body,
    }

    replay_basis = _replay_basis(root)
    root_ids = {
        "replay_basis_id": replay_basis["id"],
        "semantic_roots_id": semantic_roots["semantic_roots_id"],
        "execution_index_id": semantic_id(
            "r2.report-execution-index.v3",
            {role: executions[role]["manifest_id"] for role in EXECUTION_ROLES},
        ),
        "relation_definition_index_id": semantic_id(
            "r2.report-relation-definition-index.v3",
            {
                name: definitions[name]["definition_id"]
                for name in RELATION_NAMES
            },
        ),
        "relation_run_index_id": semantic_id(
            "r2.report-relation-run-index.v3",
            {
                name: relation_runs[name]["run_manifest_id"]
                for name in RELATION_NAMES
            },
        ),
        "case_index_id": semantic_id(
            "r2.report-case-index.v3",
            {name: cases[name]["evidence_id"] for name in sorted(cases)},
        ),
        "scope_id": scope["scope_id"],
    }
    report = {
        "schema": SCHEMA,
        "semantic_regime_id": SEMANTIC_REGIME_ID,
        "replay_basis": replay_basis,
        "semantic_roots": semantic_roots,
        "executions": executions,
        "relations": relations,
        "cases": cases,
        "evidence": evidence,
        "scope": scope,
        "root_ids": root_ids,
    }
    report["report_id"] = semantic_id(
        "r2.protocol-model-report.v3",
        {
            "schema": SCHEMA,
            "semantic_regime_id": SEMANTIC_REGIME_ID,
            "root_ids": root_ids,
        },
    )
    return report


def _verify_replay_basis(value: Any, repo_root: Path) -> list[str]:
    errors: list[str] = []
    if not isinstance(value, dict) or set(value) != {"id", "law", "source_digests"}:
        return ["replay basis shape differs"]
    sources = value.get("source_digests")
    if (
        value.get("law") != REPORT_REPLAY_LAW
        or not isinstance(sources, list)
        or not sources
        or len(sources) > MAX_REPORT_SOURCES
        or tuple(
            source.get("path") if isinstance(source, dict) else None
            for source in sources
        )
        != REPORT_SOURCE_PATHS
    ):
        return ["replay basis law, source set, or source bound differs"]
    seen: set[str] = set()
    for index, source in enumerate(sources):
        if (
            not isinstance(source, dict)
            or set(source) != {"path", "sha256"}
            or not _bounded_text(source.get("path"))
            or not isinstance(source.get("sha256"), str)
            or _HEX_DIGEST.fullmatch(source["sha256"]) is None
            or source["path"] in seen
        ):
            errors.append(f"replay basis source {index} is malformed")
            continue
        seen.add(source["path"])
        try:
            actual = hashlib.sha256((repo_root / source["path"]).read_bytes()).hexdigest()
        except OSError as error:
            errors.append(f"replay basis source {source['path']} is unavailable: {error}")
            continue
        if source["sha256"] != actual:
            errors.append(f"replay basis source {source['path']} digest differs")
    body = {"law": value.get("law"), "source_digests": sources}
    try:
        expected = semantic_id("r2.report-replay-basis.v1", body)
    except (TypeError, ValueError):
        errors.append("replay basis identity preimage is not canonical")
    else:
        if value.get("id") != expected:
            errors.append("replay basis identity differs")
    return errors


def _verify_semantic_roots(value: Any) -> list[str]:
    if not isinstance(value, dict):
        return ["semantic roots have the wrong type"]
    required = {
        "semantic_roots_id",
        "source_fixture_id",
        "companion_fixture_id",
        "source_package_id",
        "input_bundle_id",
        "application_context_id",
        "evaluator_basis_id",
        "core_ids",
        "scenario_ids",
    }
    if set(value) != required:
        return ["semantic root keys differ"]
    ids = [
        value[name]
        for name in (
            "source_fixture_id",
            "companion_fixture_id",
            "source_package_id",
            "input_bundle_id",
            "application_context_id",
            "evaluator_basis_id",
        )
    ]
    core_ids = value.get("core_ids")
    scenario_ids = value.get("scenario_ids")
    if (
        not isinstance(core_ids, dict)
        or set(core_ids) != {"grinding", "no_grinding"}
        or not isinstance(scenario_ids, dict)
        or set(scenario_ids) != {
            "fs_grinding",
            "fresh_grinding",
            "fresh_no_grinding",
        }
        or any(not _valid_id(item) for item in (*ids, *core_ids.values(), *scenario_ids.values()))
    ):
        return ["semantic root identity vocabulary differs"]
    body = {name: value[name] for name in required - {"semantic_roots_id"}}
    expected = semantic_id("r2.report-semantic-roots.v3", body)
    return [] if value["semantic_roots_id"] == expected else ["semantic roots identity differs"]


def _verify_execution_manifests(value: Any, roots: Mapping[str, Any]) -> list[str]:
    errors: list[str] = []
    if not isinstance(value, dict) or set(value) != set(EXECUTION_ROLES):
        return ["execution role set differs"]
    for role in EXECUTION_ROLES:
        manifest = value[role]
        if not isinstance(manifest, dict) or set(manifest) != _EXECUTION_MANIFEST_KEYS:
            errors.append(f"{role}: execution manifest keys differ")
            continue
        body = {key: manifest[key] for key in _EXECUTION_MANIFEST_KEYS - {"manifest_id"}}
        try:
            expected = semantic_id("r2.report-execution-manifest.v3", body)
        except (TypeError, ValueError):
            errors.append(f"{role}: execution manifest preimage is not canonical")
            continue
        if manifest["manifest_id"] != expected or manifest["role"] != role:
            errors.append(f"{role}: execution manifest identity or role differs")
        id_fields = (
            "core_id",
            "scenario_id",
            "construction_id",
            "input_bundle_id",
            "application_context_id",
            "evaluator_basis_id",
            "source_fixture_id",
            "source_package_id",
            "request_id",
            "record_id",
            "qualification_id",
        )
        if any(not _valid_id(manifest[name]) for name in id_fields):
            errors.append(f"{role}: execution manifest contains a malformed identity")
        dependencies = manifest["dependency_qualification_ids"]
        if (
            not isinstance(dependencies, list)
            or len(dependencies) > 1
            or any(not _valid_id(item) for item in dependencies)
        ):
            errors.append(f"{role}: dependency identity list differs")
        for usage_name, expected_keys in (
            ("execution_usage", _EXECUTION_USAGE_KEYS),
            ("qualification_usage", _QUALIFICATION_USAGE_KEYS),
        ):
            usage = manifest[usage_name]
            if (
                not isinstance(usage, dict)
                or set(usage) != expected_keys
                or any(
                    not isinstance(number, int) or isinstance(number, bool) or number < 0
                    for number in usage.values()
                )
            ):
                errors.append(f"{role}: {usage_name} is malformed")
        if manifest["disposition"] != TerminalKind.SOURCE_RESIDUAL.value:
            errors.append(f"{role}: canonical disposition differs")

    if errors:
        return errors
    fs = value["fs_source"]
    external = value["external_fresh_support_point"]
    coupled = value["coupled_fresh_grinding"]
    no_grind = value["coupled_fresh_no_grinding"]
    if (
        fs["coin_tape_id"] is not None
        or fs["coin_tape_origin"] is not None
        or fs["dependency_qualification_ids"]
        or fs["scenario_id"] != roots["scenario_ids"]["fs_grinding"]
        or fs["core_id"] != roots["core_ids"]["grinding"]
    ):
        errors.append("FS execution role law differs")
    if (
        not _valid_id(external["coin_tape_id"])
        or external["coin_tape_origin"] != FreshTapeOrigin.EXTERNAL_FIXTURE.value
        or external["dependency_qualification_ids"]
        or external["scenario_id"] != roots["scenario_ids"]["fresh_grinding"]
        or external["core_id"] != roots["core_ids"]["grinding"]
    ):
        errors.append("external Fresh support-point role law differs")
    for role, manifest, expected_scenario, expected_core in (
        (
            "coupled Fresh grinding",
            coupled,
            roots["scenario_ids"]["fresh_grinding"],
            roots["core_ids"]["grinding"],
        ),
        (
            "coupled Fresh no-grinding",
            no_grind,
            roots["scenario_ids"]["fresh_no_grinding"],
            roots["core_ids"]["no_grinding"],
        ),
    ):
        if (
            not _valid_id(manifest["coin_tape_id"])
            or manifest["coin_tape_origin"] != FreshTapeOrigin.DERIVED_EXECUTION.value
            or manifest["dependency_qualification_ids"] != [fs["qualification_id"]]
            or manifest["scenario_id"] != expected_scenario
            or manifest["core_id"] != expected_core
        ):
            errors.append(f"{role} role law differs")
    return errors


def _verify_relations(value: Any, executions: Mapping[str, Any]) -> list[str]:
    errors: list[str] = []
    if not isinstance(value, dict) or set(value) != {"definitions", "runs"}:
        return ["relation report shape differs"]
    definitions, runs = value["definitions"], value["runs"]
    if (
        not isinstance(definitions, dict)
        or set(definitions) != set(RELATION_NAMES)
        or not isinstance(runs, dict)
        or set(runs) != set(RELATION_NAMES)
    ):
        return ["relation definition or run set differs"]
    for name in RELATION_NAMES:
        definition = definitions[name]
        if (
            not isinstance(definition, dict)
            or set(definition) != {
                "definition_id",
                "name",
                "shape",
                "validation_profile",
            }
            or definition.get("name") != name
        ):
            errors.append(f"{name}: relation definition shape differs")
            continue
        shape = definition["shape"]
        profile = definition["validation_profile"]
        if (
            not isinstance(shape, dict)
            or set(shape) != {
                "shape_id",
                "organization",
                "fresh_core_id",
                "fs_core_id",
                "fresh_action_count",
                "fs_action_count",
            }
            or not _valid_id(shape.get("shape_id"))
            or not isinstance(profile, dict)
            or set(profile) != {"profile_id", "term"}
            or not isinstance(profile.get("term"), dict)
            or set(profile["term"]) != _PROFILE_TERM_KEYS
        ):
            errors.append(f"{name}: relation definition vocabulary differs")
            continue
        try:
            expected_profile = semantic_id(
                "r2.relation-validation-profile.v3",
                profile["term"],
            )
        except (TypeError, ValueError):
            errors.append(f"{name}: validation profile preimage is not canonical")
            continue
        if profile["profile_id"] != expected_profile:
            errors.append(f"{name}: validation profile identity differs")
        body = {
            "name": name,
            "shape": shape,
            "validation_profile": profile,
        }
        try:
            expected_definition = semantic_id(
                "r2.report-relation-definition.v3",
                body,
            )
        except (TypeError, ValueError):
            errors.append(f"{name}: relation definition preimage is not canonical")
        else:
            if definition["definition_id"] != expected_definition:
                errors.append(f"{name}: relation definition identity differs")

        run = runs[name]
        if (
            not isinstance(run, dict)
            or set(run) != {
                "run_manifest_id",
                "name",
                "run_evidence",
                "hybrid_factorization_id",
            }
            or run.get("name") != name
        ):
            errors.append(f"{name}: relation run shape differs")
            continue
        run_evidence = run["run_evidence"]
        if (
            not isinstance(run_evidence, dict)
            or set(run_evidence) != {"run_evidence_id", "term"}
            or not isinstance(run_evidence.get("term"), dict)
            or set(run_evidence["term"]) != _RUN_EVIDENCE_TERM_KEYS
        ):
            errors.append(f"{name}: relation run evidence shape differs")
            continue
        term = run_evidence["term"]
        run_ids = tuple(
            term[key]
            for key in (
                "relation_shape_id",
                "validation_profile_id",
                "fresh_qualification_id",
                "fs_qualification_id",
                "fresh_request_id",
                "fs_request_id",
                "fresh_record_id",
                "fs_record_id",
                "fresh_coin_tape_id",
            )
        )
        dependency_lists = (
            term["fresh_dependency_qualification_ids"],
            term["fs_dependency_qualification_ids"],
        )
        if (
            any(not _valid_id(value) for value in run_ids)
            or any(
                not isinstance(values, list)
                or len(values) > 1
                or any(not _valid_id(value) for value in values)
                for values in dependency_lists
            )
        ):
            errors.append(f"{name}: relation run identity vocabulary differs")
            continue
        try:
            expected_run = semantic_id(
                "r2.relation-run-evidence.v3",
                term,
            )
        except (TypeError, ValueError):
            errors.append(f"{name}: relation run evidence preimage is not canonical")
            continue
        if run_evidence["run_evidence_id"] != expected_run:
            errors.append(f"{name}: relation run evidence identity differs")
        expected_fresh_role = (
            "coupled_fresh_grinding"
            if name == "shared"
            else "coupled_fresh_no_grinding"
        )
        if (
            term["relation_shape_id"] != shape["shape_id"]
            or term["validation_profile_id"] != profile["profile_id"]
            or term["fresh_qualification_id"]
            != executions[expected_fresh_role]["qualification_id"]
            or term["fs_qualification_id"]
            != executions["fs_source"]["qualification_id"]
        ):
            errors.append(f"{name}: relation run bindings differ")
        hybrid_id = run["hybrid_factorization_id"]
        if (name == "shared" and hybrid_id is not None) or (
            name == "distinct" and not _valid_id(hybrid_id)
        ):
            errors.append(f"{name}: hybrid factorization placement differs")
        run_body = {
            "name": name,
            "run_evidence": run_evidence,
            "hybrid_factorization_id": hybrid_id,
        }
        try:
            expected_manifest = semantic_id(
                "r2.report-relation-run.v3",
                run_body,
            )
        except (TypeError, ValueError):
            errors.append(f"{name}: relation run manifest preimage is not canonical")
        else:
            if run["run_manifest_id"] != expected_manifest:
                errors.append(f"{name}: relation run manifest identity differs")
    return errors


def _verify_cases_and_evidence(cases: Any, evidence: Any) -> list[str]:
    errors: list[str] = []
    if (
        not isinstance(cases, dict)
        or not cases
        or len(cases) > MAX_REPORT_CASES
        or not isinstance(evidence, dict)
        or len(evidence) != len(cases)
        or len(evidence) > MAX_REPORT_EVIDENCE
    ):
        return ["case or evidence aggregate bound differs"]
    referenced: list[str] = []
    for name, case in cases.items():
        if not _bounded_text(name) or not isinstance(case, dict) or set(case) != {
            "outcome",
            "boundary",
            "code",
            "subject_id",
            "evidence_id",
        }:
            errors.append(f"{name!r}: case shape differs")
            continue
        try:
            outcome = OutcomeClass(case["outcome"])
        except (TypeError, ValueError):
            errors.append(f"{name}: outcome is unknown")
            continue
        if (
            outcome is OutcomeClass.CHECKER_FAILURE
            or not _bounded_text(case["boundary"])
            or not _bounded_text(case["code"], 128)
            or not _valid_id(case["subject_id"])
            or not _valid_id(case["evidence_id"])
        ):
            errors.append(f"{name}: case vocabulary differs")
            continue
        referenced.append(case["evidence_id"])
        body = evidence.get(case["evidence_id"])
        if (
            not isinstance(body, dict)
            or set(body) != {"law", "subject_id", "operand_ids", "classification"}
            or not _bounded_text(body.get("law"))
            or body.get("subject_id") != case["subject_id"]
            or not isinstance(body.get("operand_ids"), dict)
            or not body["operand_ids"]
            or len(body["operand_ids"]) > MAX_REPORT_OPERANDS
            or any(not _bounded_text(role, 128) for role in body["operand_ids"])
            or any(not _valid_id(item) for item in body["operand_ids"].values())
            or body.get("classification")
            != {
                "outcome": case["outcome"],
                "boundary": case["boundary"],
                "code": case["code"],
            }
        ):
            errors.append(f"{name}: evidence body differs")
            continue
        try:
            expected = semantic_id("r2.report-case-evidence.v1", body)
        except (TypeError, ValueError):
            errors.append(f"{name}: evidence preimage is not canonical")
        else:
            if case["evidence_id"] != expected:
                errors.append(f"{name}: evidence identity differs")
    if len(referenced) != len(set(referenced)):
        errors.append("case evidence is not one-to-one")
    if set(referenced) != set(evidence):
        errors.append("evidence sidecar has a missing or orphaned entry")
    return errors


def verify_report(report: Any, repo_root: Path) -> list[str]:
    errors: list[str] = []
    required = {
        "schema",
        "semantic_regime_id",
        "replay_basis",
        "semantic_roots",
        "executions",
        "relations",
        "cases",
        "evidence",
        "scope",
        "root_ids",
        "report_id",
    }
    if not isinstance(report, dict) or set(report) != required:
        return ["report envelope keys differ"]
    if report.get("schema") != SCHEMA:
        errors.append("report schema differs")
    if not supports_semantic_regime(report.get("semantic_regime_id")):
        errors.append("semantic regime is unsupported")

    try:
        root = _bound_repo_root(repo_root)
    except ValueError as error:
        return [str(error)]
    errors.extend(_verify_replay_basis(report["replay_basis"], root))
    semantic_root_errors = _verify_semantic_roots(report["semantic_roots"])
    errors.extend(semantic_root_errors)
    execution_errors: list[str] = []
    if not semantic_root_errors:
        execution_errors = _verify_execution_manifests(
            report["executions"],
            report["semantic_roots"],
        )
    else:
        errors.append("execution manifests have no semantic roots")
    errors.extend(execution_errors)
    if not semantic_root_errors and not execution_errors:
        errors.extend(
            _verify_relations(report["relations"], report["executions"])
        )
    else:
        errors.append("relations have no admitted execution manifest map")
    errors.extend(_verify_cases_and_evidence(report["cases"], report["evidence"]))

    scope = report["scope"]
    if (
        not isinstance(scope, dict)
        or set(scope) != {"scope_id", "body"}
        or not isinstance(scope.get("body"), dict)
    ):
        errors.append("report scope shape differs")
    else:
        try:
            expected_scope = semantic_id("r2.report-scope.v3", scope["body"])
        except (TypeError, ValueError):
            errors.append("report scope is not a bounded canonical term")
        else:
            if scope["scope_id"] != expected_scope:
                errors.append("report scope identity differs")

    root_ids = report["root_ids"]
    expected_root_keys = {
        "replay_basis_id",
        "semantic_roots_id",
        "execution_index_id",
        "relation_definition_index_id",
        "relation_run_index_id",
        "case_index_id",
        "scope_id",
    }
    if not isinstance(root_ids, dict) or set(root_ids) != expected_root_keys:
        errors.append("report root index shape differs")
    elif not all(_valid_id(value) for value in root_ids.values()):
        errors.append("report root index contains a malformed identity")
    elif (
        isinstance(report["executions"], dict)
        and isinstance(report["relations"], dict)
        and isinstance(report["cases"], dict)
        and isinstance(report["scope"], dict)
    ):
        try:
            expected_roots = {
                "replay_basis_id": report["replay_basis"]["id"],
                "semantic_roots_id": report["semantic_roots"]["semantic_roots_id"],
                "execution_index_id": semantic_id(
                    "r2.report-execution-index.v3",
                    {
                        role: report["executions"][role]["manifest_id"]
                        for role in EXECUTION_ROLES
                    },
                ),
                "relation_definition_index_id": semantic_id(
                    "r2.report-relation-definition-index.v3",
                    {
                        name: report["relations"]["definitions"][name]["definition_id"]
                        for name in RELATION_NAMES
                    },
                ),
                "relation_run_index_id": semantic_id(
                    "r2.report-relation-run-index.v3",
                    {
                        name: report["relations"]["runs"][name]["run_manifest_id"]
                        for name in RELATION_NAMES
                    },
                ),
                "case_index_id": semantic_id(
                    "r2.report-case-index.v3",
                    {
                        name: report["cases"][name]["evidence_id"]
                        for name in sorted(report["cases"])
                    },
                ),
                "scope_id": report["scope"]["scope_id"],
            }
        except (KeyError, TypeError, ValueError):
            errors.append("report root index dependencies are malformed")
        else:
            if root_ids != expected_roots:
                errors.append("report root index identities differ")

    if isinstance(root_ids, dict):
        try:
            expected_report_id = semantic_id(
                "r2.protocol-model-report.v3",
                {
                    "schema": report.get("schema"),
                    "semantic_regime_id": report.get("semantic_regime_id"),
                    "root_ids": root_ids,
                },
            )
        except (TypeError, ValueError):
            errors.append("report identity preimage is not canonical")
        else:
            if report.get("report_id") != expected_report_id:
                errors.append("report identity differs")

    if errors:
        return errors
    try:
        canonical = build_report(root)
    except (OSError, TypeError, ValueError, RuntimeError, KeyError) as error:
        return [f"canonical replay failed: {error}"]
    if report != canonical:
        errors.append("report differs from canonical replay")
    return errors
