"""Bounded K3-E cross-consumer closure witness.

This package loads and evaluates the existing K3-C Analysis and K3-D
OIR-projection instruments side by side without reimplementing either model.
It loads K3-C first and then K3-D, checks that both reach the same canonical
K3-B/K2/K1 module objects, and derives both branches independently from one
concrete K3-B case object.

The correspondence between branches is an inert tuple of typed owner IDs.
No K3-C source, profile, judgment, or capability is passed to K3-D, and K3-E
does not execute K3-C family transport or pointwise specialization.  K3-D, not
this package, checks its future-only supplement against live owner-issued
K2/K3-B views and issues the purpose-bound adapter consumed by projection.
This module never compares two integration-authored encodings and never treats
a passing finite witness as a general semantic or cryptographic proof.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
import importlib.util
from pathlib import Path
import sys


EVALUATION_ROOT = Path(__file__).resolve().parents[1]
ANALYSIS_PATH = EVALUATION_ROOT / "k3-analysis-closure" / "reference_model.py"
OIR_PATH = EVALUATION_ROOT / "k3-oir-projection" / "reference_model.py"
K3B_PATH = EVALUATION_ROOT / "k3-dependent-surfaces" / "reference_model.py"
K2_PATH = EVALUATION_ROOT / "k2-protocol-fiat-shamir" / "reference_model.py"
K1_PATH = EVALUATION_ROOT / "k1-executable-foundations" / "reference_model.py"


class IntegrationError(RuntimeError):
    """One supposedly affirmative cross-consumer lane failed."""


def _load_exact(name: str, path: Path) -> object:
    existing = sys.modules.get(name)
    if existing is not None:
        if Path(existing.__file__).resolve() != path.resolve():
            raise ImportError(f"{name} was already loaded from another path")
        return existing
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:  # pragma: no cover - host fault
        raise ImportError(f"cannot load {name} from {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


# Order is intentional.  Loading Analysis installs the canonical K3-B chain;
# OIR must reuse those module objects rather than load a parallel type universe.
analysis = _load_exact("_zkc_k3_analysis_closure", ANALYSIS_PATH)
oir = _load_exact("_zkc_k3_oir_projection", OIR_PATH)
k3 = analysis.k3
k2 = analysis.k2
k1 = analysis.k1


def assert_canonical_import_chain() -> tuple[Path, ...]:
    modules_and_paths = (
        (analysis, ANALYSIS_PATH),
        (oir, OIR_PATH),
        (k3, K3B_PATH),
        (k2, K2_PATH),
        (k1, K1_PATH),
    )
    if not (
        analysis.k3 is oir.k3 is k3
        and analysis.k2 is oir.k2 is k3.k2 is k2
        and analysis.k1 is oir.k1 is k3.k1 is k2.k1 is k1
    ):
        raise ImportError("K3-C and K3-D do not share one canonical owner chain")
    resolved = tuple(Path(module.__file__).resolve() for module, _ in modules_and_paths)
    expected = tuple(path.resolve() for _, path in modules_and_paths)
    if resolved != expected:
        raise ImportError(
            "consumer modules were not loaded from the exact evaluation files"
        )
    return resolved


CANONICAL_IMPORT_FILES = assert_canonical_import_chain()


def model_chain() -> tuple[object, object, object]:
    """Expose the exact shared owner modules without another import path."""

    return k3, k2, k1


@dataclass(frozen=True)
class AnalysisLanes:
    """Owner-derived Analysis records, not a live specialization result."""

    relation: object
    fresh_fs: object
    finite_profile: object


@dataclass(frozen=True)
class EndpointLane:
    request: object
    basis: object
    adapter: object
    source: object
    produced: object
    admitted: object
    validation: object
    checked: object


@dataclass(frozen=True)
class SharedOwnerAnchors:
    """Inert union of owner IDs; not every field is read by both consumers."""

    core_id: object
    construction_id: object
    fresh_protocol_id: object
    fiat_shamir_protocol_id: object
    interface_id: object
    plan_id: object
    relation_interface_id: object
    protocol_binding_id: object
    plan_binding_id: object


@dataclass(frozen=True)
class IntegratedWitness:
    case: object
    analysis_lanes: AnalysisLanes
    verifier: EndpointLane
    prover: EndpointLane
    anchors: SharedOwnerAnchors


@dataclass(frozen=True)
class IdentitySnapshot:
    """Observed content and validation identities, with no authority carriers."""

    anchors: SharedOwnerAnchors
    fresh_manifest_id: object
    pair_manifest_id: object
    finite_profile_id: object | None
    verifier_source_id: object
    verifier_oir_id: object
    verifier_proposition_id: object
    verifier_validation_id: object
    prover_source_id: object
    prover_oir_id: object
    prover_proposition_id: object
    prover_validation_id: object


def _affirmative(answer: object, stage: str) -> object:
    if answer.kind is not oir.OutcomeKind.AFFIRMATIVE:
        raise IntegrationError(
            f"{stage} did not affirm: {answer.kind.value}: {answer.reason}"
        )
    return answer.value


def derive_analysis_lanes(
    case: object,
    *,
    require_finite_profile: bool = True,
    relation_witness_slot: str = "secret",
) -> AnalysisLanes:
    """Derive sources and one finite descriptor, never a property result."""

    relation = analysis.derive_relation_property_source(
        case, witness_slot=relation_witness_slot
    )
    fresh_fs = analysis.derive_fresh_fs_relation_source(case)
    finite_profile = (
        analysis.derive_schnorr_special_soundness_profile(fresh_fs)
        if require_finite_profile
        else None
    )
    return AnalysisLanes(relation, fresh_fs, finite_profile)


def _future_supplement(case: object, role: object) -> object:
    if case.construction is None:
        raise IntegrationError("the joined FS witness needs a construction")
    plan = case.plan if role is oir.EndpointRole.PROVER else None
    # K3-D owns and checks this explicitly classified future-only fixture.
    return oir.future_owner_supplement(
        case.core,
        case.construction,
        case.interface,
        plan,
    )


def projection_request(
    case: object,
    role: object,
    *,
    include_supplement: bool = True,
    admit_supplement: bool = True,
    provenance: str = "k3e:joined-schnorr",
    source_label: str = "shared-total-uniform-case",
) -> object:
    plan = case.plan if role is oir.EndpointRole.PROVER else None
    supplement = _future_supplement(case, role) if include_supplement else None
    request = oir.ProjectionRequest(
        case.core,
        case.construction,
        k2.ChallengeInterpretation.FIAT_SHAMIR,
        case.interface,
        role,
        plan,
        supplement,
        provenance,
        source_label,
    )
    if not include_supplement or not admit_supplement:
        return request
    return _affirmative(
        oir.bind_future_owner_supplement(request),
        "future-owner supplement admission",
    )


def derive_endpoint_lane(request: object) -> EndpointLane:
    basis = _affirmative(oir.classify_support(request), "supported extraction basis")
    adapter = basis.adapter
    source = _affirmative(oir.extract_endpoint_source_view(basis), "source extraction")
    produced = _affirmative(
        oir.project_supported_endpoint(basis), "target construction"
    )
    if source.basis is not basis or source.adapter is not adapter:
        raise IntegrationError(
            "source extraction did not retain the exact classified authority"
        )
    admitted = _affirmative(oir.local_admit(produced), "local OIR admission")
    validation = _affirmative(
        oir.form_projection_validation_request(source, admitted),
        "projection proposition formation",
    )
    checked = _affirmative(oir.check_projection(validation), "projection checking")
    return EndpointLane(
        request,
        basis,
        adapter,
        source,
        produced,
        admitted,
        validation,
        checked,
    )


def shared_owner_anchors(case: object) -> SharedOwnerAnchors:
    """Derive the inert comparison vocabulary from the owner case alone."""

    construction = case.construction
    if construction is None:
        raise IntegrationError("the shared witness unexpectedly lacks a construction")
    return SharedOwnerAnchors(
        k2.core_id(case.core),
        k2.construction_id(case.core, construction),
        k3.protocol_id(case.core, None, k2.ChallengeInterpretation.FRESH),
        k3.protocol_id(
            case.core,
            construction,
            k2.ChallengeInterpretation.FIAT_SHAMIR,
        ),
        k3.interface_id(
            case.core,
            construction,
            k2.ChallengeInterpretation.FIAT_SHAMIR,
            case.interface,
        ),
        k3.plan_id(
            case.core,
            construction,
            k2.ChallengeInterpretation.FIAT_SHAMIR,
            case.plan,
        ),
        k3.relation_interface_id(case.relation_interfaces[0]),
        k3.protocol_relation_binding_id(case.protocol_binding),
        k3.plan_witness_binding_id(case.plan_binding),
    )


def require_analysis_anchor_correspondence(
    lanes: AnalysisLanes,
    anchors: SharedOwnerAnchors,
) -> None:
    """Check Analysis against inert IDs without exporting Analysis authority."""

    relation = lanes.relation
    fresh_fs = lanes.fresh_fs
    protocol_source = fresh_fs.protocol_source
    if (
        relation.protocol_source.core_id != anchors.core_id
        or relation.protocol_source.construction_id != anchors.construction_id
        or relation.protocol_source.fiat_shamir_protocol_id
        != anchors.fiat_shamir_protocol_id
        or relation.checked_protocol_binding.binding_id
        != anchors.protocol_binding_id
        or relation.checked_plan_binding.binding_id != anchors.plan_binding_id
        or protocol_source.core_id != anchors.core_id
        or protocol_source.construction_id != anchors.construction_id
        or protocol_source.fresh_protocol_id != anchors.fresh_protocol_id
        or protocol_source.fiat_shamir_protocol_id != anchors.fiat_shamir_protocol_id
        or fresh_fs.fresh_binding.binding_id
        != k3.protocol_relation_binding_id(fresh_fs.fresh_binding.binding)
        or fresh_fs.fiat_shamir_binding.binding_id != anchors.protocol_binding_id
        or fresh_fs.fiat_shamir_plan_binding.binding_id != anchors.plan_binding_id
    ):
        raise IntegrationError(
            "Analysis did not preserve the exact inert owner anchors"
        )


def require_endpoint_anchor_correspondence(
    case: object,
    verifier: EndpointLane,
    prover: EndpointLane,
    anchors: SharedOwnerAnchors,
) -> None:
    """Check each live K3-D lane independently against the same inert IDs."""

    for lane in (verifier, prover):
        request = lane.request
        expected_handles = (
            anchors.fiat_shamir_protocol_id.internal_reference().hex(),
            anchors.interface_id.internal_reference().hex(),
        )
        if request.role is oir.EndpointRole.PROVER:
            expected_handles += (anchors.plan_id.internal_reference().hex(),)
        if (
            request.core is not case.core
            or request.construction is not case.construction
            or request.interface is not case.interface
            or k2.core_id(request.core) != anchors.core_id
            or k2.construction_id(request.core, request.construction)
            != anchors.construction_id
            or k3.protocol_id(
                request.core,
                request.construction,
                request.interpretation,
            )
            != anchors.fiat_shamir_protocol_id
            or k3.interface_id(
                request.core,
                request.construction,
                request.interpretation,
                request.interface,
            )
            != anchors.interface_id
            or lane.source.request is not request
            or lane.adapter.request is not request
            or lane.validation.source_handles != expected_handles
        ):
            raise IntegrationError(
                "an endpoint lane detached from the exact inert owner anchors"
            )
    if prover.request.plan is not case.plan or verifier.request.plan is not None:
        raise IntegrationError("endpoint role selection chose the wrong Plan")
    if (
        k3.plan_id(
            prover.request.core,
            prover.request.construction,
            prover.request.interpretation,
            prover.request.plan,
        )
        != anchors.plan_id
    ):
        raise IntegrationError("the prover endpoint detached from the Plan anchor")


def build_integrated_witness(case: object | None = None) -> IntegratedWitness:
    selected = analysis.total_uniform_schnorr_case() if case is None else case
    lanes = derive_analysis_lanes(selected)
    verifier_request = projection_request(selected, oir.EndpointRole.VERIFIER)
    prover_request = projection_request(selected, oir.EndpointRole.PROVER)
    verifier = derive_endpoint_lane(verifier_request)
    prover = derive_endpoint_lane(prover_request)
    anchors = shared_owner_anchors(selected)
    require_analysis_anchor_correspondence(lanes, anchors)
    require_endpoint_anchor_correspondence(selected, verifier, prover, anchors)
    return IntegratedWitness(selected, lanes, verifier, prover, anchors)


def identity_snapshot(witness: IntegratedWitness) -> IdentitySnapshot:
    lanes = witness.analysis_lanes
    finite_profile_id = (
        None if lanes.finite_profile is None else lanes.finite_profile.profile_id
    )
    return IdentitySnapshot(
        witness.anchors,
        analysis.source_manifest_id(lanes.fresh_fs.fresh_manifest),
        analysis.source_manifest_id(lanes.fresh_fs.pair_manifest),
        finite_profile_id,
        witness.verifier.source.view_id,
        witness.verifier.admitted.oir_id,
        witness.verifier.validation.proposition.proposition_id,
        witness.verifier.checked.validation_request_id,
        witness.prover.source.view_id,
        witness.prover.admitted.oir_id,
        witness.prover.validation.proposition.proposition_id,
        witness.prover.checked.validation_request_id,
    )


def coherent_construction_domain(case: object, domain: bytes) -> object:
    construction = replace(case.construction, application_domain=domain)
    protocol_id = k3.protocol_id(
        case.core, construction, k2.ChallengeInterpretation.FIAT_SHAMIR
    )
    interface = replace(case.interface, protocol_id=protocol_id)
    plan = replace(case.plan, protocol_id=protocol_id)
    protocol_binding = replace(case.protocol_binding, protocol_id=protocol_id)
    surface = k3.derive_plan_witness_surface(
        case.core, construction, k2.ChallengeInterpretation.FIAT_SHAMIR, plan
    )
    plan_binding = replace(
        case.plan_binding,
        plan_witness_surface_id=k3.plan_witness_surface_id(surface),
    )
    return replace(
        case,
        construction=construction,
        interface=interface,
        plan=plan,
        protocol_binding=protocol_binding,
        plan_binding=plan_binding,
    )


def stale_challenge_domain(case: object, modulus: int = 7) -> object:
    schedule = tuple(
        replace(item, challenge_domain=k2.ChallengeDomain(modulus))
        if item.kind is k2.OccurrenceKind.CHALLENGE
        else item
        for item in case.core.schedule
    )
    return replace(case, core=replace(case.core, schedule=schedule))


def coherent_relation_witness_rename(
    case: object, name: str = "secret-renamed"
) -> object:
    relation_interface = replace(
        case.relation_interfaces[0],
        private_witness=(k3.RelationSlot(name, k3.NAT),),
    )
    relation_id = k3.relation_interface_id(relation_interface)
    binding = replace(
        case.protocol_binding,
        relation_interface_ids=(relation_id,),
        instances=tuple(
            replace(item, relation_interface_id=relation_id)
            for item in case.protocol_binding.instances
        ),
    )
    plan_binding = replace(
        case.plan_binding,
        relation_interface_id=relation_id,
        witness_edges=tuple(
            replace(item, slot=name) for item in case.plan_binding.witness_edges
        ),
    )
    return replace(
        case,
        relation_interfaces=(relation_interface,),
        protocol_binding=binding,
        plan_binding=plan_binding,
    )


def coherent_interface_external_rename(
    case: object,
    *,
    core_input: str = "statement",
    external_coordinate: str = "input.statement.renamed",
) -> object:
    assignments = tuple(
        replace(item, external_coordinate=external_coordinate)
        if item.core_input == core_input
        else item
        for item in case.interface.inputs
    )
    return replace(case, interface=replace(case.interface, inputs=assignments))


def with_unused_plan_export(case: object) -> object:
    export = k3.PlanExport("unused-copy", "response", k3.NAT)
    plan = replace(case.plan, exports=case.plan.exports + (export,))
    surface = k3.derive_plan_witness_surface(
        case.core,
        case.construction,
        k2.ChallengeInterpretation.FIAT_SHAMIR,
        plan,
    )
    plan_binding = replace(
        case.plan_binding,
        plan_witness_surface_id=k3.plan_witness_surface_id(surface),
    )
    return replace(case, plan=plan, plan_binding=plan_binding)


def downstream_oir_mismatch(lane: EndpointLane) -> object:
    graph = lane.produced.semantic_graph
    abi = graph.role_abi_graph
    first = abi.slots[0]
    changed_abi = replace(
        abi,
        slots=(replace(first, external_key=f"{first.external_key}.downstream"),)
        + abi.slots[1:],
    )
    changed = oir.remint(
        replace(
            lane.produced, semantic_graph=replace(graph, role_abi_graph=changed_abi)
        )
    )
    admitted = _affirmative(oir.local_admit(changed), "mutated local OIR admission")
    validation = _affirmative(
        oir.form_projection_validation_request(lane.source, admitted),
        "mutated projection proposition formation",
    )
    return oir.check_projection(validation)
