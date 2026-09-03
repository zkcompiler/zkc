#!/usr/bin/env python3
"""Untrusted generator for the finite Schnorr VCVio interpretation.

The generator deliberately has no authority.  It reads the typed six-view
projection of the admitted finite Schnorr subject, the exact Check and guard
algorithm preimages, and the relation/Plan candidate bodies.  It emits one
Lean module and one correspondence certificate.  ``checker.py`` does not
import this module.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from types import ModuleType
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
GENERATED = HERE / "generated"
LEAN_OUT = GENERATED / "SchnorrProvider.lean"
CERTIFICATE_OUT = GENERATED / "certificate.json"

SCHNORR_VIEW_MODEL = ROOT / "evaluation/formal-source-view-bodies-f0v2b1/model.py"
SCHNORR_CORE_MODEL = ROOT / "evaluation/formal-source-target-core-f1r1b/reference_model.py"
RELATION_PLAN_MODEL = ROOT / "evaluation/formal-schnorr-relations-plan-f2p1/model.py"
SCHNORR_VIEW_SCHEMA = (
    ROOT / "evaluation/formal-source-view-bodies-f0v2b1/normalized-schema.json"
)
TERM_VECTORS = ROOT / "evaluation/formal-kernel-mechanization-m0/vectors/m2-term-calculus.json"
TERMINAL_MECHANIZATION = (
    ROOT / "evaluation/formal-kernel-mechanization-m0/lean/M0/Terminal.lean"
)
TERM_PROBE = HERE / "TermEvaluatorProbe.lean"
ENTRY_CONTRACT = (
    ROOT
    / "docs-next/notes/semantic-revalidation-and-redesign/formal-assurance-research"
    / "f2o2-provider-interpretation-entry-contract.md"
)
DECISION_PACKET = (
    ROOT
    / "docs-next/notes/semantic-revalidation-and-redesign/formal-assurance-research"
    / "f2o2-provider-carrier-decision-2026-09-03.md"
)
OWNER_PAGES = (
    ROOT / "docs-next/pir/interactive-core.md",
    ROOT / "docs-next/analysis/analysis-model.md",
    ROOT / "docs-next/analysis/cryptographic-properties.md",
)
PROFILE_MANIFESTS = (
    ROOT / "docs-next/foundation/semantic-profile-manifests.json",
    ROOT / "docs-next/pir/profiles/interaction.json",
    ROOT / "docs-next/analysis/profiles/kernel.json",
    ROOT / "docs-next/analysis/profiles/cryptographic-property.json",
)
PACKAGE_INPUTS = (
    SCHNORR_VIEW_SCHEMA,
    TERM_VECTORS,
    TERMINAL_MECHANIZATION,
    TERM_PROBE,
)

FORMAT = "zkc.formal-provider-interpretation.certificate.v0"
PROVIDER_REVISION = "de0a3108140e3e04a7ebf0075aa110b459ee6e8a"
TOOLCHAIN = "leanprover/lean4:v4.33.1"


class GeneratorError(RuntimeError):
    """The named inputs do not determine the frozen artifact."""


def _load(name: str, path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:  # pragma: no cover - host failure
        raise ImportError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _canonical(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")


def _digest(value: Any) -> str:
    return hashlib.sha256(_canonical(value)).hexdigest()


def _file_pins(paths: tuple[Path, ...]) -> dict[str, str]:
    return {
        path.relative_to(ROOT).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in paths
    }


def _require(condition: bool, detail: str) -> None:
    if not condition:
        raise GeneratorError(detail)


LEAN_TEXT = r'''/-
Generated from the admitted finite Schnorr formal source by an untrusted
generator.  The module is an interpretation artifact, not semantic authority.

Provider: VCVio de0a3108140e3e04a7ebf0075aa110b459ee6e8a
Toolchain: leanprover/lean4:v4.33.1
-/
import Examples.Schnorr.SigmaProtocol
import Mathlib.Algebra.Field.ZMod

open OracleComp SigmaProtocol

namespace ZkcProviderInterpretation

abbrev Z3 : Type := ZMod 3

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

def generator : Z3 := 1

def relation (statement witness : Z3) : Bool :=
  decide (witness • generator = statement)

/-- The VCVio sigma protocol selected by the source relation and Plan. -/
def sigmaProtocol : SigmaProtocol Z3 Z3 Z3 Z3 Z3 Z3 relation :=
  Schnorr.sigma Z3 Z3 generator

/-- The interaction-only provider carrier used by the Fresh interpretation. -/
def freshProtocol : ChallengeVerifyProtocol Z3 Z3 Z3 Z3 Z3 Z3 relation :=
  sigmaProtocol.toChallengeVerifyProtocol

/-- The source public-coin declaration interpreted under its named premise. -/
def freshChallenge : ProbComp Z3 := $ᵗ Z3

/-- The source Plan's commitment recipe after fixing its nonce sample. -/
def candidateCommit (nonce : Z3) : Z3 := nonce

/-- The source Plan's response recipe. -/
def candidateRespond (witness nonce challenge : Z3) : Z3 :=
  nonce + challenge * witness

/-- The provider's randomized commit field is exactly the candidate recipe
after naming its sampled nonce. -/
theorem commitMatchesCandidate (statement witness : Z3) :
    freshProtocol.commit statement witness =
      (do
        let nonce ← $ᵗ Z3
        return (candidateCommit nonce, nonce)) := by
  simp [freshProtocol, sigmaProtocol, Schnorr.sigma, generator, candidateCommit]

/-- The provider's response field is exactly the candidate recipe. -/
theorem respondMatchesCandidate
    (statement witness privateState challenge : Z3) :
    freshProtocol.respond statement witness privateState challenge =
      pure (candidateRespond witness privateState challenge) := by
  rfl

/-- One generated Fresh execution.  Sampling semantics remain a named premise. -/
def interaction (statement witness : Z3) : ProbComp Bool := do
  let (commitment, privateState) ← freshProtocol.commit statement witness
  let challenge ← freshChallenge
  let response ← freshProtocol.respond statement witness privateState challenge
  return freshProtocol.verify statement commitment challenge response

def fromNat (value : Nat) : Z3 := value

def bit (value : Bool) : Nat := if value then 1 else 0

def providerCheck (statement commitment challenge response : Nat) : Bool :=
  freshProtocol.verify (fromNat statement) (fromNat commitment)
    (fromNat challenge) (fromNat response)

def emitCheckRows : IO Unit := do
  for statement in List.range 3 do
    for commitment in List.range 3 do
      for challenge in List.range 3 do
        for response in List.range 3 do
          IO.println s!"CHECK\t{statement}\t{commitment}\t{challenge}\t{response}\t{bit (providerCheck statement commitment challenge response)}"

def emitRunRows : IO Unit := do
  for statement in List.range 3 do
    for witness in List.range 3 do
      for nonce in List.range 3 do
        for challenge in List.range 3 do
          let commitment := candidateCommit (fromNat nonce)
          let response := candidateRespond (fromNat witness) commitment (fromNat challenge)
          let accepted := freshProtocol.verify (fromNat statement) commitment
            (fromNat challenge) response
          let lastOccurrence := if accepted then 4 else 5
          IO.println s!"RUN\t{statement}\t{witness}\t{nonce}\t{challenge}\t{commitment.val}\t{response.val}\t{bit accepted}\t{lastOccurrence}"

#eval emitCheckRows
#eval emitRunRows

#print axioms ZkcProviderInterpretation.sigmaProtocol
#print axioms ZkcProviderInterpretation.freshProtocol
#print axioms ZkcProviderInterpretation.interaction
#print axioms ZkcProviderInterpretation.commitMatchesCandidate
#print axioms ZkcProviderInterpretation.respondMatchesCandidate

end ZkcProviderInterpretation
'''


def _algorithm_inputs(b1: ModuleType) -> dict[str, Any]:
    fixture = b1.owner.make_fixture()
    k1 = b1.owner.k1
    check = k1.algorithm_preimage(fixture.schnorr_algorithm)
    guard = k1.algorithm_preimage(fixture.guard_algorithm)
    return {
        "check": {
            "identity": fixture.schnorr_algorithm.identity.carrier(),
            "preimage_sha256": hashlib.sha256(check).hexdigest(),
            "preimage_length": len(check),
        },
        "guard": {
            "identity": fixture.guard_algorithm.identity.carrier(),
            "preimage_sha256": hashlib.sha256(guard).hexdigest(),
            "preimage_length": len(guard),
        },
    }


def _candidate_inputs() -> dict[str, Any]:
    source_core = _load("_provider_generator_source_core", SCHNORR_CORE_MODEL)
    relation_plan = _load(
        "_provider_generator_relation_plan", RELATION_PLAN_MODEL
    )
    artifacts = relation_plan._build_artifacts(
        source_core, source_core.make_fixture()
    )
    premises = relation_plan._premise_table(artifacts)
    bodies = relation_plan._body_catalog(artifacts)
    _require(artifacts.definition.payload["scalar_modulus"] == 3, "candidate modulus drifted")
    _require(artifacts.definition.payload["generator"] == 1, "candidate generator drifted")
    _require(
        premises["honest-commit"]["meaning"] == "A := r"
        and premises["honest-respond"]["meaning"] == "z := r + c*x mod 3",
        "candidate Plan formulas drifted",
    )
    plan_body = bodies["prover_plan"]
    recipes = {row["decision"]: row["recipe"] for row in plan_body["decision_recipes"]}
    return {
        "algebra": artifacts.definition.payload,
        "protocol_id": artifacts.protocol_id,
        "relation": premises["relation-predicate"]["meaning"],
        "witness": premises["witness-type"]["meaning"],
        "private_state": premises["prover-private-state"]["meaning"],
        "plan": {
            "decision_order": [row["decision"] for row in plan_body["decision_recipes"]],
            "commit": {
                "formula": premises["honest-commit"]["meaning"],
                "input_kinds": [item["case"] for item in recipes[0]["nodes"][0]["inputs"]],
                "state_binding": recipes[0]["state_after"][0]["binding"]["case"],
            },
            "respond": {
                "formula": premises["honest-respond"]["meaning"],
                "input_kinds": [item["case"] for item in recipes[2]["nodes"][0]["inputs"]],
                "challenge_occurrence": recipes[2]["nodes"][0]["inputs"][1]["coordinate"]["occurrence"],
                "state_binding": recipes[2]["state_after"][0]["binding"]["case"],
            },
        },
        "published_candidate_bodies_sha256": _digest(bodies),
    }


def _view_inputs() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    source_views = _load("_provider_generator_source_views", SCHNORR_VIEW_MODEL)
    core_handle, protocol_handle = source_views.admitted_handles()
    candidate = source_views.build_candidate(core_handle, protocol_handle)
    views = candidate["values"]
    _require(tuple(views) == (
        "PublicBindingView",
        "StrategyDecisionView",
        "PublicCoinView",
        "EffectView",
        "ClaimReductionView",
        "ExecutionView",
    ), "six-view order drifted")
    effect_cases = [row[3]["case"] for row in views["EffectView"][1]]
    decisions = [int.from_bytes(bytes.fromhex(row[0]["body"])[-1:], "big")
                 for row in views["StrategyDecisionView"][1]]
    _require(effect_cases == [0, 2, 0, 3, 5, 5], "Schnorr schedule drifted")
    _require(decisions == [0, 2], "Schnorr Prover decisions drifted")
    summary = {
        "source_digest": candidate["source_digest"],
        "body_sha256": {name: _digest(body) for name, body in views.items()},
        "active_leaf_counts": {
            name: len(candidate["requested_manifests"][name]) for name in views
        },
        "core_id": core_handle.core_id.carrier(),
        "protocol_id": protocol_handle.protocol_id.carrier(),
    }
    fixture = source_views.owner.make_fixture()
    carrier_inputs = {
        "core_profiled_body_sha256": hashlib.sha256(
            source_views.owner.core_profiled_body(
                fixture.core_candidate.core, fixture.environment.profile_id
            )
        ).hexdigest(),
        "protocol_profiled_body_sha256": hashlib.sha256(
            source_views.owner.protocol_profiled_body(
                fixture.protocol_candidate.core_id, fixture.environment.profile_id
            )
        ).hexdigest(),
        "view_schema_source_sha256": hashlib.sha256(
            SCHNORR_VIEW_SCHEMA.read_bytes()
        ).hexdigest(),
        "active_view_manifest_sha256": {
            name: _digest(candidate["requested_manifests"][name]) for name in views
        },
    }
    return summary, _algorithm_inputs(source_views), carrier_inputs


def build_certificate() -> dict[str, Any]:
    views, algorithms, carriers = _view_inputs()
    candidate = _candidate_inputs()
    occurrence_to_step = [
        {"occurrence": 0, "effect": "ProverMessage", "step": "commit", "actor": "Prover"},
        {"occurrence": 1, "effect": "Challenge", "step": "challenge", "actor": "Verifier"},
        {"occurrence": 2, "effect": "ProverMessage", "step": "respond", "actor": "Prover"},
        {"occurrence": 3, "effect": "Check", "step": "verify", "actor": "Verifier"},
        {"occurrence": 4, "effect": "Terminal", "step": "accept", "actor": "Verifier"},
        {"occurrence": 5, "effect": "Terminal", "step": "reject", "actor": "Verifier"},
    ]
    type_map = [
        {"source": "PublicBindingView.public_inputs[0]", "provider": "Stmt", "carrier": "ZMod 3"},
        {"source": "RelationInterface.private_witness[0]", "provider": "Wit", "carrier": "ZMod 3"},
        {"source": "EffectView.occurrences[0].outputs[0]", "provider": "Commit", "carrier": "ZMod 3"},
        {"source": "ProverPlan.persistent_state[0]", "provider": "PrvState", "carrier": "ZMod 3"},
        {"source": "PublicCoinView.challenges[0].value_type", "provider": "Chal", "carrier": "ZMod 3"},
        {"source": "EffectView.occurrences[2].outputs[0]", "provider": "Resp", "carrier": "ZMod 3"},
        {"source": "EffectView.occurrences[3].outputs[0]", "provider": "verify result", "carrier": "Bool"},
    ]
    lane_map = [
        {"lane": "Accepted", "provider_lane_image": {"case": "Image", "value": True}},
        {"lane": "Rejected", "provider_lane_image": {"case": "Image", "value": False}},
        {"lane": "Aborted", "provider_lane_image": {"case": "Unmodelled"}},
        {"lane": "StrategyStopped", "provider_lane_image": {"case": "Unmodelled"}},
        {
            "lane": "OperationalNoncompletion",
            "provider_lane_image": {"case": "Unmodelled"},
        },
    ]
    return {
        "format": FORMAT,
        "authority": "none; untrusted generator output",
        "question": "Does this generated VCVio artifact operationally correspond to the admitted finite Schnorr Fresh Protocol under all five contract clauses?",
        "subject": views,
        "provider": {
            "name": "VCVio",
            "revision": PROVIDER_REVISION,
            "toolchain": TOOLCHAIN,
            "module": "Examples.Schnorr.SigmaProtocol",
            "definition": "Schnorr.sigma",
            "closed_carrier": "Bool",
            "modelled_lanes": ["Accepted", "Rejected"],
        },
        "inputs": {
            "owner_pages": _file_pins(OWNER_PAGES),
            "profile_manifests": _file_pins(PROFILE_MANIFESTS),
            "package_inputs": _file_pins(PACKAGE_INPUTS),
            "carriers": carriers,
            "algorithms": algorithms,
            "candidates": candidate,
        },
        "occurrence_to_step": occurrence_to_step,
        "type_map": type_map,
        "lane_map": lane_map,
        "lean_sha256": hashlib.sha256(LEAN_TEXT.encode("utf-8")).hexdigest(),
    }


def certificate_text() -> str:
    return json.dumps(build_certificate(), indent=2, sort_keys=True) + "\n"


def check_generated() -> None:
    _require(LEAN_OUT.read_text(encoding="utf-8") == LEAN_TEXT, "generated Lean drifted")
    _require(
        CERTIFICATE_OUT.read_text(encoding="utf-8") == certificate_text(),
        "generated certificate drifted",
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", action="store_true", help="print generated Lean")
    parser.add_argument("--certificate", action="store_true", help="print certificate JSON")
    parser.add_argument("--check", action="store_true", help="compare committed artifacts")
    args = parser.parse_args()
    if sum((args.lean, args.certificate, args.check)) != 1:
        parser.error("select exactly one output mode")
    if args.check:
        check_generated()
        print("generated provider module and certificate match their inputs")
    elif args.lean:
        print(LEAN_TEXT, end="")
    else:
        print(certificate_text(), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
