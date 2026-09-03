#!/usr/bin/env python3
"""Untrusted generator for the finite Schnorr ArkLib interpretation.

The generator has no authority. It reads the typed six-view projection of the
admitted finite Schnorr subject, the exact Check and guard preimages, and the
relation and Plan candidate bodies. It emits one Lean module and one
source-bound correspondence certificate. The independent checker does not
import this program.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
from types import ModuleType
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
GENERATED = HERE / "generated"
LEAN_OUT = GENERATED / "SchnorrArkLib.lean"
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

FORMAT = "zkc.formal-provider-interpretation.arklib.certificate.v0"
PROVIDER_REVISION = "fad5cbf808774838924dc8273715724c6a6caa1f"
PROVIDER_TREE = "e38383088598a1305c15447c53db309ccd6b35ee"
VCVIO_REVISION = "cbd4144b51d92da00dd50f05e068b2348fa6e529"
VCVIO_TREE = "28c268057ed58427973e5bbf4854d472a7088954"
TOOLCHAIN = "leanprover/lean4:v4.31.0"
PROVIDER_DEFAULT = Path("/home/wonjae/code/ArkLib")
PROVIDER_SOURCE_FILES = (
    "ArkLib/OracleReduction/Basic.lean",
    "ArkLib/OracleReduction/Execution.lean",
    "ArkLib/OracleReduction/ProtocolSpec/Basic.lean",
    "lake-manifest.json",
    "lean-toolchain",
)


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


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _file_pins(paths: tuple[Path, ...]) -> dict[str, str]:
    return {path.relative_to(ROOT).as_posix(): _sha256(path) for path in paths}


def _require(condition: bool, detail: str) -> None:
    if not condition:
        raise GeneratorError(detail)


def _external_git_env() -> dict[str, str]:
    environment = dict(os.environ)
    for name in (
        "GIT_OBJECT_DIRECTORY",
        "GIT_ALTERNATE_OBJECT_DIRECTORIES",
        "GIT_INDEX_FILE",
        "GIT_WORK_TREE",
    ):
        environment.pop(name, None)
    return environment


LEAN_TEXT = r'''/-
Generated from the admitted finite Schnorr formal source by an untrusted
generator. The module is an interpretation artifact, not semantic authority.

Provider: ArkLib fad5cbf808774838924dc8273715724c6a6caa1f
Toolchain: leanprover/lean4:v4.31.0
-/
import ArkLib.OracleReduction.Execution
import Mathlib.Algebra.Field.ZMod

open OracleComp OracleSpec ProtocolSpec

namespace ZkcArkLibInterpretation

abbrev Z3 := ZMod 3

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- The three-step public-coin schedule selected by the formal source. -/
def protocolSpec : ProtocolSpec 3 :=
  ⟨!v[.P_to_V, .V_to_P, .P_to_V], fun _ => Z3⟩

/-- A uniform draw transported from `Fin 3` to the challenge carrier. -/
def freshChallenge : ProbComp Z3 :=
  (ZMod.finEquiv 3) <$> $[0..2]

/-- An implementation of ArkLib's challenge oracle that samples the selected
finite carrier uniformly. The Fresh independence law remains a premise. -/
def freshChallengeQueryImpl : QueryImpl [protocolSpec.Challenge]ₒ ProbComp :=
  fun _ => freshChallenge

structure Memory where
  witness : Z3
  nonce : Z3
  challenge : Z3

/-- The selected Plan's commitment recipe after fixing its nonce sample. -/
def candidateCommit (nonce : Z3) : Z3 := nonce

/-- The selected Plan's response recipe. -/
def candidateRespond (witness nonce challenge : Z3) : Z3 :=
  nonce + challenge * witness

def roundZero (transcript : FullTranscript protocolSpec) : Z3 := by
  simpa [protocolSpec] using transcript (0 : Fin 3)

def roundOne (transcript : FullTranscript protocolSpec) : Z3 := by
  simpa [protocolSpec] using transcript (1 : Fin 3)

def roundTwo (transcript : FullTranscript protocolSpec) : Z3 := by
  simpa [protocolSpec] using transcript (2 : Fin 3)

/-- An ArkLib prover whose two sending rounds implement the selected recipes. -/
def prover (nonce : Z3) : Prover []ₒ Z3 Z3 Unit Unit protocolSpec where
  PrvState := fun _ => Memory
  input := fun (_, witness) => ⟨witness, nonce, 0⟩
  sendMessage
    | ⟨0, _⟩ => fun state => pure (candidateCommit state.nonce, state)
    | ⟨1, h⟩ => nomatch h
    | ⟨2, _⟩ => fun state =>
        pure (candidateRespond state.witness state.nonce state.challenge, state)
  receiveChallenge
    | ⟨0, h⟩ => nomatch h
    | ⟨1, _⟩ => fun state => pure fun challenge => { state with challenge }
    | ⟨2, h⟩ => nomatch h
  output := fun _ => pure ((), ())

/-- The portable Check represented as ArkLib verifier rejection or unit output. -/
def verifier : Verifier []ₒ Z3 Unit protocolSpec where
  verify := fun statement transcript => do
    guard (roundTwo transcript = roundZero transcript + roundOne transcript * statement)
    return ()

/-- The generated provider reduction. -/
def reduction (nonce : Z3) : Reduction []ₒ Z3 Z3 Unit Unit protocolSpec where
  prover := prover nonce
  verifier := verifier

/-- Kernel-checked equality for the commitment field of the generated prover. -/
theorem commitRoundMatchesCandidate (state : Memory) :
    (prover state.nonce).sendMessage ⟨0, rfl⟩ state =
      pure (candidateCommit state.nonce, state) := rfl

/-- Kernel-checked equality for the response field of the generated prover. -/
theorem responseRoundMatchesCandidate (state : Memory) :
    (prover state.nonce).sendMessage ⟨2, rfl⟩ state =
      pure (candidateRespond state.witness state.nonce state.challenge, state) := rfl

def challengeValues (challenge : Z3) (_ : protocolSpec.ChallengeIdx) : Z3 := challenge

def challengeImpl (challenge : Z3) :
    QueryImpl ([]ₒ + [protocolSpec.Challenge]ₒ) Id :=
  fun
    | Sum.inl i => nomatch i
    | Sum.inr query => challengeValues challenge query.1

def emptyImpl : QueryImpl []ₒ Id := fun i => nomatch i

def transcriptOf (commitment challenge response : Z3) : FullTranscript protocolSpec :=
  fun i => Fin.cases commitment (Fin.cases challenge (Fin.cases response Fin.elim0)) i

/-- Execute the actual ArkLib verifier against one complete transcript. -/
def executeCheck (statement commitment challenge response : Z3) : Option Unit :=
  evalWithAnswerFn emptyImpl
    (verifier.run statement (transcriptOf commitment challenge response)).run

/-- Execute all three rounds of the actual ArkLib prover with a fixed challenge. -/
def executeProver (statement witness nonce challenge : Z3) :
    FullTranscript protocolSpec × Unit × Unit :=
  evalWithAnswerFn (challengeImpl challenge)
    ((prover nonce).run statement witness)

/-- Execute the actual ArkLib reduction verdict with a fixed challenge. -/
def executeVerdict (statement witness nonce challenge : Z3) : Option Unit :=
  evalWithAnswerFn (challengeImpl challenge)
    ((reduction nonce).verdict statement witness).run

def fromNat (value : Nat) : Z3 := value

def bit (value : Bool) : Nat := if value then 1 else 0

def providerCheck (statement commitment challenge response : Nat) : Bool :=
  (executeCheck (fromNat statement) (fromNat commitment)
    (fromNat challenge) (fromNat response)).isSome

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
          let proverResult := executeProver (fromNat statement) (fromNat witness)
            (fromNat nonce) (fromNat challenge)
          let transcript := proverResult.1
          let verdict := executeVerdict (fromNat statement) (fromNat witness)
            (fromNat nonce) (fromNat challenge)
          let accepted := verdict.isSome
          let lastOccurrence := if accepted then 4 else 5
          IO.println s!"RUN\t{statement}\t{witness}\t{nonce}\t{challenge}\t{(roundZero transcript).val}\t{(roundTwo transcript).val}\t{bit accepted}\t{lastOccurrence}"

#eval emitCheckRows
#eval emitRunRows

#print axioms ZkcArkLibInterpretation.protocolSpec
#print axioms ZkcArkLibInterpretation.freshChallenge
#print axioms ZkcArkLibInterpretation.freshChallengeQueryImpl
#print axioms ZkcArkLibInterpretation.reduction
#print axioms ZkcArkLibInterpretation.commitRoundMatchesCandidate
#print axioms ZkcArkLibInterpretation.responseRoundMatchesCandidate
#print axioms ZkcArkLibInterpretation.executeCheck
#print axioms ZkcArkLibInterpretation.executeProver
#print axioms ZkcArkLibInterpretation.executeVerdict

end ZkcArkLibInterpretation
'''


def _algorithm_inputs(source_views: ModuleType) -> dict[str, Any]:
    fixture = source_views.owner.make_fixture()
    k1 = source_views.owner.k1
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
    source_core = _load("_arklib_generator_source_core", SCHNORR_CORE_MODEL)
    relation_plan = _load("_arklib_generator_relation_plan", RELATION_PLAN_MODEL)
    artifacts = relation_plan._build_artifacts(source_core, source_core.make_fixture())
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
    source_views = _load("_arklib_generator_source_views", SCHNORR_VIEW_MODEL)
    core_handle, protocol_handle = source_views.admitted_handles()
    candidate = source_views.build_candidate(core_handle, protocol_handle)
    views = candidate["values"]
    _require(
        tuple(views)
        == (
            "PublicBindingView",
            "StrategyDecisionView",
            "PublicCoinView",
            "EffectView",
            "ClaimReductionView",
            "ExecutionView",
        ),
        "six-view order drifted",
    )
    effect_cases = [row[3]["case"] for row in views["EffectView"][1]]
    decisions = [int.from_bytes(bytes.fromhex(row[0]["body"])[-1:], "big") for row in views["StrategyDecisionView"][1]]
    _require(effect_cases == [0, 2, 0, 3, 5, 5], "Schnorr schedule drifted")
    _require(decisions == [0, 2], "Schnorr prover decisions drifted")
    summary = {
        "source_digest": candidate["source_digest"],
        "body_sha256": {name: _digest(body) for name, body in views.items()},
        "active_leaf_counts": {name: len(candidate["requested_manifests"][name]) for name in views},
        "core_id": core_handle.core_id.carrier(),
        "protocol_id": protocol_handle.protocol_id.carrier(),
    }
    fixture = source_views.owner.make_fixture()
    carrier_inputs = {
        "core_profiled_body_sha256": hashlib.sha256(
            source_views.owner.core_profiled_body(fixture.core_candidate.core, fixture.environment.profile_id)
        ).hexdigest(),
        "protocol_profiled_body_sha256": hashlib.sha256(
            source_views.owner.protocol_profiled_body(fixture.protocol_candidate.core_id, fixture.environment.profile_id)
        ).hexdigest(),
        "view_schema_source_sha256": _sha256(SCHNORR_VIEW_SCHEMA),
        "active_view_manifest_sha256": {
            name: _digest(candidate["requested_manifests"][name]) for name in views
        },
    }
    return summary, _algorithm_inputs(source_views), carrier_inputs


def _provider_inputs() -> dict[str, Any]:
    provider = Path(os.environ.get("ZKC_ARKLIB_ROOT", str(PROVIDER_DEFAULT))).resolve()
    _require(provider.is_dir(), f"pinned provider tree is absent: {provider}")
    revision = subprocess.run(
        ["git", "rev-parse", "HEAD", "HEAD^{tree}"],
        cwd=provider,
        env=_external_git_env(),
        check=False,
        capture_output=True,
        text=True,
    )
    values = revision.stdout.split()
    _require(
        revision.returncode == 0 and values == [PROVIDER_REVISION, PROVIDER_TREE],
        "provider revision or tree differs from the pin",
    )
    dependency = provider / ".lake/packages/VCVio"
    dependency_revision = subprocess.run(
        ["git", "rev-parse", "HEAD", "HEAD^{tree}"],
        cwd=dependency,
        env=_external_git_env(),
        check=False,
        capture_output=True,
        text=True,
    )
    dependency_values = dependency_revision.stdout.split()
    _require(
        dependency_revision.returncode == 0
        and dependency_values == [VCVIO_REVISION, VCVIO_TREE],
        "provider dependency revision or tree differs from the pin",
    )
    return {
        "git_tree": PROVIDER_TREE,
        "dependency_revision": VCVIO_REVISION,
        "dependency_tree": VCVIO_TREE,
        "source_sha256": {name: _sha256(provider / name) for name in PROVIDER_SOURCE_FILES},
    }


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
        {"source": "PublicBindingView.public_inputs[0]", "provider": "StmtIn", "carrier": "ZMod 3"},
        {"source": "RelationInterface.private_witness[0]", "provider": "WitIn", "carrier": "ZMod 3"},
        {"source": "EffectView.occurrences[0].outputs[0]", "provider": "round 0", "carrier": "ZMod 3"},
        {"source": "ProverPlan.persistent_state[0]", "provider": "Memory.nonce", "carrier": "ZMod 3"},
        {"source": "PublicCoinView.challenges[0].value_type", "provider": "round 1", "carrier": "ZMod 3"},
        {"source": "EffectView.occurrences[2].outputs[0]", "provider": "round 2", "carrier": "ZMod 3"},
        {"source": "EffectView.occurrences[3].outputs[0]", "provider": "verifier predicate", "carrier": "Bool"},
        {"source": "ExecutionView.terminals", "provider": "Reduction.verdict", "carrier": "Option Unit"},
    ]
    lane_map = [
        {"lane": "Accepted", "provider_lane_image": {"case": "Image", "value": "some ()"}},
        {"lane": "Rejected", "provider_lane_image": {"case": "Image", "value": "none"}},
        {"lane": "Aborted", "provider_lane_image": {"case": "Unmodelled"}},
        {"lane": "StrategyStopped", "provider_lane_image": {"case": "Unmodelled"}},
        {"lane": "OperationalNoncompletion", "provider_lane_image": {"case": "Unmodelled"}},
    ]
    return {
        "format": FORMAT,
        "authority": "none; untrusted generator output",
        "question": "Does this generated ArkLib Reduction operationally correspond to the admitted finite Schnorr Fresh Protocol under all five contract clauses?",
        "subject": views,
        "provider": {
            "name": "ArkLib",
            "revision": PROVIDER_REVISION,
            "toolchain": TOOLCHAIN,
            "module": "ArkLib.OracleReduction.Execution",
            "definition": "Reduction.verdict",
            "closed_carrier": {
                "schema": "Option Unit",
                "canonical_values": ["none", "some ()"],
            },
            "modelled_lanes": ["Accepted", "Rejected"],
            "prover_run_carrier": "OracleComp (FullTranscript x Unit x Unit)",
            "verifier_run_carrier": "OptionT (OracleComp) Unit",
            **_provider_inputs(),
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


def write_generated() -> None:
    GENERATED.mkdir(exist_ok=True)
    LEAN_OUT.write_text(LEAN_TEXT, encoding="utf-8")
    CERTIFICATE_OUT.write_text(certificate_text(), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", action="store_true", help="print generated Lean")
    parser.add_argument("--certificate", action="store_true", help="print certificate JSON")
    parser.add_argument("--check", action="store_true", help="compare generated artifacts")
    parser.add_argument("--write", action="store_true", help="write generated artifacts")
    args = parser.parse_args()
    if sum((args.lean, args.certificate, args.check, args.write)) != 1:
        parser.error("select exactly one output mode")
    if args.check:
        check_generated()
        print("generated ArkLib module and certificate match their inputs")
    elif args.write:
        write_generated()
        print("generated ArkLib module and certificate written")
    elif args.lean:
        print(LEAN_TEXT, end="")
    else:
        print(certificate_text(), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
