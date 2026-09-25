import ZkcArkLib.Sumcheck.Scalar
import Zkc.Protocols.AlgebraicRounds.BlockTemplates
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

namespace ZkcArkLib.Sumcheck.Scalar.Stopping
open Zkc.Protocols.Sumcheck.ProductFamily Zkc.Protocols.AlgebraicRounds.Scalar Zkc.Protocols.AlgebraicRounds.BlockEvaluation Zkc.Protocols.AlgebraicRounds.Early Zkc.Protocols.AlgebraicRounds.BlockEvaluation.Templates OracleSpec OracleComp
theorem family_replacement {F ι WI WO : Type} [CommRing F] [DecidableEq F]
    (oSpec : OracleSpec ι) (m : Nat)
    (prover : Prover oSpec F WI Unit WO (protocol F m)) (s : F) (w : WI) :
    (Reduction.mk prover (verifier oSpec m (moduleValue target 7))).run s w =
    (Reduction.mk prover (verifier oSpec m value)).run s w :=
  checked_reduction oSpec source target 8 7 admitted m prover s w

-- This is an actual ArkLib prover and an actual VCV-io stateful interpreter.
-- Deterministic counting discriminates effects; it is not the sampling law
-- used in ArkLib's soundness definition or the native toy Fiat-Shamir provider.
def zeroProver (m : Nat) : Prover []ₒ Int Unit Unit Unit (protocol Int m) where
  PrvState _ := Unit
  input _ := ()
  sendMessage _ _ := pure ((0 : Int), ())
  receiveChallenge _ _ := pure (fun _ => ())
  output _ := pure ((), ())

def counting (m : Nat) : QueryImpl ([]ₒ + [(protocol Int m).Challenge]ₒ) (StateM Nat) :=
  fun i => match i with
    | .inl impossible => nomatch impossible
    | .inr _ => fun q => ((q : Int), q+1)

def arkFailure : Option Unit × Nat :=
  (simulateQ (counting 0)
    ((Reduction.mk (zeroProver 0) (verifier []ₒ 0 value)).verdict 1 ()).run).run 0

theorem actual_arklib_failure_consumes_challenge : arkFailure = (none, 1) := by decide

theorem actual_early_arklib_state_difference :
    (early value badSend ignoreChallenge counterDraw 1 1 () 0).oracleState ≠ arkFailure.2 := by
  rw [actual_arklib_failure_consumes_challenge]
  decide

def earlyObservation : Option Unit × Nat :=
  let out := early value badSend ignoreChallenge counterDraw 1 1 () 0
  (out.result.map (fun _ => ()), out.oracleState)

theorem early_observation : earlyObservation = (none, 0) := by decide

theorem failure_verdicts_agree : earlyObservation.1 = arkFailure.1 := by
  rw [early_observation, actual_arklib_failure_consumes_challenge]

-- The resource assertion cannot be reconstructed from the shared verdict,
-- even on this two-execution set. The abstraction has lost needed information.
theorem resource_property_does_not_factor_through_verdict :
    ¬ ∃ p : Option Unit → Prop, ∀ o ∈ [earlyObservation, arkFailure], p o.1 ↔ o.2 = 0 := by
  rintro ⟨p, hp⟩
  have hzero := hp earlyObservation (by simp)
  have hone := hp arkFailure (by simp)
  rw [early_observation] at hzero
  rw [actual_arklib_failure_consumes_challenge] at hone
  have hbad : (1 : Nat) = 0 := hone.mp (hzero.mpr rfl)
  omega

-- An exhausted interpreter is an outer failure, distinct from an inner
-- verifier rejection. This does not change ArkLib's default security sampler.
def exhausted (m : Nat) : QueryImpl ([]ₒ + [(protocol Int m).Challenge]ₒ) Option :=
  fun i => match i with
    | .inl impossible => nomatch impossible
    | .inr _ => none

def arkExhaustion : Option (Option Unit) :=
  simulateQ (exhausted 0)
    ((Reduction.mk (zeroProver 0) (verifier []ₒ 0 value)).verdict 1 ()).run

theorem actual_arklib_exhaustion : arkExhaustion = none := by decide

theorem exhaustion_is_not_verifier_rejection : arkExhaustion ≠ some none := by
  rw [actual_arklib_exhaustion]
  decide

-- A finite field supplies an actual instance of the sampling interface used
-- by checked_soundness. This is only interface inhabitation, not soundness.
@[reducible] def finiteChallengeSampleable (m : Nat) (i : (protocol (ZMod 5) m).ChallengeIdx) :
    SampleableType ((protocol (ZMod 5) m).Challenge i) := inferInstance


end ZkcArkLib.Sumcheck.Scalar.Stopping
