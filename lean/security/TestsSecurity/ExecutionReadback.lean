import ZkcSecurityTools.Bindings.ExecutionReadback
import ZkcSecurity.Bindings.Transcript.SamplingControl
import Mathlib.Data.ZMod.Basic

/-! Focused controls for equation-based execution normalization. These use
different carriers, return layouts and service states from the source client.
All equations retain the complete execution rather than only acceptance. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace TestsSecurity.ExecutionReadback
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.FiatShamir OracleComp OracleSpec

abbrev carriers := uniformCarriers (ZMod 5) (ZMod 5)

section Sampling
variable [∀ event : Domain.Event carriers, SampleableType (Domain.Raw event)]
variable (context : Context) (producer validator : List ServicePort)
  (port : ServicePort) (origin : Origin)
  (oracle : Domain.Oracle (OracleComp (SampledCompiled.Spec carriers)) carriers Nat)
  (env : Domain.Environment carriers) (proof : Domain.Proof carriers) (state : Nat)

theorem private_checkpoint
    (admitted : SampledCompiled.allowed context producer validator .producer port origin = true) :
    Domain.run .producer oracle
      (.call (.checkpoint env) fun _ =>
        .call (.localService port origin) fun value => .done (false, value))
      ⟨[], proof, state⟩ (SampledCompiled.services context producer validator) = (do
        let value ← (liftM ($ᵗ (Domain.Raw (.challenge origin : Domain.Event carriers))) :
          OracleComp (SampledCompiled.Spec carriers) _)
        pure ⟨.returned (false, value), ⟨env, proof, state⟩, []⟩) := by
  normalize_domain_execution [admitted] unfolding []

theorem unauthorized_continuation_stops
    (refused : SampledCompiled.allowed context producer validator .validator port origin = false) :
    Domain.run .validator oracle
      (.call (.localService port origin) fun _ =>
        .call (.checkpoint []) fun _ => .done true)
      ⟨env, proof, state⟩ (SampledCompiled.services context producer validator) =
      pure ⟨.stopped .refused, ⟨env, proof, state⟩, []⟩ := by
  normalize_domain_execution [refused] unfolding []

/-- A sample-dependent stop preserves the entire initial state and has no
post-stop checkpoint. The normalizer must not assume the future draw is good. -/
theorem private_abort (bad : Domain.Raw (.challenge origin : Domain.Event carriers))
    [DecidableEq (Domain.Raw (.challenge origin : Domain.Event carriers))]
    (admitted : SampledCompiled.allowed context producer validator .producer port origin = true) :
    Domain.run .producer oracle
      (.call (.localService port origin) fun value =>
        if value = bad then .halt .abort else .done (value, true))
      ⟨env, proof, state⟩ (SampledCompiled.services context producer validator) = (do
        let value ← (liftM ($ᵗ (Domain.Raw (.challenge origin : Domain.Event carriers))) :
          OracleComp (SampledCompiled.Spec carriers) _)
        pure (if value = bad then ⟨.stopped .abort, ⟨env, proof, state⟩, []⟩
          else ⟨.returned (value, true), ⟨env, proof, state⟩, []⟩)) := by
  classical
  normalize_domain_execution [admitted] unfolding []
  rw [← bind_pure_comp]
  congr 1
  funext value
  split_ifs <;> normalize_domain_execution [] unfolding []
end Sampling

section Deterministic
variable (oracle : Domain.Oracle Id carriers Nat)
  (env : Domain.Environment carriers) (suffix : Domain.Proof carriers) (state : Nat)

theorem heterogeneous_readback (flag : Bool) (value : ZMod 5) :
    Domain.run .validator oracle
      (.call (.receive .boolean "flag" "flag" "sender") fun flag =>
        .call (.receive (.field "coin") "value" "value" "sender") fun value =>
        .done (value, flag))
      ⟨env, .boolean flag :: .field "coin" value :: suffix, state⟩ =
      pure ⟨.returned (value, flag), ⟨env, suffix, state⟩, []⟩ := by
  normalize_domain_process [] unfolding []
  normalize_domain_execution [Domain.Payload.value] unfolding []

theorem wrong_nominal_field_retains_suffix (value : ZMod 5) :
    Domain.run .validator oracle
      (.call (.receive (.field "other") "value" "value" "sender") fun value =>
        .done value)
      ⟨env, .field "coin" value :: suffix, state⟩ =
      pure ⟨.stopped .refused, ⟨env, .field "coin" value :: suffix, state⟩, []⟩ := by
  normalize_domain_execution [Domain.Payload.value] unfolding []

theorem rejected_guard_skips_send (value : ZMod 5) :
    Domain.run .producer oracle
      (Domain.View.sequence (Domain.View.guard 0 [])
        (Domain.View.send "value" "value" "receiver" 1 [])
        [.data (.boolean false), .data (.field "coin" value)])
      ⟨env, suffix, state⟩ =
      pure ⟨.stopped .reject,
        ⟨[.data (.boolean false), .data (.field "coin" value)], suffix, state⟩, []⟩ := by
  normalize_domain_process [] unfolding []
  normalize_domain_execution [] unfolding []

theorem ordered_subtraction (left right : ZMod 5) :
    Domain.run .producer oracle
      (Domain.View.participant [.data (.field "coin"), .data (.field "coin")]
        [.data (.field "coin"), .data (.field "coin")] [2, 0]
        (Domain.View.calculation (ringModel (ZMod 5) (ZMod 5)) (.fieldSubtract "coin")
          [1, 0] [.data (.field "coin")])
        [.data (.field "coin" left), .data (.field "coin" right)])
      ⟨env, suffix, state⟩ =
      pure ⟨.returned
        ⟨[.data (.field "coin" (right - left)), .data (.field "coin" left)],
          [.data (.field "coin" left), .data (.field "coin" right),
            .data (.field "coin" (right - left))]⟩,
        ⟨[.data (.field "coin" left), .data (.field "coin" right)], suffix, state⟩, []⟩ := by
  normalize_domain_process
    [Domain.Calculations.fieldSubtract (F := ZMod 5) (G := ZMod 5)] unfolding []
  normalize_domain_execution [] unfolding []

theorem missing_operand_refuses :
    Domain.run .producer oracle
      (Domain.View.calculation (ringModel (ZMod 5) (ZMod 5)) (.fieldSubtract "coin")
        [1, 0] [.data (.field "coin")] [])
      ⟨env, suffix, state⟩ =
      pure ⟨.stopped .refused, ⟨env, suffix, state⟩, []⟩ := by
  normalize_domain_process [] unfolding []
  normalize_domain_execution [] unfolding []

/-- Normalizing one component must leave the caller's other obligations alone. -/
theorem pending_goal :
    Domain.run .producer oracle (.done true)
      ⟨env, suffix, state⟩ = pure ⟨.returned true, ⟨env, suffix, state⟩, []⟩ ∧
    Domain.run .producer oracle (.done false)
      ⟨env, suffix, state⟩ = pure ⟨.returned false, ⟨env, suffix, state⟩, []⟩ := by
  constructor
  normalize_domain_execution [] unfolding []
  rfl
end Deterministic

noncomputable section
local instance : SampleableType (Fin 3) := SampleableType.ofFintype (Fin 3)

/-- A different failure point and result type use the same ordinary sampling
law. There is no premise constraining the future private sample. -/
theorem ternary_failure {E : Type} {Raw : E → Type} [DecidableEq E]
    [∀ event, SampleableType (Raw event)] :
    HonestSampling.failure (do
      let value ← (liftM ($ᵗ (Fin 3)) : OracleComp (HonestSampling.Spec Raw) _)
      pure (decide (value ≠ 2))) (fun result => result = true) =
      1 / (Fintype.card (Fin 3) : ENNReal) := by
  apply SamplingControl.failure_after_private (2 : Fin 3)
  intro value cache
  by_cases bad : value = 2 <;> simp [bad]

#print axioms private_checkpoint
#print axioms unauthorized_continuation_stops
#print axioms private_abort
#print axioms heterogeneous_readback
#print axioms wrong_nominal_field_retains_suffix
#print axioms rejected_guard_skips_send
#print axioms ordered_subtraction
#print axioms missing_operand_refuses
#print axioms pending_goal
#print axioms ternary_failure

end
end TestsSecurity.ExecutionReadback
