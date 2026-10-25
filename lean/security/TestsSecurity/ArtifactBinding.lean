module

import TestsSecurity.OriginalPairExecution

/-! Kernel audits and refusal controls for original-to-retained construction.
No concrete field execution, fixed callback recognizer, or receipt is used. -/
set_option autoImplicit false
namespace TestsSecurity.ArtifactBinding
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Examples.Generated.OriginalArtifacts

/-- Changing a nominal query identity cannot be certified by the structural
rules. Checkpoints cannot hide the differing observable operation. -/
theorem query_identity {carriers : Carriers}
    (history : Domain.History carriers) (expected actual : Origin)
    (different : expected ≠ actual)
    (relation : Unit → Unit → Prop)
    (live : PIR.Process (Domain.effects carriers) Unit → Domain.Environment carriers → Prop) :
    ¬ Nonempty (Original.Simulation relation live
      (.call (.query history expected) (fun _ => .done ()))
      (.call (.query history actual) (fun _ => .done ()))) := by
  rintro ⟨derivation⟩
  cases derivation with
  | call operation next => exact different rfl

/-- An original refusal cannot be paired with an artifact that queries instead. -/
theorem refusal_before_query {carriers : Carriers}
    (history : Domain.History carriers) (origin : Origin)
    (relation : Unit → Unit → Prop)
    (live : PIR.Process (Domain.effects carriers) Unit → Domain.Environment carriers → Prop) :
    ¬ Nonempty (Original.Simulation relation live
      (.halt .refused) (.call (.query history origin) (fun _ => .done ()))) := by
  rintro ⟨derivation⟩
  cases derivation

/-- Omitting a guard that rejects cannot be certified as successful production.
This control concerns the failing branch; producer correspondence separately
states its honest-input admission assumptions. -/
theorem omitted_failed_guard {carriers : Carriers} {A B : Type}
    (relation : A → B → Prop)
    (live : PIR.Process (Domain.effects carriers) A → Domain.Environment carriers → Prop)
    (value : B) :
    ¬ Nonempty (Original.Simulation relation live (.halt .reject) (.done value)) := by
  rintro ⟨derivation⟩
  cases derivation

/-- The real Small source route refuses a handle different from the selected
root service, independently of the callback's field values. -/
example (selected supplied : Nat) (different : supplied ≠ selected)
    (frames : Original.Frames) (site field : String) :
    (SmallSumcheck.routing selected).draw frames site field supplied = none := by
  simp [Original.Routing.draw, different]

example (selected supplied : Nat) (different : supplied ≠ selected)
    (frames : Original.Frames) (site field : String) :
    (TwoSums.routing selected).draw frames site field supplied = none := by
  simp [Original.Routing.draw, different]

#print axioms Zkc.Construction.ArtifactBinding.captures_trans
#print axioms ZkcSecurity.Realizations.Sumcheck.ArtifactBinding.original_round
#print axioms ZkcSecurity.Realizations.Sumcheck.ArtifactBinding.VerifierCallback.reduce
#print axioms ZkcSecurity.Realizations.Sumcheck.ArtifactBinding.terminal
#print axioms SmallSumcheck.ValidatorCall0.round
#print axioms TwoSums.ValidatorCall0.round
#print axioms TwoSums.ValidatorCall1.round
#print axioms SmallSumcheckValidatorRoot.validator
#print axioms TwoSumsValidatorRoot.validator
#print axioms SmallSumcheckProducerRoot.producer
#print axioms TwoSumsProducerRoot.producer
#print axioms TestsSecurity.OriginalPairExecution.Small.execute_pair
#print axioms TestsSecurity.OriginalPairExecution.Two.execute_pair
#print axioms query_identity
#print axioms refusal_before_query
#print axioms omitted_failed_guard

end TestsSecurity.ArtifactBinding
