module

import TestsSecurity.OriginalPairExecution

/-! Kernel audits and refusal controls for original-to-retained construction.
No concrete field execution, fixed callback recognizer, or receipt is used. -/
set_option autoImplicit false
namespace TestsSecurity.ArtifactBinding
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured.Generated.Connections

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
This control concerns the failing branch; the connection also covers malformed inputs and reached stops. -/
theorem omitted_failed_guard {carriers : Carriers} {A B : Type}
    (relation : A → B → Prop)
    (live : PIR.Process (Domain.effects carriers) A → Domain.Environment carriers → Prop)
    (value : B) :
    ¬ Nonempty (Original.Simulation relation live (.halt .reject) (.done value)) := by
  rintro ⟨derivation⟩
  cases derivation

/-- Every source route refuses a handle different from the capability selected
by the checked root ABI, independently of callback values and occurrence frames. -/
theorem wrong_query_handle (routing : Original.Routing) (supplied : Nat)
    (different : supplied ≠ routing.selectedHandle)
    (frames : Original.Frames) (site field : String) :
    routing.draw frames site field supplied = none := by
  simp [Original.Routing.draw, different]

example (supplied : Nat) (different : supplied ≠ SmallSumcheck.validatorRouting.selectedHandle)
    (frames : Original.Frames) (site field : String) :
    SmallSumcheck.validatorRouting.draw frames site field supplied = none :=
  wrong_query_handle _ supplied different frames site field

example (supplied : Nat) (different : supplied ≠ TwoSums.validatorRouting.selectedHandle)
    (frames : Original.Frames) (site field : String) :
    TwoSums.validatorRouting.draw frames site field supplied = none :=
  wrong_query_handle _ supplied different frames site field

#print axioms SmallSumcheck.validatorConnected
#print axioms TwoSums.validatorConnected
#print axioms SmallSumcheck.producerConnected
#print axioms TwoSums.producerConnected
#print axioms wrong_query_handle
#print axioms TestsSecurity.OriginalPairExecution.Small.execute_pair
#print axioms TestsSecurity.OriginalPairExecution.Two.execute_pair
#print axioms query_identity
#print axioms refusal_before_query
#print axioms omitted_failed_guard

end TestsSecurity.ArtifactBinding
