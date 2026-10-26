module

import ZkcExamples.Structured.OriginalArtifacts.SmallSumcheckProducerRoot
import ZkcExamples.Structured.OriginalArtifacts.TwoSumsProducerRoot

/-! Kernel audits of actual original-to-retained producer certificates, with
nominal delivery and stopped-prefix controls. No concrete execution fixture
or assumed root-process equality supplies the producer evidence. -/
set_option autoImplicit false
namespace TestsSecurity.OriginalProducerBinding
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured.OriginalArtifacts

/-- Even an equal field payload cannot justify changing the delivery origin.
The arbitrary continuation reply remains part of the structural certificate. -/
theorem delivery_identity {carriers : Carriers} (field : String)
    (value : carriers.Field field) (expected actual : Origin) (different : expected ≠ actual)
    (relation : Unit → Unit → Prop)
    (live : PIR.Process (Domain.effects carriers) Unit → Domain.Environment carriers → Prop) :
    ¬ Nonempty (Original.Simulation relation live
      (.call (.observe (.message expected (.field field value))) (fun _ => .done ()))
      (.call (.observe (.message actual (.field field value))) (fun _ => .done ()))) := by
  rintro ⟨derivation⟩
  cases derivation with
  | call operation next => exact different rfl

/-- Adding a refusal after successful original production is observable and
cannot be certified by erasing physical checkpoints. -/
theorem extra_refusal {carriers : Carriers} {A B : Type}
    (relation : A → B → Prop)
    (live : PIR.Process (Domain.effects carriers) A → Domain.Environment carriers → Prop)
    (value : A) :
    ¬ Nonempty (Original.Simulation relation live (.done value) (.halt .refused)) := by
  rintro ⟨derivation⟩
  cases derivation

section Projections
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- The instantiated Small producer projects to the complete actual artifact,
including its physical checkpoints, rather than to a selected result slot. -/
example (raw : List F) (count handle : Nat)
    (shape : ZkcExamples.Structured.PrimitiveLibrary.HasShape raw count 1)
    (bounded : raw.length < indexLimit)
    (history : Domain.History (uniformCarriers F G)) :
    (SmallSumcheckProducerRoot.producer raw count handle shape bounded history).paired.bind
        (fun pair => .done pair.2) =
      Domain.participant (ringModel F G) SmallSumcheckProducerRoot.program SmallSumcheckProducerRoot.context SmallSumcheckProducerRoot.artifact
        (SmallSumcheckProducerRoot.inputs raw count history) :=
  (SmallSumcheckProducerRoot.producer raw count handle shape bounded history).target

/-- The source projection explicitly abstracts only physical checkpoints. -/
example (leftRaw rightRaw : List F) (count handle : Nat)
    (leftShape : ZkcExamples.Structured.PrimitiveLibrary.HasShape leftRaw count 1)
    (leftBound : leftRaw.length < indexLimit)
    (rightShape : ZkcExamples.Structured.PrimitiveLibrary.HasShape rightRaw count 1)
    (rightBound : rightRaw.length < indexLimit)
    (history : Domain.History (uniformCarriers F G)) :
    ((TwoSumsProducerRoot.producer leftRaw rightRaw count handle leftShape leftBound rightShape rightBound history).paired.bind
      (fun pair => .done pair.1)).interpret Original.forgetCheckpoints =
    (Original.participant (ringModel F G) TwoSumsProducerRoot.program (TwoSumsProducerRoot.routing handle) 0
      (.cons (some leftRaw) (.cons (some rightRaw) (.cons none (.cons none
        (.cons (some count) (.cons none .nil)))))) ⟨[], history⟩).interpret
        Original.forgetCheckpoints :=
  (TwoSumsProducerRoot.producer leftRaw rightRaw count handle leftShape leftBound rightShape rightBound history).source

end Projections

#print axioms ZkcExamples.Structured.SumcheckArtifacts.OriginalProducer.original_round
#print axioms ZkcExamples.Structured.SumcheckArtifacts.OriginalProducer.ProducerCallback.loop
#print axioms ZkcExamples.Structured.SumcheckArtifacts.OriginalProducer.ProducerCallback.reduce
#print axioms SmallSumcheck.ProducerCall0.round
#print axioms TwoSums.ProducerCall0.round
#print axioms TwoSums.ProducerCall1.round
#print axioms SmallSumcheckProducerRoot.producer
#print axioms TwoSumsProducerRoot.producer
#print axioms Zkc.Construction.Original.produce_eq
#print axioms delivery_identity
#print axioms extra_refusal

end TestsSecurity.OriginalProducerBinding
