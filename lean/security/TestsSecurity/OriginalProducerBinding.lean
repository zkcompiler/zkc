module

import ZkcExamples.Structured.Generated.Connections.SmallSumcheck
import ZkcExamples.Structured.Generated.Connections.TwoSums

/-! Kernel audits of actual original-to-retained producer certificates, with
nominal delivery and stopped-prefix controls. No concrete execution fixture
or assumed root-process equality supplies the producer evidence. -/
set_option autoImplicit false
namespace TestsSecurity.OriginalProducerBinding
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured.Generated.Connections

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
variable (model : DomainModel) (physical : Domain.Environment model.toCarriers)

/-- Every physical row, including ABI refusals, projects to the whole artifact. -/
example : ((SmallSumcheck.producerFacts.simulation model physical).paired.bind
    (fun pair => .done pair.2)) =
    Domain.participant model SmallSumcheck.program SmallSumcheck.context
      SmallSumcheck.producerArtifact physical :=
  (SmallSumcheck.producerFacts.simulation model physical).target

/-- Source projection preserves every optional return and nominal checkpoint. -/
example : (((TwoSums.producerFacts.simulation model physical).paired.bind
    (fun pair => .done pair.1)).interpret Original.forgetCheckpoints) =
    (TwoSums.producer.source model physical).interpret Original.forgetCheckpoints :=
  (TwoSums.producerFacts.simulation model physical).source

/-- Both producer roots establish the method-independent fixed connection. -/
example : SourceConnection.Connected SmallSumcheck.program SmallSumcheck.producerRouting
    SmallSumcheck.context.producer SmallSumcheck.producer.inputs.abi SmallSumcheck.producerArtifact :=
  SmallSumcheck.producerConnected
example : SourceConnection.Connected TwoSums.program TwoSums.producerRouting
    TwoSums.context.producer TwoSums.producer.inputs.abi TwoSums.producerArtifact :=
  TwoSums.producerConnected

end Projections

#print axioms SmallSumcheck.producer
#print axioms TwoSums.producer
#print axioms SmallSumcheck.producerConnected
#print axioms TwoSums.producerConnected
#print axioms Original.Simulation.runM
#print axioms delivery_identity
#print axioms extra_refusal

end TestsSecurity.OriginalProducerBinding
