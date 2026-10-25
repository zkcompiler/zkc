module

public import ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Sources

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Honest
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcExamples.Structured
open ZkcSecurity.FiatShamir ZkcSecurity.Families.Sumcheck TableComponent
open ZkcSecurity.Realizations.Sumcheck
open ZkcSecurity.Realizations.Sumcheck.OriginalRaw
open ZkcSecurity.Realizations.Sumcheck.OriginalRoot
open ZkcSecurity.Realizations.Sumcheck
open OriginalHonest
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

def routes0 (handle : Nat) : OriginalHonest.Routes (ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheckProducerRoot.routing handle) (ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.routing handle)
    ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.occurrence0.protocol handle :=
  ⟨_, ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.ProducerCall0.routes handle, ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.occurrence0_routes handle⟩

theorem source (input0 : List F) (input2 : Nat) (handle : Nat) (shape0 : PrimitiveLibrary.HasShape input0 input2 1) (bounded0 : input0.length < indexLimit)
    (admitted : input2 ≤ 2) (history : Domain.History (uniformCarriers F G)) :
    Readback RootPost
      (Original.participant (ringModel F G) ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.program (ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheckProducerRoot.routing handle) 0 (.cons (some input0) (.cons none (.cons (some input2) (.cons none .nil)))) ⟨[], history⟩)
      (Original.participant (ringModel F G) ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.program (ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.routing handle) 1 (.cons (some input0) (.cons (some input0.sum) (.cons (some input2) (.cons (some handle) .nil)))) ⟨[], history⟩) := by
  unfold Original.participant
  rw [ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheckProducerRoot.producer_source input0 input2 shape0 bounded0, ZkcExamples.Structured.Generated.Original.SmallSumcheck.participant_binding]
  simp only [ZkcExamples.Structured.Generated.Original.SmallSumcheck.realized, Original.fold_bind,
    PIR.Process.bind_assoc, Zkc.Construction.ArtifactBinding.fold_done, PIR.Process.bind]
  apply (OriginalHonest.reduce ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.program.payload ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.helper_bodies.sumcheck 2
    (ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheckProducerRoot.routing handle) (ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.routing handle) ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.occurrence0.protocol (by change 0 ≠ 1; decide)
    handle (routes0 handle) input0 input2 shape0 bounded0 admitted history).bind
  intro left0 right0 returned0
  obtain ⟨final0, original0, length0, honest0, reached0, rfl, rfl⟩ := returned0
  have checked0 := ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Sources.check0_honest (G := G) final0
    (by simpa only [original0] using bounded0) (by omega)
  rw [original0] at checked0
  erw [checked0]
  simp only [honest0, decide_true, Zkc.Construction.ArtifactBinding.fold_done]
  exact .done ⟨reached0, rfl, rfl⟩

theorem readback (input0 : List F) (input2 : Nat) (handle : Nat) (shape0 : PrimitiveLibrary.HasShape input0 input2 1) (bounded0 : input0.length < indexLimit)
    (admitted : input2 ≤ 2) (history : Domain.History (uniformCarriers F G)) :
    Readback (ActualPost ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.context 17 18 8 7)
      (Domain.participant (ringModel F G) ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.program ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.context ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheckProducerRoot.artifact (ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheckProducerRoot.inputs input0 input2 history))
      (Domain.participant (ringModel F G) ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.program ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.context ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheckValidatorRoot.artifact (ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheckValidatorRoot.inputs input0 input0.sum input2 history)) :=
  Readback.original (ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheckProducerRoot.producer input0 input2 handle shape0 bounded0 history)
    (ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheckValidatorRoot.validator input0 input0.sum input2 handle history)
    (source input0 input2 handle shape0 bounded0 admitted history)

theorem actual (input0 : List F) (input2 : Nat) (handle : Nat) (shape0 : PrimitiveLibrary.HasShape input0 input2 1) (bounded0 : input0.length < indexLimit)
    (admitted : input2 ≤ 2) (history : Domain.History (uniformCarriers F G)) :
    Readback (fun _ result => Domain.acceptanceAt 0 result.values = some true)
      (Domain.participant (ringModel F G) ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.program ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.context ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheckProducerRoot.artifact (ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheckProducerRoot.inputs input0 input2 history))
      (Domain.participant (ringModel F G) ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.program ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.context ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheckValidatorRoot.artifact (ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheckValidatorRoot.inputs input0 input0.sum input2 history)) :=
  (readback input0 input2 handle shape0 bounded0 admitted history).mono (fun _ _ related => related.acceptance)

end ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Honest
