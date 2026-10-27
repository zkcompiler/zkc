module

public import ZkcSecurity.Examples.Generated.OriginalSecurity.TwoSums.Sources

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Examples.Generated.OriginalSecurity.TwoSums.Honest
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcExamples.Structured
open ZkcSecurity.FiatShamir ZkcSecurity.Families.Sumcheck TableComponent
open ZkcSecurity.Realizations.Sumcheck
open ZkcSecurity.Realizations.Sumcheck.OriginalRaw
open ZkcSecurity.Realizations.Sumcheck.OriginalRoot
open ZkcSecurity.Realizations.Sumcheck
open OriginalHonest
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

def routes0 (handle : Nat) : OriginalHonest.Routes (ZkcExamples.Structured.OriginalArtifacts.TwoSumsProducerRoot.routing handle) (ZkcExamples.Structured.OriginalArtifacts.TwoSums.routing handle)
    ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence0.protocol handle :=
  ⟨_, ZkcExamples.Structured.OriginalArtifacts.TwoSums.ProducerCall0.routes handle, ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence0_routes handle⟩

def routes1 (handle : Nat) : OriginalHonest.Routes (ZkcExamples.Structured.OriginalArtifacts.TwoSumsProducerRoot.routing handle) (ZkcExamples.Structured.OriginalArtifacts.TwoSums.routing handle)
    ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence1.protocol handle :=
  ⟨_, ZkcExamples.Structured.OriginalArtifacts.TwoSums.ProducerCall1.routes handle, ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence1_routes handle⟩

theorem source (input0 : List F) (input1 : List F) (input4 : Nat) (handle : Nat) (shape0 : PrimitiveLibrary.HasShape input0 input4 1) (bounded0 : input0.length < indexLimit) (shape1 : PrimitiveLibrary.HasShape input1 input4 1) (bounded1 : input1.length < indexLimit)
    (admitted : input4 ≤ 4) (history : Domain.History (uniformCarriers F G)) :
    Readback RootPost
      (Original.participant (ringModel F G) ZkcExamples.Structured.OriginalArtifacts.TwoSums.program (ZkcExamples.Structured.OriginalArtifacts.TwoSumsProducerRoot.routing handle) 0 (.cons (some input0) (.cons (some input1) (.cons none (.cons none (.cons (some input4) (.cons none .nil)))))) ⟨[], history⟩)
      (Original.participant (ringModel F G) ZkcExamples.Structured.OriginalArtifacts.TwoSums.program (ZkcExamples.Structured.OriginalArtifacts.TwoSums.routing handle) 1 (.cons (some input0) (.cons (some input1) (.cons (some input0.sum) (.cons (some input1.sum) (.cons (some input4) (.cons (some handle) .nil)))))) ⟨[], history⟩) := by
  unfold Original.participant
  rw [ZkcExamples.Structured.OriginalArtifacts.TwoSumsProducerRoot.producer_source input0 input1 input4 shape0 bounded0 shape1 bounded1, ZkcExamples.Structured.Generated.Original.TwoSums.participant_binding]
  simp only [ZkcExamples.Structured.Generated.Original.TwoSums.realized, Original.fold_bind,
    PIR.Process.bind_assoc, Zkc.Construction.ArtifactBinding.fold_done, PIR.Process.bind]
  apply (OriginalHonest.reduce ZkcExamples.Structured.OriginalArtifacts.TwoSums.program.payload ZkcExamples.Structured.OriginalArtifacts.TwoSums.helper_bodies.sumcheck 4
    (ZkcExamples.Structured.OriginalArtifacts.TwoSumsProducerRoot.routing handle) (ZkcExamples.Structured.OriginalArtifacts.TwoSums.routing handle) ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence0.protocol (by change 0 ≠ 1; decide)
    handle (routes0 handle) input0 input4 shape0 bounded0 admitted history).bind
  intro left0 right0 returned0
  obtain ⟨final0, original0, length0, honest0, reached0, rfl, rfl⟩ := returned0
  have checked0 := ZkcSecurity.Examples.Generated.OriginalSecurity.TwoSums.Sources.check0_honest (G := G) final0
    (by simpa only [original0] using bounded0) (by omega)
  rw [original0] at checked0
  erw [checked0]
  simp only [honest0, decide_true, Zkc.Construction.ArtifactBinding.fold_done, PIR.Process.bind]
  apply (OriginalHonest.reduce ZkcExamples.Structured.OriginalArtifacts.TwoSums.program.payload ZkcExamples.Structured.OriginalArtifacts.TwoSums.helper_bodies.sumcheck 4
    (ZkcExamples.Structured.OriginalArtifacts.TwoSumsProducerRoot.routing handle) (ZkcExamples.Structured.OriginalArtifacts.TwoSums.routing handle) ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence1.protocol (by change 0 ≠ 1; decide)
    handle (routes1 handle) input1 input4 shape1 bounded1 admitted reached0).bind
  intro left1 right1 returned1
  obtain ⟨final1, original1, length1, honest1, reached1, rfl, rfl⟩ := returned1
  have checked1 := ZkcSecurity.Examples.Generated.OriginalSecurity.TwoSums.Sources.check1_honest (G := G) final1
    (by simpa only [original1] using bounded1) (by omega)
  rw [original1] at checked1
  erw [checked1]
  simp only [honest1, decide_true, Zkc.Construction.ArtifactBinding.fold_done, PIR.Process.bind]
  rw [ZkcSecurity.Examples.Generated.OriginalSecurity.TwoSums.Sources.combine]
  simp only [both, Values.get, Option.bind, Option.map, Bool.true_and, Zkc.Construction.ArtifactBinding.fold_done]
  exact .done ⟨reached1, rfl, rfl⟩

theorem readback (input0 : List F) (input1 : List F) (input4 : Nat) (handle : Nat) (shape0 : PrimitiveLibrary.HasShape input0 input4 1) (bounded0 : input0.length < indexLimit) (shape1 : PrimitiveLibrary.HasShape input1 input4 1) (bounded1 : input1.length < indexLimit)
    (admitted : input4 ≤ 4) (history : Domain.History (uniformCarriers F G)) :
    Readback (ActualPost ZkcExamples.Structured.OriginalArtifacts.TwoSums.context 33 34 16 14)
      (Domain.participant (ringModel F G) ZkcExamples.Structured.OriginalArtifacts.TwoSums.program ZkcExamples.Structured.OriginalArtifacts.TwoSums.context ZkcExamples.Structured.OriginalArtifacts.TwoSumsProducerRoot.artifact (ZkcExamples.Structured.OriginalArtifacts.TwoSumsProducerRoot.inputs input0 input1 input4 history))
      (Domain.participant (ringModel F G) ZkcExamples.Structured.OriginalArtifacts.TwoSums.program ZkcExamples.Structured.OriginalArtifacts.TwoSums.context ZkcExamples.Structured.OriginalArtifacts.TwoSumsValidatorRoot.artifact (ZkcExamples.Structured.OriginalArtifacts.TwoSumsValidatorRoot.inputs input0 input1 input0.sum input1.sum input4 history)) :=
  Readback.original (ZkcExamples.Structured.OriginalArtifacts.TwoSumsProducerRoot.producer input0 input1 input4 handle shape0 bounded0 shape1 bounded1 history)
    (ZkcExamples.Structured.OriginalArtifacts.TwoSumsValidatorRoot.validator input0 input1 input0.sum input1.sum input4 handle history)
    (source input0 input1 input4 handle shape0 bounded0 shape1 bounded1 admitted history)

theorem actual (input0 : List F) (input1 : List F) (input4 : Nat) (handle : Nat) (shape0 : PrimitiveLibrary.HasShape input0 input4 1) (bounded0 : input0.length < indexLimit) (shape1 : PrimitiveLibrary.HasShape input1 input4 1) (bounded1 : input1.length < indexLimit)
    (admitted : input4 ≤ 4) (history : Domain.History (uniformCarriers F G)) :
    Readback (fun _ result => Domain.acceptanceAt 0 result.values = some true)
      (Domain.participant (ringModel F G) ZkcExamples.Structured.OriginalArtifacts.TwoSums.program ZkcExamples.Structured.OriginalArtifacts.TwoSums.context ZkcExamples.Structured.OriginalArtifacts.TwoSumsProducerRoot.artifact (ZkcExamples.Structured.OriginalArtifacts.TwoSumsProducerRoot.inputs input0 input1 input4 history))
      (Domain.participant (ringModel F G) ZkcExamples.Structured.OriginalArtifacts.TwoSums.program ZkcExamples.Structured.OriginalArtifacts.TwoSums.context ZkcExamples.Structured.OriginalArtifacts.TwoSumsValidatorRoot.artifact (ZkcExamples.Structured.OriginalArtifacts.TwoSumsValidatorRoot.inputs input0 input1 input0.sum input1.sum input4 history)) :=
  (readback input0 input1 input4 handle shape0 bounded0 shape1 bounded1 admitted history).mono (fun _ _ related => related.acceptance)

end ZkcSecurity.Examples.Generated.OriginalSecurity.TwoSums.Honest
