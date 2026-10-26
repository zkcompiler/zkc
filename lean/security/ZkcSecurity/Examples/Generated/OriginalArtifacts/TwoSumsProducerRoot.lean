module

public import ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums
public import ZkcExamples.Structured.Generated.Original.TwoSums
public import ZkcExamples.Structured.Generated.OriginalArtifacts.TwoSumsProducerSource
public import ZkcSecurity.Realizations.Sumcheck.ArtifactRoot
public import ZkcExamples.Structured.NormalFormSteps
public import Zkc.Construction.OriginalCorrespondence

public meta import Zkc.Construction.ArtifactBindingTactic
public meta import ZkcSecurity.Tools.ProcessView

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSumsProducerRoot
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcExamples.Structured
open ZkcSecurity.Realizations.Sumcheck.ArtifactBinding
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

attribute [local irreducible] Zkc.Construction.Original.fold ZkcExamples.Structured.OriginalSumcheckLibrary.reduce Zkc.Construction.Domain.View.loop Zkc.Source.Participant.owned Zkc.Source.Structured.invoke Zkc.Construction.Domain.callHelper
open ZkcSecurity.Realizations.Sumcheck.ArtifactRoot
abbrev program := ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.program
abbrev context := ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.context
abbrev artifact := ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.producerArtifact
abbrev routing := ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.ProducerCall0.routing
abbrev RootReturns := ProducerReturns (F := F) (G := G)
def inputs (input0 : List F) (input1 : List F) (input4 : Nat) (history : Domain.History (uniformCarriers F G)) : Domain.Environment (uniformCarriers F G) :=
  [.data (.vector "bls12-381.fr" input0), .data (.vector "bls12-381.fr" input1), .data (.index input4), .transcript context.suite history]

open ZkcSecurity.Realizations.Sumcheck.OriginalProducer
theorem sourceHelper8_identity : ZkcExamples.Structured.Generated.Original.TwoSums.sourceHelper8.helper = ({ name := "zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a",   kind := Zkc.Source.Structured.HelperKind.local,   inputs := [Zkc.Source.Structured.Ty.vector "bls12-381.fr",              Zkc.Source.Structured.Ty.index,              Zkc.Source.Structured.Ty.index],   outputs := [Zkc.Source.Structured.Ty.vector "bls12-381.fr",               Zkc.Source.Structured.Ty.index,               Zkc.Source.Structured.Ty.index] }) := by kernel_rfl

theorem sourceHelper31_identity : ZkcExamples.Structured.Generated.Original.TwoSums.sourceHelper31.helper = ({ name := "s3h7a6b637h626f6f6c65616e4h626f7468",   kind := Zkc.Source.Structured.HelperKind.math,   inputs := [Zkc.Source.Structured.Ty.boolean, Zkc.Source.Structured.Ty.boolean],   outputs := [Zkc.Source.Structured.Ty.boolean] }) := by kernel_rfl

theorem mathHelper31 (left right : Option Bool) :
    invoke (OriginalSumcheckLibrary.helpers (F := F) (G := G) program.payload).components ZkcExamples.Structured.Generated.Original.TwoSums.sourceHelper31.helper (.cons left (.cons right .nil)) =
      .done (.cons (left.bind fun x => right.map fun y => x && y) .nil) := by
  have association : BodyIn program.payload.definitions ZkcExamples.Structured.Generated.Original.TwoSums.sourceHelper31.helper ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs.helper31Body := by bind_structured_bodies
  rw [← (OriginalSumcheckLibrary.helpers_lift program.payload).components, SumcheckVerifierHelpers.component_body_plain program.payload ZkcExamples.Structured.Generated.Original.TwoSums.sourceHelper31.helper ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs.helper31Body association]
  cases left <;> cases right <;> rfl

theorem producer_source (input0 : List F) (input1 : List F) (input4 : Nat) (shape0 : PrimitiveLibrary.HasShape input0 input4 1) (bounded0 : input0.length < indexLimit) (shape1 : PrimitiveLibrary.HasShape input1 input4 1) (bounded1 : input1.length < indexLimit) :
    Occurrence.participant (ringModel F G) program 0 ((.cons (some input0) (.cons (some input1) (.cons none (.cons none (.cons (some input4) (.cons none .nil))))))) =
  (OriginalSumcheckLibrary.reduce program.payload 4 ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.occurrence0.protocol 0 []
    (.cons (some input0) (.cons (some input4) (.cons (some 1) (.cons none (.cons (some input4) (.cons none .nil))))))).bind fun _ =>
  (OriginalSumcheckLibrary.reduce program.payload 4 ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.occurrence1.protocol 0 []
    (.cons (some input1) (.cons (some input4) (.cons (some 1) (.cons none (.cons (some input4) (.cons none .nil))))))).bind fun _ =>
  .done (.cons none .nil) := by
  rw [ZkcExamples.Structured.Generated.OriginalArtifacts.TwoSumsProducerSource.participant_binding]
  simp only [ZkcExamples.Structured.Generated.OriginalArtifacts.TwoSumsProducerSource.realized, ZkcExamples.Structured.Generated.OriginalArtifacts.TwoSumsProducerSource.step0, ZkcExamples.Structured.Generated.OriginalArtifacts.TwoSumsProducerSource.step1Realized, ZkcExamples.Structured.Generated.OriginalArtifacts.TwoSumsProducerSource.step2, ZkcExamples.Structured.Generated.OriginalArtifacts.TwoSumsProducerSource.step3Realized, ZkcExamples.Structured.Generated.OriginalArtifacts.TwoSumsProducerSource.step4, ZkcExamples.Structured.OriginalSumcheckProducerCalls.realizeProducerCall]
  erw [ZkcExamples.Structured.OriginalSumcheckProducerCalls.table_owned program.payload ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.helper_bodies.sumcheck input0 input4 shape0 bounded0]
  dsimp only [Values.get, PIR.Process.bind]
  erw [ZkcExamples.Structured.OriginalSumcheckProducerCalls.table_owned program.payload ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.helper_bodies.sumcheck input1 input4 shape1 bounded1]
  dsimp only [Values.get, PIR.Process.bind]
  simp only [mathHelper31, PIR.Process.bind, PIR.Process.bind_assoc]
  rfl

def producer (input0 : List F) (input1 : List F) (input4 : Nat) (handle : Nat) (shape0 : PrimitiveLibrary.HasShape input0 input4 1) (bounded0 : input0.length < indexLimit) (shape1 : PrimitiveLibrary.HasShape input1 input4 1) (bounded1 : input1.length < indexLimit) (history : Domain.History (uniformCarriers F G)) :
    Original.Producer (model := ringModel F G) (program := program) (routing handle) artifact
      (inputs input0 input1 input4 history) ((.cons (some input0) (.cons (some input1) (.cons none (.cons none (.cons (some input4) (.cons none .nil))))))) ⟨[], history⟩
      (RootReturns context 33 34)
      (fun _ frame => Zkc.Construction.ArtifactBinding.Captures (inputs input0 input1 input4 history) frame) := by
  change Original.Simulation _ _ _ _
  have countBound : input4 < indexLimit := lt_trans shape0.2.1 (by decide +kernel)
  let capture0  : Domain.Environment (uniformCarriers F G) := [.data (.vector "bls12-381.fr" input0), .data (.vector "bls12-381.fr" input1), .data (.index input4), .transcript context.suite history, .data (.index 1), .data (.vector "bls12-381.fr" input0), .data (.index input4), .data (.index 1), .data (.index 1), .data (.boolean true), .data (.boolean false), .data (.boolean false), .data (.boolean true), .data (.vector "bls12-381.fr" [])]
  have loopRule0  :=
    (ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.ProducerCall0.callback (F := F) (G := G) handle).reduce program ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.helper_bodies.sumcheck (routing handle) ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.occurrence0 (by decide +kernel)
      context ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.ProducerCall0.outputs 14 4 handle _ (capture0) rfl input0 input4 input4 2 [5, 6, 7, 13, 3]
      shape0 bounded0 countBound (by omega) history rfl rfl
  let capture1 (raw0 : List F) (width0 : Nat) (point0 : List F) (history0 : Domain.History (uniformCarriers F G)) : Domain.Environment (uniformCarriers F G) := [.data (.vector "bls12-381.fr" input0), .data (.vector "bls12-381.fr" input1), .data (.index input4), .transcript context.suite history, .data (.index 1), .data (.vector "bls12-381.fr" input0), .data (.index input4), .data (.index 1), .data (.index 1), .data (.boolean true), .data (.boolean false), .data (.boolean false), .data (.boolean true), .data (.vector "bls12-381.fr" []), .data (.vector "bls12-381.fr" raw0), .data (.index 0), .data (.index width0), .data (.vector "bls12-381.fr" point0), .transcript context.suite history0, .data (.index 1), .data (.vector "bls12-381.fr" input1), .data (.index input4), .data (.index 1), .data (.index 1), .data (.boolean true), .data (.boolean false), .data (.boolean false), .data (.boolean true), .data (.vector "bls12-381.fr" [])]
  have loopRule1 (raw0 : List F) (width0 : Nat) (point0 : List F) (history0 : Domain.History (uniformCarriers F G)) :=
    (ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.ProducerCall1.callback (F := F) (G := G) handle).reduce program ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.helper_bodies.sumcheck (routing handle) ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.occurrence1 (by decide +kernel)
      context ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.ProducerCall1.outputs 29 4 handle _ (capture1 raw0 width0 point0 history0) rfl input1 input4 input4 2 [20, 21, 22, 28, 18]
      shape1 bounded1 countBound (by omega) history0 rfl rfl
  unfold Original.participant
  rw [producer_source input0 input1 input4 shape0 bounded0 shape1 bounded1]
  rw [ZkcExamples.Structured.Generated.Constructed.TwoSumsProducer.participant_eq]
  unfold_component_bodies [ZkcExamples.Structured.Generated.Constructed.TwoSumsProducer.view]
  derive_artifact_binding [Original.Simulation.bind (loopRule0 ), Original.Simulation.bind (loopRule1 _ _ _ _)]
    normalizing (
      try (rename_i source final returned; change ReduceReturns _ _ _ _ _ at returned; apply Classical.choice; obtain ⟨nextRaw, width, point, reached, rfl, rfl, nextShape, nextBound⟩ := returned; refine ⟨?_⟩)
      try simp only [Original.fold_bind, Zkc.Construction.ArtifactBinding.fold_done]
      try normalize_artifact_operations [ZkcSecurity.Realizations.Sumcheck.DomainHelpers.table program ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.helper_bodies.sumcheck input0 input4 1 shape0 bounded0 countBound (by decide +kernel), ZkcSecurity.Realizations.Sumcheck.DomainHelpers.less program ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.helper_bodies.sumcheck input4 input4 countBound countBound, ZkcSecurity.Realizations.Sumcheck.DomainHelpers.empty program ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.helper_bodies.sumcheck, ZkcSecurity.Realizations.Sumcheck.DomainHelpers.table program ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.helper_bodies.sumcheck input1 input4 1 shape1 bounded1 countBound (by decide +kernel), boolean_and] unfolding [ZkcExamples.Structured.Generated.Constructed.TwoSumsProducer.inputSorts, ZkcExamples.Structured.Generated.Constructed.TwoSumsProducer.outputSorts, ZkcExamples.Structured.Generated.Constructed.TwoSumsProducer.returned, inputs, capture0, capture1, ZkcSecurity.Realizations.Sumcheck.OriginalProducer.carried, context, ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.context]
      try simp only [Nat.lt_irrefl, decide_false, Nat.sub_self]
      change Original.Simulation _ _ _ _)
    solving (first
      | (rename_i source final returned; change ReduceReturns _ _ _ _ _ at returned; obtain ⟨nextRaw, width, point, reached, sourceEq, frameEq, nextShape, nextBound⟩ := returned; rw [frameEq]; rfl)
      | rfl
      | (intro process frame retained; apply Zkc.Construction.ArtifactBinding.captures_trans (inner := retained); rfl)
      | (unfold RootReturns ProducerReturns; exact ⟨rfl, rfl, rfl, rfl, rfl⟩))

end ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSumsProducerRoot
