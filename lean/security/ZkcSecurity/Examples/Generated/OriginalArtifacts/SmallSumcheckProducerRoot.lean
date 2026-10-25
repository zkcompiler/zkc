module

public import ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck
public import ZkcExamples.Structured.Generated.Original.SmallSumcheck
public import ZkcExamples.Structured.Generated.OriginalArtifacts.SmallSumcheckProducerSource
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
namespace ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheckProducerRoot
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcExamples.Structured
open ZkcSecurity.Realizations.Sumcheck.ArtifactBinding
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

attribute [local irreducible] Zkc.Construction.Original.fold ZkcExamples.Structured.OriginalSumcheckLibrary.reduce Zkc.Construction.Domain.View.loop Zkc.Source.Participant.owned Zkc.Source.Structured.invoke Zkc.Construction.Domain.callHelper
open ZkcSecurity.Realizations.Sumcheck.ArtifactRoot
abbrev program := ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.program
abbrev context := ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.context
abbrev artifact := ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.producerArtifact
abbrev routing := ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.ProducerCall0.routing
abbrev RootReturns := ProducerReturns (F := F) (G := G)
def inputs (input0 : List F) (input2 : Nat) (history : Domain.History (uniformCarriers F G)) : Domain.Environment (uniformCarriers F G) :=
  [.data (.vector "bls12-381.fr" input0), .data (.index input2), .transcript context.suite history]

open ZkcSecurity.Realizations.Sumcheck.OriginalProducer
theorem sourceHelper8_identity : ZkcExamples.Structured.Generated.Original.SmallSumcheck.sourceHelper8.helper = ({ name := "zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a",   kind := Zkc.Source.Structured.HelperKind.local,   inputs := [Zkc.Source.Structured.Ty.vector "bls12-381.fr",              Zkc.Source.Structured.Ty.index,              Zkc.Source.Structured.Ty.index],   outputs := [Zkc.Source.Structured.Ty.vector "bls12-381.fr",               Zkc.Source.Structured.Ty.index,               Zkc.Source.Structured.Ty.index] }) := by kernel_rfl

theorem producer_source (input0 : List F) (input2 : Nat) (shape0 : PrimitiveLibrary.HasShape input0 input2 1) (bounded0 : input0.length < indexLimit) :
    Occurrence.participant (ringModel F G) program 0 ((.cons (some input0) (.cons none (.cons (some input2) (.cons none .nil))))) =
  (OriginalSumcheckLibrary.reduce program.payload 2 ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.occurrence0.protocol 0 []
    (.cons (some input0) (.cons (some input2) (.cons (some 1) (.cons none (.cons (some input2) (.cons none .nil))))))).bind fun _ =>
  .done (.cons none .nil) := by
  rw [ZkcExamples.Structured.Generated.OriginalArtifacts.SmallSumcheckProducerSource.participant_binding]
  simp only [ZkcExamples.Structured.Generated.OriginalArtifacts.SmallSumcheckProducerSource.realized, ZkcExamples.Structured.Generated.OriginalArtifacts.SmallSumcheckProducerSource.step0, ZkcExamples.Structured.Generated.OriginalArtifacts.SmallSumcheckProducerSource.step1Realized, ZkcExamples.Structured.OriginalSumcheckProducerCalls.realizeProducerCall]
  erw [ZkcExamples.Structured.OriginalSumcheckProducerCalls.table_owned program.payload ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.helper_bodies.sumcheck input0 input2 shape0 bounded0]
  dsimp only [Values.get, PIR.Process.bind]
  simp only [PIR.Process.bind, PIR.Process.bind_assoc]
  rfl

def producer (input0 : List F) (input2 : Nat) (handle : Nat) (shape0 : PrimitiveLibrary.HasShape input0 input2 1) (bounded0 : input0.length < indexLimit) (history : Domain.History (uniformCarriers F G)) :
    Original.Producer (model := ringModel F G) (program := program) (routing handle) artifact
      (inputs input0 input2 history) ((.cons (some input0) (.cons none (.cons (some input2) (.cons none .nil))))) ⟨[], history⟩
      (RootReturns context 17 18)
      (fun _ frame => Zkc.Construction.ArtifactBinding.Captures (inputs input0 input2 history) frame) := by
  change Original.Simulation _ _ _ _
  have countBound : input2 < indexLimit := lt_trans shape0.2.1 (by decide +kernel)
  let capture0  : Domain.Environment (uniformCarriers F G) := [.data (.vector "bls12-381.fr" input0), .data (.index input2), .transcript context.suite history, .data (.index 1), .data (.vector "bls12-381.fr" input0), .data (.index input2), .data (.index 1), .data (.index 1), .data (.boolean true), .data (.boolean false), .data (.boolean false), .data (.boolean true), .data (.vector "bls12-381.fr" [])]
  have loopRule0  :=
    (ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.ProducerCall0.callback (F := F) (G := G) handle).reduce program ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.helper_bodies.sumcheck (routing handle) ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.occurrence0 (by decide +kernel)
      context ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.ProducerCall0.outputs 13 2 handle _ (capture0) rfl input0 input2 input2 1 [4, 5, 6, 12, 2]
      shape0 bounded0 countBound (by omega) history rfl rfl
  unfold Original.participant
  rw [producer_source input0 input2 shape0 bounded0]
  rw [ZkcExamples.Structured.Generated.Constructed.SmallSumcheckProducer.participant_eq]
  unfold_component_bodies [ZkcExamples.Structured.Generated.Constructed.SmallSumcheckProducer.view]
  derive_artifact_binding [Original.Simulation.bind (loopRule0 )]
    normalizing (
      try (rename_i source final returned; change ReduceReturns _ _ _ _ _ at returned; apply Classical.choice; obtain ⟨nextRaw, width, point, reached, rfl, rfl, nextShape, nextBound⟩ := returned; refine ⟨?_⟩)
      try simp only [Original.fold_bind, Zkc.Construction.ArtifactBinding.fold_done]
      try normalize_artifact_operations [ZkcSecurity.Realizations.Sumcheck.DomainHelpers.table program ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.helper_bodies.sumcheck input0 input2 1 shape0 bounded0 countBound (by decide +kernel), ZkcSecurity.Realizations.Sumcheck.DomainHelpers.less program ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.helper_bodies.sumcheck input2 input2 countBound countBound, ZkcSecurity.Realizations.Sumcheck.DomainHelpers.empty program ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.helper_bodies.sumcheck, boolean_and] unfolding [ZkcExamples.Structured.Generated.Constructed.SmallSumcheckProducer.inputSorts, ZkcExamples.Structured.Generated.Constructed.SmallSumcheckProducer.outputSorts, ZkcExamples.Structured.Generated.Constructed.SmallSumcheckProducer.returned, inputs, capture0, ZkcSecurity.Realizations.Sumcheck.OriginalProducer.carried, context, ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.context]
      try simp only [Nat.lt_irrefl, decide_false, Nat.sub_self]
      change Original.Simulation _ _ _ _)
    solving (first
      | (rename_i source final returned; change ReduceReturns _ _ _ _ _ at returned; obtain ⟨nextRaw, width, point, reached, sourceEq, frameEq, nextShape, nextBound⟩ := returned; rw [frameEq]; rfl)
      | rfl
      | (intro process frame retained; apply Zkc.Construction.ArtifactBinding.captures_trans (inner := retained); rfl)
      | (unfold RootReturns ProducerReturns; exact ⟨rfl, rfl, rfl, rfl, rfl⟩))

end ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheckProducerRoot
