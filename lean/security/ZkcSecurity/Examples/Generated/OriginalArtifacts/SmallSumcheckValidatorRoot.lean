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
set_option linter.unusedSimpArgs false
noncomputable section
namespace ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheckValidatorRoot
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcExamples.Structured
open ZkcSecurity.Realizations.Sumcheck.ArtifactBinding
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

attribute [local irreducible] Zkc.Construction.Original.fold ZkcExamples.Structured.OriginalSumcheckLibrary.reduce Zkc.Construction.Domain.View.loop Zkc.Source.Participant.owned Zkc.Source.Structured.invoke Zkc.Construction.Domain.callHelper
open ZkcSecurity.Realizations.Sumcheck.ArtifactRoot
abbrev program := ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.program
abbrev context := ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.context
abbrev artifact := ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.validatorArtifact
abbrev routing := ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.routing
abbrev RootReturns := ValidatorReturns (F := F) (G := G)
def inputs (input0 : List F) (input1 : F) (input2 : Nat) (history : Domain.History (uniformCarriers F G)) : Domain.Environment (uniformCarriers F G) :=
  [.data (.vector "bls12-381.fr" input0), .data (.field "bls12-381.fr" input1), .data (.index input2), .transcript context.suite history]

theorem sourceHelper26_identity : ZkcExamples.Structured.Generated.Original.SmallSumcheck.sourceHelper26.helper = ({ name := "zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc",   kind := Zkc.Source.Structured.HelperKind.local,   inputs := [Zkc.Source.Structured.Ty.vector "bls12-381.fr",              Zkc.Source.Structured.Ty.vector "bls12-381.fr",              Zkc.Source.Structured.Ty.field "bls12-381.fr"],   outputs := [Zkc.Source.Structured.Ty.boolean] }) := by kernel_rfl

theorem mask_outputs (site : String) (point : List F) (scalar : F) :
    (show Values (Component (assignment F G)) SumcheckVerifierBodies.reduceOutputs from
    maskValues ((({} : ProtocolContext).enter site [0, 1]).roles 1)
      ((({} : ProtocolContext).enter site [0, 1]).mapScopes ZkcExamples.Structured.Generated.Original.SmallSumcheck.sourceProtocol0.outputScopes)
      (.cons none (.cons none (.cons none (.cons none (.cons (some point) (.cons (some scalar) .nil))))))) =
      (.cons none (.cons none (.cons none (.cons none (.cons (some point) (.cons (some scalar) .nil)))))) := by kernel_rfl

def validator (input0 : List F) (input1 : F) (input2 : Nat) (handle : Nat)  (history : Domain.History (uniformCarriers F G)) :
    Original.Simulation (RootReturns context 8 7)
      (fun _ frame => Zkc.Construction.ArtifactBinding.Captures (inputs input0 input1 input2 history) frame)
      (Original.participant (ringModel F G) program (routing handle) 1 ((.cons (some input0) (.cons (some input1) (.cons (some input2) (.cons (some handle) .nil))))) ⟨[], history⟩)
      (Domain.participant (ringModel F G) program context artifact (inputs input0 input1 input2 history)) := by
  let capture0  : Domain.Environment (uniformCarriers F G) := [.data (.vector "bls12-381.fr" input0), .data (.field "bls12-381.fr" input1), .data (.index input2), .transcript context.suite history, .data (.vector "bls12-381.fr" [])]
  have loopRule0  :=
    (ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.ValidatorCall0.callback (F := F) (G := G) handle).reduce program ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.verifier_bodies (routing handle) ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.occurrence0 (by decide +kernel)
      context ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.ValidatorCall0.outputs 5 2 handle _ (capture0) rfl input2 2 [4, 1, 3] input1 history rfl rfl
  have terminalRule0 (point0 : List F) (scalar0 : F) (history0 : Domain.History (uniformCarriers F G)) :=
    terminal (F := F) (G := G) program ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.helper_bodies (routing handle) ⟨[], history0⟩ 1
      input0 point0 scalar0 [.data (.vector "bls12-381.fr" input0), .data (.field "bls12-381.fr" input1), .data (.index input2), .transcript context.suite history, .data (.vector "bls12-381.fr" []), .data (.vector "bls12-381.fr" point0), .data (.field "bls12-381.fr" scalar0), .transcript context.suite history0] [0, 5, 6] rfl
  unfold Original.participant
  rw [ZkcExamples.Structured.Generated.Original.SmallSumcheck.participant_binding]
  rw [ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.participant_eq]
  unfold_component_bodies [ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.view]
  derive_artifact_binding [Original.Simulation.bind (loopRule0 ), finish (terminalRule0 _ _ _)]
    normalizing (
      try (rename_i source final returned; change ReduceReturns _ _ _ _ at returned; apply Classical.choice; obtain ⟨point, scalar, reached, rfl, rfl⟩ := returned; refine ⟨?_⟩)
      try (rename_i source final returned; change BooleanReturns _ _ _ _ at returned; apply Classical.choice; obtain ⟨value, rfl, rfl⟩ := returned; refine ⟨?_⟩)
      try simp only [ZkcExamples.Structured.Generated.Original.SmallSumcheck.realized, ZkcExamples.Structured.Generated.Original.SmallSumcheck.step0, ZkcExamples.Structured.Generated.Original.SmallSumcheck.step0Realized, ZkcExamples.Structured.Generated.Original.SmallSumcheck.step1, sourceHelper26_identity, ZkcExamples.Structured.OriginalSumcheckProducerCalls.realizeProducerCall, ZkcExamples.Structured.OriginalSumcheckCalls.realizeCall, mask_outputs, Values.get, Values.present, SumcheckVerifierBodies.reduceReturnValues, SumcheckVerifierLaws.embedV, SumcheckRoundNormalForms.verifierState, Original.fold_bind, Zkc.Construction.ArtifactBinding.fold_done, PIR.Process.bind, PIR.Process.bind_assoc]
      try normalize_artifact_operations [ZkcSecurity.Realizations.Sumcheck.DomainHelpers.empty program ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.helper_bodies.sumcheck, boolean_and] unfolding [ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.inputSorts, ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.outputSorts, ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.returned, inputs, capture0, carried, context, ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.context]
      try simp only [Nat.lt_irrefl, decide_false, Nat.sub_self, List.cons_append, List.nil_append, List.getElem?_cons_zero, List.getElem?_cons_succ, PIR.Process.bind, PIR.Process.bind_assoc]
      try dsimp only
      change Original.Simulation _ _ _ _)
    solving (first
      | (rename_i source final returned; change ReduceReturns _ _ _ _ at returned; obtain ⟨point, scalar, reached, sourceEq, frameEq⟩ := returned; rw [frameEq]; simp [Zkc.Construction.ArtifactBinding.Captures, inputs, capture0, carried, context, ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.context, List.append_assoc, List.take_append])
      | (rename_i source final returned; change BooleanReturns _ _ _ _ at returned; obtain ⟨value, sourceEq, frameEq⟩ := returned; rw [frameEq]; simp [Zkc.Construction.ArtifactBinding.Captures, inputs, capture0, carried, context, ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.context, List.append_assoc, List.take_append])
      | rfl
      | solve | simp_all [Zkc.Construction.ArtifactBinding.Captures, inputs, capture0, carried, context, ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.context, List.append_assoc, List.take_append]
      | (intro process frame retained; apply Zkc.Construction.ArtifactBinding.captures_trans (inner := retained); simp [Zkc.Construction.ArtifactBinding.Captures, inputs, capture0, carried, context, ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.context, List.append_assoc, List.take_append])
      | (unfold RootReturns ValidatorReturns; refine ⟨_, rfl, ?_⟩; simp [inputs, capture0, carried, context, ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.context, List.cons_append, List.nil_append]))

end ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheckValidatorRoot
