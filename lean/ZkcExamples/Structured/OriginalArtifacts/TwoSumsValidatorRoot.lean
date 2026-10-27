module

public import ZkcExamples.Structured.OriginalArtifacts.TwoSums
public import ZkcExamples.Structured.Generated.Original.TwoSums
public import ZkcExamples.Structured.Generated.OriginalArtifacts.TwoSumsProducerSource
public import ZkcExamples.Structured.SumcheckArtifacts.ArtifactRoot
public import ZkcExamples.Structured.NormalFormSteps
public import Zkc.Construction.OriginalCorrespondence

public meta import Zkc.Construction.ArtifactBindingTactic
public meta import Zkc.Construction.ProcessViewTactic

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcExamples.Structured.OriginalArtifacts.TwoSumsValidatorRoot
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcExamples.Structured
open ZkcExamples.Structured.SumcheckArtifacts.ArtifactBinding
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

attribute [local irreducible] Zkc.Construction.Original.fold ZkcExamples.Structured.OriginalSumcheckLibrary.reduce Zkc.Construction.Domain.View.loop Zkc.Source.Participant.owned Zkc.Source.Structured.invoke Zkc.Construction.Domain.callHelper
open ZkcExamples.Structured.SumcheckArtifacts.ArtifactRoot
abbrev program := ZkcExamples.Structured.OriginalArtifacts.TwoSums.program
abbrev context := ZkcExamples.Structured.OriginalArtifacts.TwoSums.context
abbrev artifact := ZkcExamples.Structured.OriginalArtifacts.TwoSums.validatorArtifact
abbrev routing := ZkcExamples.Structured.OriginalArtifacts.TwoSums.routing
abbrev RootReturns := ValidatorReturns (F := F) (G := G)
def inputs (input0 : List F) (input1 : List F) (input2 : F) (input3 : F) (input4 : Nat) (history : Domain.History (uniformCarriers F G)) : Domain.Environment (uniformCarriers F G) :=
  [.data (.vector "bls12-381.fr" input0), .data (.vector "bls12-381.fr" input1), .data (.field "bls12-381.fr" input2), .data (.field "bls12-381.fr" input3), .data (.index input4), .transcript context.suite history]

theorem sourceHelper9_identity : ZkcExamples.Structured.Generated.Original.TwoSums.sourceHelper9.helper = ({ name := "zkl_c0a3a2b8b5f989e0e9c138a171631d20dc8bd296769b6ee7636d2d79a8518ba0",   kind := Zkc.Source.Structured.HelperKind.local,   inputs := [Zkc.Source.Structured.Ty.field "bls12-381.fr"],   outputs := [Zkc.Source.Structured.Ty.vector "bls12-381.fr", Zkc.Source.Structured.Ty.field "bls12-381.fr"] }) := by kernel_rfl

theorem sourceHelper37_identity : ZkcExamples.Structured.Generated.Original.TwoSums.sourceHelper37.helper = ({ name := "zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc",   kind := Zkc.Source.Structured.HelperKind.local,   inputs := [Zkc.Source.Structured.Ty.vector "bls12-381.fr",              Zkc.Source.Structured.Ty.vector "bls12-381.fr",              Zkc.Source.Structured.Ty.field "bls12-381.fr"],   outputs := [Zkc.Source.Structured.Ty.boolean] }) := by kernel_rfl

theorem sourceHelper25_identity : ZkcExamples.Structured.Generated.Original.TwoSums.sourceHelper25.helper = ({ name := "s3h7a6b637h626f6f6c65616e4h626f7468",   kind := Zkc.Source.Structured.HelperKind.math,   inputs := [Zkc.Source.Structured.Ty.boolean, Zkc.Source.Structured.Ty.boolean],   outputs := [Zkc.Source.Structured.Ty.boolean] }) := by kernel_rfl

theorem mathHelper25 (left right : Option Bool) :
    invoke (OriginalSumcheckLibrary.helpers (F := F) (G := G) program.payload).components ZkcExamples.Structured.Generated.Original.TwoSums.sourceHelper25.helper (.cons left (.cons right .nil)) =
      .done (.cons (left.bind fun x => right.map fun y => x && y) .nil) := by
  have association : BodyIn program.payload.definitions ZkcExamples.Structured.Generated.Original.TwoSums.sourceHelper25.helper ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs.helper25Body := by bind_structured_bodies
  rw [← (OriginalSumcheckLibrary.helpers_lift program.payload).components, Zkc.Source.Structured.component_body_plain program.payload ZkcExamples.Structured.Generated.Original.TwoSums.sourceHelper25.helper ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs.helper25Body association]
  cases left <;> cases right <;> rfl

theorem mask_outputs (site : String) (point : List F) (scalar : F) :
    (show Values (Component (assignment F G)) SumcheckVerifierBodies.reduceOutputs from
    maskValues ((({} : ProtocolContext).enter site [0, 1]).roles 1)
      ((({} : ProtocolContext).enter site [0, 1]).mapScopes ZkcExamples.Structured.Generated.Original.TwoSums.sourceProtocol0.outputScopes)
      (.cons none (.cons none (.cons none (.cons none (.cons (some point) (.cons (some scalar) .nil))))))) =
      (.cons none (.cons none (.cons none (.cons none (.cons (some point) (.cons (some scalar) .nil)))))) := by kernel_rfl

set_option linter.unusedSimpArgs false in
def validator (input0 : List F) (input1 : List F) (input2 : F) (input3 : F) (input4 : Nat) (handle : Nat)  (history : Domain.History (uniformCarriers F G)) :
    Original.Simulation (RootReturns context 26 22)
      (fun _ frame => Zkc.Construction.ArtifactBinding.Captures (inputs input0 input1 input2 input3 input4 history) frame)
      (Original.participant (ringModel F G) program (routing handle) 1 ((.cons (some input0) (.cons (some input1) (.cons (some input2) (.cons (some input3) (.cons (some input4) (.cons (some handle) .nil))))))) ⟨[], history⟩)
      (Domain.participant (ringModel F G) program context artifact (inputs input0 input1 input2 input3 input4 history)) := by
  let capture0  : Domain.Environment (uniformCarriers F G) := [.data (.vector "bls12-381.fr" input0), .data (.vector "bls12-381.fr" input1), .data (.field "bls12-381.fr" input2), .data (.field "bls12-381.fr" input3), .data (.index input4), .transcript context.suite history, .data (.vector "bls12-381.fr" []), .data (.field "bls12-381.fr" input2), .data (.vector "bls12-381.fr" []), .data (.field "bls12-381.fr" input2)]
  have loopRule0  :=
    (ZkcExamples.Structured.OriginalArtifacts.TwoSums.ValidatorCall0.callback (F := F) (G := G) handle).reduce program ZkcExamples.Structured.OriginalArtifacts.TwoSums.verifier_bodies ZkcExamples.Structured.OriginalArtifacts.TwoSums.claim_bodies (routing handle) ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence0 (by decide +kernel)
      context ZkcExamples.Structured.OriginalArtifacts.TwoSums.ValidatorCall0.outputs 10 4 handle _ (capture0) rfl input4 4 [8, 9, 5] [] input2 history rfl rfl
  have terminalRule0 (point0 : List F) (scalar0 : F) (history0 : Domain.History (uniformCarriers F G)) :=
    terminal (F := F) (G := G) program ZkcExamples.Structured.OriginalArtifacts.TwoSums.helper_bodies (routing handle) ⟨[], history0⟩ 1
      input0 point0 scalar0 [.data (.vector "bls12-381.fr" input0), .data (.vector "bls12-381.fr" input1), .data (.field "bls12-381.fr" input2), .data (.field "bls12-381.fr" input3), .data (.index input4), .transcript context.suite history, .data (.vector "bls12-381.fr" []), .data (.field "bls12-381.fr" input2), .data (.vector "bls12-381.fr" []), .data (.field "bls12-381.fr" input2), .data (.vector "bls12-381.fr" point0), .data (.field "bls12-381.fr" scalar0), .transcript context.suite history0, .data (.vector "bls12-381.fr" point0), .data (.field "bls12-381.fr" scalar0)] [0, 13, 14] rfl
  let capture1 (point0 : List F) (scalar0 : F) (history0 : Domain.History (uniformCarriers F G)) (checked0 : Bool) : Domain.Environment (uniformCarriers F G) := [.data (.vector "bls12-381.fr" input0), .data (.vector "bls12-381.fr" input1), .data (.field "bls12-381.fr" input2), .data (.field "bls12-381.fr" input3), .data (.index input4), .transcript context.suite history, .data (.vector "bls12-381.fr" []), .data (.field "bls12-381.fr" input2), .data (.vector "bls12-381.fr" []), .data (.field "bls12-381.fr" input2), .data (.vector "bls12-381.fr" point0), .data (.field "bls12-381.fr" scalar0), .transcript context.suite history0, .data (.vector "bls12-381.fr" point0), .data (.field "bls12-381.fr" scalar0), .data (.boolean checked0), .data (.vector "bls12-381.fr" []), .data (.field "bls12-381.fr" input3), .data (.vector "bls12-381.fr" []), .data (.field "bls12-381.fr" input3)]
  have loopRule1 (point0 : List F) (scalar0 : F) (history0 : Domain.History (uniformCarriers F G)) (checked0 : Bool) :=
    (ZkcExamples.Structured.OriginalArtifacts.TwoSums.ValidatorCall1.callback (F := F) (G := G) handle).reduce program ZkcExamples.Structured.OriginalArtifacts.TwoSums.verifier_bodies ZkcExamples.Structured.OriginalArtifacts.TwoSums.claim_bodies (routing handle) ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence1 (by decide +kernel)
      context ZkcExamples.Structured.OriginalArtifacts.TwoSums.ValidatorCall1.outputs 20 4 handle _ (capture1 point0 scalar0 history0 checked0) rfl input4 4 [18, 19, 12] [] input3 history0 rfl rfl
  have terminalRule1 (point0 : List F) (scalar0 : F) (history0 : Domain.History (uniformCarriers F G)) (checked0 : Bool) (point1 : List F) (scalar1 : F) (history1 : Domain.History (uniformCarriers F G)) :=
    terminal (F := F) (G := G) program ZkcExamples.Structured.OriginalArtifacts.TwoSums.helper_bodies (routing handle) ⟨[], history1⟩ 1
      input1 point1 scalar1 [.data (.vector "bls12-381.fr" input0), .data (.vector "bls12-381.fr" input1), .data (.field "bls12-381.fr" input2), .data (.field "bls12-381.fr" input3), .data (.index input4), .transcript context.suite history, .data (.vector "bls12-381.fr" []), .data (.field "bls12-381.fr" input2), .data (.vector "bls12-381.fr" []), .data (.field "bls12-381.fr" input2), .data (.vector "bls12-381.fr" point0), .data (.field "bls12-381.fr" scalar0), .transcript context.suite history0, .data (.vector "bls12-381.fr" point0), .data (.field "bls12-381.fr" scalar0), .data (.boolean checked0), .data (.vector "bls12-381.fr" []), .data (.field "bls12-381.fr" input3), .data (.vector "bls12-381.fr" []), .data (.field "bls12-381.fr" input3), .data (.vector "bls12-381.fr" point1), .data (.field "bls12-381.fr" scalar1), .transcript context.suite history1, .data (.vector "bls12-381.fr" point1), .data (.field "bls12-381.fr" scalar1)] [1, 23, 24] rfl
  unfold Original.participant
  rw [ZkcExamples.Structured.Generated.Original.TwoSums.participant_binding]
  rw [ZkcExamples.Structured.Generated.Constructed.TwoSumsValidator.participant_eq]
  unfold_component_bodies [ZkcExamples.Structured.Generated.Constructed.TwoSumsValidator.view]
  derive_artifact_binding [Original.Simulation.bind (loopRule0 ), Original.Simulation.bind (terminalRule0 _ _ _), Original.Simulation.bind (loopRule1 _ _ _ _), Original.Simulation.bind (terminalRule1 _ _ _ _ _ _ _)]
    normalizing (
      try (rename_i source final returned; change ReduceReturns _ _ _ _ at returned; apply Classical.choice; obtain ⟨point, scalar, reached, rfl, rfl⟩ := returned; refine ⟨?_⟩)
      try (rename_i source final returned; change BooleanReturns _ _ _ _ at returned; apply Classical.choice; obtain ⟨value, rfl, rfl⟩ := returned; refine ⟨?_⟩)
      try simp only [ZkcExamples.Structured.Generated.Original.TwoSums.realized, ZkcExamples.Structured.Generated.Original.TwoSums.step0, ZkcExamples.Structured.Generated.Original.TwoSums.step1Realized, ZkcExamples.Structured.Generated.Original.TwoSums.step2, ZkcExamples.Structured.Generated.Original.TwoSums.step3, ZkcExamples.Structured.Generated.Original.TwoSums.step4Realized, ZkcExamples.Structured.Generated.Original.TwoSums.step5, ZkcExamples.Structured.Generated.Original.TwoSums.step6, ZkcExamples.Structured.OriginalSumcheckCalls.realizeCall, sourceHelper9_identity, sourceHelper37_identity, sourceHelper25_identity, SumcheckPendingLaws.pending_owned (F := F) (G := G) program.payload ZkcExamples.Structured.OriginalArtifacts.TwoSums.claim_bodies 1 input2, SumcheckPendingLaws.pending_owned (F := F) (G := G) program.payload ZkcExamples.Structured.OriginalArtifacts.TwoSums.claim_bodies 1 input3, mathHelper25, Values.get, SumcheckVerifierBodies.reduceReturnValues, SumcheckVerifierLaws.embedV, SumcheckRoundNormalForms.verifierState, PIR.Process.bind, PIR.Process.bind_assoc, Original.fold_bind, Zkc.Construction.ArtifactBinding.fold_done]
      try erw [SumcheckPendingLaws.pending_owned (F := F) (G := G) program.payload ZkcExamples.Structured.OriginalArtifacts.TwoSums.claim_bodies 1 input2]
      try erw [SumcheckPendingLaws.pending_owned (F := F) (G := G) program.payload ZkcExamples.Structured.OriginalArtifacts.TwoSums.claim_bodies 1 input3]
      try simp only [PIR.Process.bind, Zkc.Construction.ArtifactBinding.fold_done]
      try normalize_artifact_operations [ZkcExamples.Structured.SumcheckArtifacts.DomainHelpers.pending (F := F) (G := G) program ZkcExamples.Structured.OriginalArtifacts.TwoSums.claim_bodies, ZkcExamples.Structured.SumcheckArtifacts.DomainHelpers.claim_identity (F := F) (G := G) program "zkl_e8df957aab384c1d5416600c13a571512206e97abfbf6e0e9cddac5c84860d07" ZkcExamples.Structured.OriginalArtifacts.TwoSums.claim_bodies.openClaim, ZkcExamples.Structured.SumcheckArtifacts.DomainHelpers.claim_identity (F := F) (G := G) program "zkl_c36a2d2c6bd38573735fb9b90d1a3848c562d2c1f688234e2b669408e9c9eea9" ZkcExamples.Structured.OriginalArtifacts.TwoSums.claim_bodies.atPrefix, boolean_and] unfolding [ZkcExamples.Structured.Generated.Constructed.TwoSumsValidator.inputSorts, ZkcExamples.Structured.Generated.Constructed.TwoSumsValidator.outputSorts, ZkcExamples.Structured.Generated.Constructed.TwoSumsValidator.returned, inputs, capture0, capture1, carried, context, ZkcExamples.Structured.OriginalArtifacts.TwoSums.context]
      change Original.Simulation _ _ _ _)
    solving (first
      | (rename_i source final returned; change ReduceReturns _ _ _ _ at returned; obtain ⟨point, scalar, reached, sourceEq, frameEq⟩ := returned; rw [frameEq]; rfl)
      | (rename_i source final returned; change BooleanReturns _ _ _ _ at returned; obtain ⟨value, sourceEq, frameEq⟩ := returned; rw [frameEq]; rfl)
      | rfl
      | (intro process frame equation; subst frame; rfl)
      | (intro process frame retained; apply Zkc.Construction.ArtifactBinding.captures_trans (inner := retained); rfl)
      | (unfold RootReturns ValidatorReturns; exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩))

end ZkcExamples.Structured.OriginalArtifacts.TwoSumsValidatorRoot
