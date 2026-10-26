module

public import ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Sources
public import ZkcSecurity.Examples.Generated.Components.SmallSumcheckABI
public import ZkcSecurity.FiatShamir.LosslessPresentationClaims

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Installation
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcExamples.Structured
open ZkcSecurity.FiatShamir ZkcSecurity.Families.Sumcheck TableComponent
open ZkcSecurity.Realizations.Sumcheck
open ZkcSecurity.Realizations.Sumcheck.OriginalRaw
open ZkcSecurity.Realizations.Sumcheck.OriginalRoot
open ZkcSecurity.Examples.Generated.SmallSumcheck
open ZkcSecurity.Examples.Generated.Components.SmallSumcheckABI
abbrev Scalar := ZMod blsModulus
abbrev Group := ZMod blsModulus
abbrev carriers := uniformCarriers Scalar Group
abbrev Statement := validatorArtifacts.Statement model

def publicInputs (input0 : List Scalar) (input1 : Scalar) (input2 : Nat) : Domain.Environment carriers := [.data (.vector ("bls12-381.fr") input0), .data (.field ("bls12-381.fr") input1), .data (.index input2)]

theorem public_input_association (input0 : List Scalar) (input1 : Scalar) (input2 : Nat) : publicInputs input0 input1 input2 =
    (Domain.encodeValues (statement input0 input1 input2)).getD [] := by kernel_rfl

theorem validator_returned : ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheckValidatorRoot.artifact.returned = [8, 7] := by kernel_rfl

theorem selected_program : validatorCompiled.imported.program = ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.program :=
  Zkc.Verification.Imported.unique _ _
theorem selected_context : validatorCompiled.selection.context = ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.context := by decide +kernel
theorem selected_artifact : validatorArtifacts.participant = ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheckValidatorRoot.artifact := by kernel_rfl

def sourceInputs (input0 : List Scalar) (input1 : Scalar) (input2 : Nat) (history : Domain.History carriers) :=
  Original.participant (ringModel Scalar Group) ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.program (ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.routing 0) 1 (.cons (some input0) (.cons (some input1) (.cons (some input2) (.cons (some 0) .nil)))) ⟨[], history⟩
abbrev presentedInputs := ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Sources.presented (F := Scalar) (G := Group)

def bridgeInputs (input0 : List Scalar) (input1 : Scalar) (input2 : Nat) (history : Domain.History carriers) :
    Original.Bridge (Nominal.interface (G := Group) "bls12-381.fr") closedPost history
      (sourceInputs input0 input1 input2 history)
      (Domain.participant model validatorCompiled.imported.program validatorCompiled.selection.context
        validatorArtifacts.participant (publicInputs input0 input1 input2 ++ [.transcript validatorCompiled.selection.context.suite history]))
      (presentedInputs input0 input1 input2 history)
      (ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheckValidatorRoot.RootReturns ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.context 8 7)
      (fun _ frame => Zkc.Construction.ArtifactBinding.Captures (ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheckValidatorRoot.inputs input0 input1 input2 history) frame) := by
  rw [selected_context, selected_artifact, selected_program]
  exact ⟨ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Sources.bridge input0 input1 input2 0 history, ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheckValidatorRoot.validator input0 input1 input2 0 history⟩

def source (statement : Statement) :=
  TypedABI.apply (Value := model.Value) (types := validatorArtifacts.publics) sourceInputs statement
def presented (statement : Statement) :=
  TypedABI.apply (Value := model.Value) (types := validatorArtifacts.publics) presentedInputs statement

def installation : Original.Claims.Installation validatorSubject where
  result := Result (F := Scalar) (G := Group)
  signature := Nominal.signature Scalar "bls12-381.fr"
  absorb := Nominal.interface (G := Group) "bls12-381.fr"
  inputs statement := (Domain.encodeValues statement).getD []
  encoded statement := Domain.encodeValues_getD statement (by rfl)
  source := source
  presented := presented
  Post := closedPost
  returns := ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheckValidatorRoot.RootReturns ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.context 8 7
  live statement history _ frame := Zkc.Construction.ArtifactBinding.Captures
    ((Domain.encodeValues statement).getD [] ++ [.transcript validatorCompiled.selection.context.suite history]) frame
  acceptance := acceptance
  bridge := by bind_subject_abi using bridgeInputs
  agrees := root_acceptance validatorCompiled ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.context 8 7 rfl

end ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Installation
