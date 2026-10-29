import ZkcSecurity.Examples.RootProperties.SmallSumcheck.Soundness
import ZkcSecurity.Examples.RootProperties.TwoSums.Soundness
import TestsSecurity.DomainCharges

/-! Current source-family contracts, independently of canonical claim printing. -/
set_option autoImplicit false
noncomputable section
namespace TestsSecurity.OriginalSecurityFamily
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Examples.RootProperties
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Realizations.Sumcheck

example : SmallSumcheck.Soundness.budget = 2 := rfl
example : TwoSums.Soundness.budget = 8 := rfl
example : TestsSecurity.DomainCharges.leftOrigin ≠ TestsSecurity.DomainCharges.rightOrigin := by decide +kernel

/-- Both roles select the exact same checked reduction declaration and body. -/
example (selection : ZkcExamples.Structured.SumcheckSourceSelections.Selection) :
    (SourceRootReference.reductionAssociation selection).definition.raw =
      (ZkcExamples.Structured.SumcheckVerifierBodies.reduceBody
        (ZkcExamples.Structured.SumcheckSourceSelections.maximum selection)).erase :=
  (SourceRootReference.reductionAssociation selection).body_eq

/-! The zero-round regression is about the actual admitted source. Its exact
terminal equation retains the arbitrary incoming construction state, with
explicit overflow and no shape or claim-truth premise. -/
open ZkcExamples.Structured SumcheckSourceSelections TableComponent
section ZeroRounds
variable (model : DomainModel) [fieldLaw : Fact (IsField (model.Field field))]
local instance : Field (model.Field field) := fieldLaw.out.toField

def terminalZero (selection : Selection) (raw : List (model.Field field)) (scalar : model.Field field) :=
 SourceIteration.terminalCheck model selection raw
  (SumcheckVerifierBodies.reduceReturnValues (SumcheckReferenceInstallation.state model (some []) (some scalar)))

theorem zero_round_source (selection : Selection) (site : String) (raw : List (model.Field field))
    (scalar : model.Field field) (handle : Nat) :
    SourceRootReference.one model selection {} site (some raw) (some scalar) (some 0) (some handle) =
      terminalZero model selection raw scalar := by
  rw [SourceIteration.one_reduction_with_original model selection site raw [0] 0 handle scalar () (by rfl)]
  rw [SourceIteration.reduction_equation model _ (source selection).payload.linked
    (roundBodies selection) (Occurrence.table model (source selection).payload)
    (ProtocolContext.enter {} site [0,1]) (SourceRootProperties.context_distinct site) handle
    (SumcheckReductionReference.actual_bodies model selection) (maximum selection) 0 (by omega)]
  rfl

example (routing : Original.Routing) (selection : Selection) (site : String)
    (raw : List (model.Field field)) (scalar : model.Field field) (handle : Nat)
    (state : Original.State model.toCarriers) :
    Original.fold routing
      (SourceRootReference.one model selection {} site (some raw) (some scalar) (some 0) (some handle)) state =
      Original.fold routing (terminalZero model selection raw scalar) state := by rw [zero_round_source]

example (routing : Original.Routing) (selection : Selection) (site : String)
    (raw : List (model.Field field)) (scalar : model.Field field) (handle : Nat)
    (state : Original.State model.toCarriers) :
    Original.fold routing
      (SourceRootReference.one model selection {} site (some raw) (some scalar) (some 0) (some handle)) state =
      if raw.length < indexLimit then .done (some (decide
        (ReferenceLibrary.Multilinear.Admission.HasShape raw 0 1 ∧ raw.sum = scalar)), state)
      else .halt .exhausted := by
  rw [zero_round_source]
  have eqn := SourceRootBounds.terminal_equation model selection raw
    (PrefixState.initial [0] 0 scalar () (by rfl)) (by change (0 : Nat) < 64; decide)
  change terminalZero model selection raw scalar = _ at eqn
  rw [eqn]
  split <;> rfl

#print axioms zero_round_source
end ZeroRounds

#print axioms SourceIteration.frame_contract
#print axioms SourceIteration.no_contract
#print axioms SourcePair.reduction
#print axioms SourcePublicInstallations.small_no
#print axioms SourcePublicInstallations.two_no
#print axioms SmallSumcheck.Soundness.rejected
#print axioms SmallSumcheck.Soundness.costs
#print axioms TwoSums.Soundness.rejected
#print axioms TwoSums.Soundness.costs
end TestsSecurity.OriginalSecurityFamily
