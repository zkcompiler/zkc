module

public import ZkcExamples.Structured.SumcheckReduceAssociations
public import ZkcExamples.Structured.SumcheckVerifierBodies
public import ZkcExamples.Structured.SumcheckVerifierHelpers
public import ZkcExamples.Structured.SumcheckVerifierPrelude
public import ZkcExamples.Structured.SumcheckReductionNormalForms

@[expose] public section

/-! Plain verifier equations for the complete original Reduction source unit. The
root's participant normal form, with the generated normal form of the applied
`Reduce` body substituted at its application, is
`SumcheckReductionNormalForms`; the equations below admit the repeat. -/
namespace ZkcExamples.Structured.SumcheckReduceVerifier
open Zkc.Source Zkc.Source.Structured
open SumcheckReduceViews

/-- Every dependency is a complete body in this source's own definition list. -/
theorem helperBodies : SumcheckVerifierHelpers.Bodies unit.definitions where
  empty := SumcheckReduceAssociations.empty_association
  append := SumcheckReduceAssociations.append_association
  width := SumcheckReduceAssociations.width_association
  «variables» := SumcheckReduceAssociations.variables_association
  values := SumcheckReduceAssociations.values_association

/-- Complete body association at the unit's own maximum, including the nested callback and suffix. -/
theorem reduce_raw_shared :
    reduceDefinition.raw = (SumcheckVerifierBodies.reduceBody SumcheckReductionNormalForms.reduceMaximum).erase := by
  refine SumcheckReduceViews.reduce_raw.trans ?_
  unfold SumcheckVerifierBodies.reduceBody SumcheckVerifierBodies.roundBody
    SumcheckVerifierBodies.reduceReturn
  rfl

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

open SumcheckVerifierHelpers SumcheckVerifierPrelude

/-- Full signature, member and raw tree select the child in the actual plain table. -/
theorem reduce_invoke_plain (ctx : ProtocolContext) (self : Nat)
    (arguments : Values (Component (assignment F G)) SumcheckVerifierBodies.reduceInputs) :
    invokeProtocol (unit.plainProtocolTable F G) SumcheckReduceBodies.reduceSignature
      ctx self arguments = reduceDenote SumcheckReductionNormalForms.reduceMaximum unit ctx self arguments :=
  SumcheckReductionNormalForms.reduce_view ctx self arguments _ rfl

def reduceRootInputs (xs : Option (List F)) (dimension : Option Nat)
    (claim : Option F) (count service : Option Nat) :
    Values (Component (assignment F G)) SumcheckReduceBodies.runSignature.inputs :=
  .cons xs (.cons dimension (.cons claim (.cons count (.cons service .nil))))

def reduceRootResults (pc : Option (List F) × Option F) :
    Values (Component (assignment F G)) SumcheckReduceBodies.runSignature.outputs :=
  .cons none (.cons none (.cons pc.1 (.cons pc.2 .nil)))

/-- Contextual equation for the complete imported Reduction root. The child
uses the real s3 application prefix and the caller's mapped participant roles. -/
theorem verifier_context_optional (ctx : ProtocolContext) (self : Nat)
    (verifier : self = ctx.roles 1) (separate : ctx.roles 0 ≠ self)
    (xs : Option (List F)) (dimension : Option Nat) (claim : Option F)
    (count service : Option Nat) :
    invokeProtocol (unit.plainProtocolTable F G) SumcheckReduceBodies.runSignature
      ctx self (reduceRootInputs xs dimension claim count service) =
      (admittedRounds SumcheckReductionNormalForms.reduceMaximum (ctx.enter "s3" [0, 1]) count service claim).bind
        (fun pc => .done (reduceRootResults pc)) := by
  refine (SumcheckReductionNormalForms.verifier_invoke (bodies := helperBodies) (ctx := ctx)
    (self := self) (role := verifier) (separate := separate) (raw := xs) (dimension := dimension)
    (claim := claim) (count := count) (service := service)).trans ?_
  subst self
  unfold SumcheckReductionNormalForms.verifierProcess
  rw [verifierReduce_rounds unit helperBodies (SumcheckReductionNormalForms.reduceContext ctx) separate]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind]
  rfl

/-- The actual root skips tableP construction, calls Reduce at s3, and selects
its original verifier outputs using the exact optional Math projection. -/
theorem root_context_expansion (ctx : ProtocolContext) (self : Nat)
    (verifier : self = ctx.roles 1) (separate : ctx.roles 0 ≠ self)
    (xs : Option (List F)) (dimension : Option Nat) (claim : Option F)
    (count service : Option Nat) :
    invokeProtocol (unit.plainProtocolTable F G) SumcheckReduceBodies.runSignature
      ctx self (reduceRootInputs xs dimension claim count service) =
      (invokeProtocol (unit.plainProtocolTable F G) SumcheckReduceBodies.reduceSignature
        (ctx.enter "s3" [0, 1]) self
        (reduceArguments none none none claim count service)).bind
        (fun result => .done (reduceRootResults
          (result.get (.there (.there (.there (.there .here)))),
            result.get (.there (.there (.there (.there (.there .here)))))))) := by
  rw [verifier_context_optional ctx self verifier separate,
    reduce_invoke_plain (ctx.enter "s3" [0, 1]) self (reduceArguments none none none claim count service),
    reduce_optional unit helperBodies (ctx.enter "s3" [0, 1]) self verifier separate
      SumcheckReductionNormalForms.reduceMaximum none none none claim count service]
  refine Eq.trans ?_ (PIR.Process.bind_assoc _ _ _).symm
  rfl

/-- The actual complete source participant, including original root input and
output masks and the original child selected in its full protocol table. -/
theorem verifier_optional (xs : Option (List F)) (dimension : Option Nat)
    (claim : Option F) (count service : Option Nat) :
    program.participant F G 1 (reduceRootInputs xs dimension claim count service) =
      (admittedRounds SumcheckReductionNormalForms.reduceMaximum (ProtocolContext.enter {} "s3" [0, 1]) count service claim).bind
        (fun pc => .done (reduceRootResults pc)) :=
  (unit.protocolTable_forgetSites (F := F) (G := G)
    SumcheckReduceBodies.runSignature {} 1 (reduceRootInputs xs dimension claim count service)).trans
    (verifier_context_optional {} 1 rfl (by decide) xs dimension claim count service)

/-- Missing root count is incomplete even if the other arguments are present. -/
theorem verifier_missing (xs : Option (List F)) (dimension : Option Nat)
    (claim : Option F) (service : Option Nat) :
    program.participant F G 1 (reduceRootInputs xs dimension claim none service) =
      .halt .incomplete :=
  (verifier_optional xs dimension claim none service).trans rfl

/-- Counts above the unit's own maximum are refused before any callback. -/
theorem verifier_excess (xs : Option (List F)) (dimension : Option Nat)
    (claim : Option F) (count : Nat) (large : SumcheckReductionNormalForms.reduceMaximum < count) (service : Option Nat) :
    program.participant F G 1 (reduceRootInputs xs dimension claim (some count) service) =
      .halt .refused := by
  refine (verifier_optional xs dimension claim (some count) service).trans ?_
  rw [admittedRounds_excess SumcheckReductionNormalForms.reduceMaximum count _ large]
  rfl

/-- With zero rounds, the actual root returns emptyV and the unchanged optional
claim, including absent claim or absent service. -/
theorem verifier_zero (xs : Option (List F)) (dimension : Option Nat)
    (claim : Option F) (service : Option Nat) :
    program.participant F G 1 (reduceRootInputs xs dimension claim (some 0) service) =
      .done (reduceRootResults (some [], claim)) := by
  refine (verifier_optional xs dimension claim (some 0) service).trans ?_
  rw [admittedRounds_zero]
  rfl

/-- A distinct caller mapping and nonempty prefix retain the same real root. -/
theorem verifier_permuted_optional (xs : Option (List F)) (dimension : Option Nat)
    (claim : Option F) (count service : Option Nat) :
    invokeProtocol (unit.plainProtocolTable F G) SumcheckReduceBodies.runSignature
      ⟨some "outer", roleSubstitution [2, 0]⟩ 0
      (reduceRootInputs xs dimension claim count service) =
      (admittedRounds SumcheckReductionNormalForms.reduceMaximum
        (ProtocolContext.enter ⟨some "outer", roleSubstitution [2, 0]⟩ "s3" [0, 1])
        count service claim).bind (fun pc => .done (reduceRootResults pc)) :=
  verifier_context_optional _ 0 rfl (by decide) xs dimension claim count service

/-- Successful execution of the actual complete root returns exactly one point
entry per admitted round. Zero preserves the optional claim; a positive return
has a present claim. Every interaction reply and phase remains quantified. -/
theorem verifier_returns (P : PIR.Interaction (participantInterface F G))
    (xs : Option (List F)) (dimension : Option Nat) (claim : Option F)
    (count : Nat) (bounded : count ≤ SumcheckReductionNormalForms.reduceMaximum) (service : Option Nat) (phase : P.Phase) :
    PIR.Boundary.Returns P (fun result _ =>
      ∃ point current, result = reduceRootResults (G := G) (some point, current) ∧
        point.length = count ∧ (count = 0 → current = claim) ∧
        (0 < count → current.isSome = true))
      (program.participant F G 1 (reduceRootInputs xs dimension claim (some count) service))
      phase := by
  rw [verifier_optional]
  simp only [admittedRounds, bounded, ↓reduceIte]
  apply PIR.Boundary.returns_bind P _ _
    (fun result _ => ∃ point, result.1 = some point ∧ point.length = count ∧
      (count = 0 → result.2 = claim) ∧ (0 < count → result.2.isSome = true))
  · simpa only [List.length_nil, Nat.zero_add] using
      (SumcheckVerifierLaws.repeat_returns P (ProtocolContext.enter {} "s3" [0, 1])
        service count [] claim phase)
  · intro result nextPhase returned
    obtain ⟨point, present, length, zeroClaim, positiveClaim⟩ := returned
    exact ⟨point, result.2, congrArg (reduceRootResults (G := G)) (Prod.ext present rfl),
      length, zeroClaim, positiveClaim⟩

end ZkcExamples.Structured.SumcheckReduceVerifier
