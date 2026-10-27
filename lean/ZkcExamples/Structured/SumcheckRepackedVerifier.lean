module

public import ZkcExamples.Structured.SumcheckRepackedViews
public import ZkcExamples.Structured.SumcheckReduceVerifier
public import ZkcExamples.Structured.SumcheckRepackedNormalForms

@[expose] public section

/-! Plain verifier equations for the complete repacked Reduction unit. The
child Reduce, its helpers and the repeat laws are the retained Reduction's;
only the root's input masks, operand positions and return order are new. The
root's participant normal form is `SumcheckRepackedNormalForms`. -/
namespace ZkcExamples.Structured.SumcheckRepackedVerifier
open Zkc.Source Zkc.Source.Structured
open SumcheckRepackedViews SumcheckRepackedBodies

/-- The repacked unit has exactly the retained Reduction's helper list. -/
theorem helperBodies : SumcheckVerifierHelpers.Bodies unit.definitions :=
  SumcheckReduceVerifier.helperBodies

/-- Exact consuming and constructing bodies; discharged within the source package. -/
theorem claimBodies : SumcheckPendingLaws.Bodies unit.definitions :=
  SumcheckReduceVerifier.claimBodies

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

open SumcheckVerifierHelpers SumcheckVerifierPrelude

/-- Full signature, member and raw tree select the same child in this table. -/
theorem reduce_invoke_plain (ctx : ProtocolContext) (self : Nat)
    (arguments : Values (Component (assignment F G)) SumcheckVerifierBodies.reduceInputs) :
    invokeProtocol (unit.plainProtocolTable F G) SumcheckReduceBodies.reduceSignature
      ctx self arguments = reduceDenote SumcheckRepackedNormalForms.reduceMaximum unit ctx self arguments :=
  SumcheckRepackedNormalForms.reduce_view ctx self arguments _ rfl

/-- Inputs in the repacked order: claim, rounds, variables, values, challenges. -/
def rootInputs (claim : Option F) (count dimension : Option Nat) (xs : Option (List F))
    (service : Option Nat) : Values (Component (assignment F G)) runSignature.inputs :=
  .cons claim (.cons count (.cons dimension (.cons xs (.cons service .nil))))

/-- Outputs in the repacked order: V's point and value first, then P's values. -/
def rootResults (pc : Option (List F) × Option F) :
    Values (Component (assignment F G)) runSignature.outputs :=
  .cons pc.1 (.cons pc.2 (.cons none (.cons none .nil)))

theorem verifier_context_optional (ctx : ProtocolContext) (self : Nat)
    (verifier : self = ctx.roles 1) (separate : ctx.roles 0 ≠ self)
    (claim : Option F) (count dimension : Option Nat) (xs : Option (List F))
    (service : Option Nat) :
    invokeProtocol (unit.plainProtocolTable F G) runSignature
      ctx self (rootInputs claim count dimension xs service) =
      (admittedRounds SumcheckRepackedNormalForms.reduceMaximum (ctx.enter "s5" [0, 1]) count service claim).bind
        (fun pc => .done (rootResults pc)) := by
  refine (SumcheckRepackedNormalForms.verifier_invoke (bodies := helperBodies) (claims := claimBodies) (ctx := ctx)
    (self := self) (role := verifier) (separate := separate) (claim := claim) (count := count)
    (dimension := dimension) (raw := xs) (service := service)).trans ?_
  subst self
  unfold SumcheckRepackedNormalForms.verifierProcess
  rw [SumcheckPendingLaws.pending_plain_owned unit claimBodies]
  cases claim with
  | none => rfl
  | some claim =>
    simp only [PIR.Process.bind]
    rw [verifierReduce_rounds unit helperBodies (SumcheckRepackedNormalForms.reduceContext ctx) separate]
    simp only [PIR.Process.bind_assoc, PIR.Process.bind]
    rfl

/-- The repacked root skips P's table construction, calls the same Reduce at
s5 and returns V's point and value in its own first two positions. -/
theorem root_context_expansion (ctx : ProtocolContext) (self : Nat)
    (verifier : self = ctx.roles 1) (separate : ctx.roles 0 ≠ self)
    (claim : Option F) (count dimension : Option Nat) (xs : Option (List F))
    (service : Option Nat) :
    invokeProtocol (unit.plainProtocolTable F G) runSignature
      ctx self (rootInputs claim count dimension xs service) =
      (invokeProtocol (unit.plainProtocolTable F G) SumcheckReduceBodies.reduceSignature
        (ctx.enter "s5" [0, 1]) self
        (reduceArguments none none none (some []) claim count service)).bind
        (fun result => .done (rootResults
          (result.get (.there (.there (.there (.there .here)))),
            result.get (.there (.there (.there (.there (.there .here)))))))) := by
  rw [verifier_context_optional ctx self verifier separate,
    reduce_invoke_plain (ctx.enter "s5" [0, 1]) self (reduceArguments none none none (some []) claim count service),
    reduce_optional unit helperBodies claimBodies (ctx.enter "s5" [0, 1]) self verifier separate
      SumcheckRepackedNormalForms.reduceMaximum none none none (some []) claim count service]
  refine Eq.trans ?_ (PIR.Process.bind_assoc _ _ _).symm
  rfl

/-- The actual complete repacked participant V. -/
theorem verifier_optional (claim : Option F) (count dimension : Option Nat)
    (xs : Option (List F)) (service : Option Nat) :
    program.participant F G 1 (rootInputs claim count dimension xs service) =
      (admittedRounds SumcheckRepackedNormalForms.reduceMaximum (ProtocolContext.enter {} "s5" [0, 1]) count service claim).bind
        (fun pc => .done (rootResults pc)) :=
  (unit.protocolTable_forgetSites (F := F) (G := G)
    runSignature {} 1 (rootInputs claim count dimension xs service)).trans
    (verifier_context_optional {} 1 rfl (by decide) claim count dimension xs service)

theorem verifier_excess (claim : F) (count : Nat) (large : SumcheckRepackedNormalForms.reduceMaximum < count)
    (dimension : Option Nat) (xs : Option (List F)) (service : Option Nat) :
    program.participant F G 1 (rootInputs (some claim) (some count) dimension xs service) =
      .halt .refused := by
  refine (verifier_optional (some claim) (some count) dimension xs service).trans ?_
  rw [admittedRounds_excess SumcheckRepackedNormalForms.reduceMaximum count _ large]
  rfl

/-- Process-level repacking: the repacked participant is the retained one with
inputs read in the retained order and outputs returned in the repacked order. -/
theorem participant_repacked (claim : Option F) (count dimension : Option Nat)
    (xs : Option (List F)) (service : Option Nat) :
    program.participant F G 1 (rootInputs claim count dimension xs service) =
      (SumcheckReduceViews.program.participant F G 1
        (SumcheckReduceVerifier.reduceRootInputs xs dimension claim count service)).bind
        (fun outputs => .done (rootResults
          (outputs.get (.there (.there .here)), outputs.get (.there (.there (.there .here)))))) := by
  rw [verifier_optional, SumcheckReduceVerifier.verifier_optional]
  refine Eq.trans ?_ (PIR.Process.bind_assoc _ _ _).symm
  rfl

end ZkcExamples.Structured.SumcheckRepackedVerifier
