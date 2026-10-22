module

public import ZkcExamples.Structured.SumcheckProverPrelude
public import ZkcExamples.Structured.SumcheckSourceVerifier
public import ZkcExamples.Structured.SumcheckSourceContracts
public import ZkcExamples.Structured.SumcheckReduceVerifier
public import ZkcExamples.Structured.SumcheckReduceContracts

@[expose] public section

/-! Plain prover equations of both complete original roots: the actual table
constructor, the child Reduce at the prover and, for Source, the skipped
verifier terminal. The verifier's inputs are absent at the prover. The roots'
participant normal forms, with the generated normal form of `Reduce`
substituted at the application, are `SumcheckSourceNormalForms` and
`SumcheckReductionNormalForms`; the equations below admit the repeat. -/
namespace ZkcExamples.Structured.SumcheckProverRoots
open Zkc.Source Zkc.Source.Structured PrimitiveLibrary
open SumcheckVerifierPrelude SumcheckVerifierHelpers SumcheckProverLaws SumcheckProverPrelude
open Zkc.Polynomial.Multilinear (restrictPrefixValues)

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-! ### Complete Source root -/

section Source
open SumcheckSourceViews

/-- The complete Source root at the prover in an arbitrary caller context: the
checked table, the actual Reduce at the unit's own maximum on the prover's state, and no
terminal. -/
theorem source_context_prover (ctx : ProtocolContext) (self : Nat)
    (prover : self = ctx.roles 0) (separate : ctx.roles 1 ≠ self)
    (raw : List F) (rounds : Nat) (shape : HasShape raw rounds 1)
    (bound : raw.length < indexLimit) (admitted : rounds ≤ SumcheckSourceNormalForms.reduceMaximum)
    (claim : Option F) (service : Option Nat) :
    invokeProtocol (unit.plainProtocolTable F G) SumcheckSourceBodies.runSignature ctx self
      (SumcheckSourceVerifier.sourceRootInputs (some raw) claim (some rounds) service) =
      (PIR.repeatN rounds (roundHonest (ctx.enter "label_726564756365" [0, 1]) raw rounds) []).bind
        (fun _ => .done (.cons none .nil)) := by
  refine (SumcheckSourceNormalForms.prover_invoke (bodies := SumcheckSourceContracts.bodies)
    (ctx := ctx) (self := self) (role := prover) (separate := separate) (raw := raw)
    (rounds := rounds) (claim := claim) (service := service) (shape := shape)
    (bound := bound)).trans ?_
  subst self
  unfold SumcheckSourceNormalForms.proverProcess
  rw [proverReduce_honest unit SumcheckSourceContracts.bodies
    (SumcheckSourceNormalForms.reduceContext ctx) separate SumcheckSourceNormalForms.reduceMaximum raw rounds shape bound
    rounds admitted]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind]

/-- The complete Source root at the prover. -/
theorem source_prover (raw : List F) (rounds : Nat) (shape : HasShape raw rounds 1)
    (bound : raw.length < indexLimit) (admitted : rounds ≤ SumcheckSourceNormalForms.reduceMaximum)
    (claim : Option F) (service : Option Nat) :
    program.participant F G 0
      (SumcheckSourceVerifier.sourceRootInputs (some raw) claim (some rounds) service) =
      (PIR.repeatN rounds (roundHonest SumcheckSourceVerifier.childContext raw rounds) []).bind
        (fun _ => .done (.cons none .nil)) :=
  (unit.protocolTable_forgetSites (F := F) (G := G)
    SumcheckSourceBodies.runSignature {} 0
    (SumcheckSourceVerifier.sourceRootInputs (some raw) claim (some rounds) service)).trans
    (source_context_prover {} 0 rfl (by decide) raw rounds shape bound admitted claim service)

end Source

/-! ### Complete Reduction root -/

section Reduction
open SumcheckReduceViews

/-- The prover's two returned root components, the received point and the
residual entries; the verifier's point and claim are absent. -/
def reductionResults (raw : List F) (point : List F) :
    Values (Component (assignment F G)) SumcheckReduceBodies.runSignature.outputs :=
  .cons (some point) (.cons (some (restrictPrefixValues raw point)) (.cons none (.cons none .nil)))

/-- The complete Reduction root at the prover in an arbitrary caller context: the
checked table, the actual Reduce at the unit's own maximum and the residual projection. -/
theorem reduction_context_prover (ctx : ProtocolContext) (self : Nat)
    (prover : self = ctx.roles 0) (separate : ctx.roles 1 ≠ self)
    (raw : List F) (count rounds : Nat) (shape : HasShape raw count 1)
    (bound : raw.length < indexLimit) (admitted : rounds ≤ SumcheckReductionNormalForms.reduceMaximum) (enough : rounds ≤ count)
    (claim : Option F) (service : Option Nat) :
    invokeProtocol (unit.plainProtocolTable F G) SumcheckReduceBodies.runSignature ctx self
      (SumcheckReduceVerifier.reduceRootInputs (some raw) (some count) claim (some rounds) service) =
      (PIR.repeatN rounds (roundHonest (ctx.enter "s3" [0, 1]) raw count) []).bind
        (fun point => .done (reductionResults raw point)) := by
  refine (SumcheckReductionNormalForms.prover_invoke (bodies := SumcheckReduceContracts.bodies)
    (ctx := ctx) (self := self) (role := prover) (separate := separate) (raw := raw)
    (count := count) (rounds := rounds) (claim := claim) (service := service) (shape := shape)
    (bound := bound) (enough := enough)).trans ?_
  subst self
  unfold SumcheckReductionNormalForms.proverProcess
  rw [proverReduce_honest unit SumcheckReduceContracts.bodies
    (SumcheckReductionNormalForms.reduceContext ctx) separate SumcheckReductionNormalForms.reduceMaximum raw count shape bound
    rounds admitted]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind]
  rfl

/-- The complete Reduction root at the prover. -/
theorem reduction_prover (raw : List F) (count rounds : Nat) (shape : HasShape raw count 1)
    (bound : raw.length < indexLimit) (admitted : rounds ≤ SumcheckReductionNormalForms.reduceMaximum) (enough : rounds ≤ count)
    (claim : Option F) (service : Option Nat) :
    program.participant F G 0
      (SumcheckReduceVerifier.reduceRootInputs (some raw) (some count) claim (some rounds) service) =
      (PIR.repeatN rounds (roundHonest (ProtocolContext.enter {} "s3" [0, 1]) raw count) []).bind
        (fun point => .done (reductionResults raw point)) :=
  (unit.protocolTable_forgetSites (F := F) (G := G)
    SumcheckReduceBodies.runSignature {} 0
    (SumcheckReduceVerifier.reduceRootInputs (some raw) (some count) claim (some rounds)
      service)).trans
    (reduction_context_prover {} 0 rfl (by decide) raw count rounds shape bound admitted enough
      claim service)

end Reduction

end ZkcExamples.Structured.SumcheckProverRoots
