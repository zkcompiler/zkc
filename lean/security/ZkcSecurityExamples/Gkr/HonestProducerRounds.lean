module

public import ZkcSecurityExamples.Gkr.HonestHelpersRounds
public import Zkc.Protocols.Sumcheck.Source.VerifierHelpers
public import ZkcSecurityExamples.Gkr.HonestProducerRoundAlgorithm
public import Zkc.Source.Structured.Occurrence

@[expose] public section

/-! Entire actual producer round loops. The loop equations quantify over every
field delivery and keep all four factors and the complete point prefix. -/



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace ZkcSecurity.Realizations.Gkr.HonestProducerRounds
open Zkc Source Structured
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open ZkcExamples.Structured GkrSourceLaws SumcheckVerifierHelpers
open ZkcSecurity.Examples.Components
open GkrRoundsRealization (RawState Decodes restriction_decodes)


variable {F G : Type} [Field F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

theorem empty_plain :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
      GkrSourceBodies.emptyHelper .nil =
      .done (HonestHelpers.EmptyResults.pack (Value := assignment F G) ⟨[]⟩) :=
  closed_invoke_returned GkrSourceViews.unit _ _ _ GkrSourceLaws.empty_equation

open Generated.Presentations.Gkr.Rounds

def round_result (raw : RawState F) (point : List F) (challenge : F) : Result F :=
  (some (raw.restrict challenge).add, some (raw.restrict challenge).mul,
    some (raw.restrict challenge).left, some (raw.restrict challenge).right,
    some (point ++ [challenge]))

/-- Exact actual producer, for every possible field delivery. The equation
preserves the three ordered payloads and all continuation branches. -/
theorem round_process {n : Nat} (ctx : ProtocolContext) (raw : RawState F)
    (state : GkrRoundsReference.State F (n + 1))
    (decoded : Decodes raw state)
    (capacity : 2 ^ n < indexLimit) (point : List F) :
    Generated.Presentations.Gkr.Rounds.proverProcess (G := G) ctx
      (some raw.add) (some raw.mul) (some raw.left) (some raw.right) (some point) =
      .call (.send (ty := .field scalarDomain) (GkrVerifier.roundSite ctx "0") (ctx.roles 1)
        (GkrRoundsReference.message state).constant) fun _ =>
      .call (.send (ty := .field scalarDomain) (GkrVerifier.roundSite ctx "1") (ctx.roles 1)
        (GkrRoundsReference.message state).linear) fun _ =>
      .call (.send (ty := .field scalarDomain) (GkrVerifier.roundSite ctx "2") (ctx.roles 1)
        (GkrRoundsReference.message state).quadratic) fun _ =>
      .call (.receive (.field scalarDomain) (GkrVerifier.deliverySite ctx) (ctx.roles 1)) fun challenge =>
      .done (round_result raw point challenge) := by
  simp only [Generated.Presentations.Gkr.Rounds.proverProcess, Evaluation.ComponentTables.toOn, Generated.Presentations.Gkr.payload,
    Generated.Presentations.Gkr.program, GkrSourceViews.program]
  have coefficients := HonestHelpers.round_coefficients (G := G) raw state decoded capacity
  dsimp only [GkrRoundsRealization.RawState.values] at coefficients
  rw [coefficients]
  simp only [PIR.Process.bind]
  congr 1; funext _; congr 1; funext _; congr 1; funext _; congr 1; funext challenge
  rw [show invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
      GkrSourceBodies.helper45Helper
      (HonestHelpers.RestrictionArguments.pack (Value := assignment F G)
        { add := raw.add, mul := raw.mul, left := raw.left, right := raw.right, challenge }) = _ from
    HonestHelpers.round_restriction raw state decoded capacity challenge]
  simp only [PIR.Process.bind]
  rfl


/-- The existing runner uses each actually reached state. A stopped send or
receive remains stopped, with its state and events. No state is rebased. -/
theorem round_run {n : Nat} {H E : Type} (ctx : ProtocolContext)
    (raw : GkrRoundsRealization.RawState F) (state : GkrRoundsReference.State F (n + 1))
    (decoded : GkrRoundsRealization.Decodes raw state)
    (capacity : 2 ^ n < indexLimit) (point : List F)
    (handler : PIR.Handler (participantInterface F G) H E) (initial : H) :
    (Generated.Presentations.Gkr.Rounds.proverProcess ctx
      (some raw.add) (some raw.mul) (some raw.left) (some raw.right) (some point)).run handler initial =
      (handler (.send (ty := .field scalarDomain) (GkrVerifier.roundSite ctx "0") (ctx.roles 1)
        (GkrRoundsReference.message state).constant) initial).follow fun _ afterConstant =>
      (handler (.send (ty := .field scalarDomain) (GkrVerifier.roundSite ctx "1") (ctx.roles 1)
        (GkrRoundsReference.message state).linear) afterConstant).follow fun _ afterLinear =>
      (handler (.send (ty := .field scalarDomain) (GkrVerifier.roundSite ctx "2") (ctx.roles 1)
        (GkrRoundsReference.message state).quadratic) afterLinear).follow fun _ afterQuadratic =>
      (handler (.receive (.field scalarDomain) (GkrVerifier.deliverySite ctx) (ctx.roles 1)) afterQuadratic).follow
        fun challenge reached => ⟨.returned (round_result raw point challenge), reached, []⟩ := by
  rw [round_process ctx raw state decoded capacity point]
  rfl


end ZkcSecurity.Realizations.Gkr.HonestProducerRounds
