module

public import ZkcSecurity.Realizations.Gkr.HonestHelpersRounds
public import ZkcExamples.Structured.GkrRoundsNormalForms

@[expose] public section

/-! A source producer round, with every coefficient, arbitrary delivered
challenge, all four updated factors, and the retained challenge prefix.
This is a local equation; whole-layer and root composition are separate. -/

namespace ZkcSecurity.Realizations.Gkr.HonestRound
open Zkc Source Structured
open ZkcExamples.Structured GkrSourceLaws SumcheckVerifierHelpers
open ZkcSecurity.Examples.Components
open GkrRoundsNormalForms

set_option backward.isDefEq.respectTransparency false

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

abbrev Result (F : Type) :=
  Option (List F) × Option (List F) × Option (List F) × Option (List F) × Option (List F)

/-- Pure return data, including the whole existing prefix. -/
def result (raw : GkrRoundsRealization.RawState F) (point : List F) (challenge : F) : Result F :=
  (some (raw.restrict challenge).add, some (raw.restrict challenge).mul,
    some (raw.restrict challenge).left, some (raw.restrict challenge).right,
    some (point ++ [challenge]))

private theorem append_plain (point : List F) (challenge : F) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
      GkrSourceBodies.appendHelper (.cons point (.cons challenge .nil)) =
      .done (.cons (point ++ [challenge]) .nil) := by
  rw [closed_invoke_plain]
  change (invoke (helpers (G := G)) GkrSourceBodies.appendHelper _).interpret _ = _
  rw [append_equation]
  rfl

/-- Exact actual producer, for every possible field delivery. The equation
preserves the three ordered payloads and all continuation branches. -/
theorem process {n : Nat} (ctx : ProtocolContext) (raw : GkrRoundsRealization.RawState F)
    (state : GkrRoundsReference.State F (n + 1))
    (decoded : GkrRoundsRealization.Decodes raw state)
    (capacity : 2 ^ n < indexLimit) (point : List F) :
    GkrRoundsNormalForms.proverProcess (G := G) ctx
      (some raw.add) (some raw.mul) (some raw.left) (some raw.right) (some point) =
      .call (.send (ty := .field scalarDomain) (round0Site ctx) (ctx.roles 1)
        (GkrRoundsReference.message state).constant) fun _ =>
      .call (.send (ty := .field scalarDomain) (round1Site ctx) (ctx.roles 1)
        (GkrRoundsReference.message state).linear) fun _ =>
      .call (.send (ty := .field scalarDomain) (round2Site ctx) (ctx.roles 1)
        (GkrRoundsReference.message state).quadratic) fun _ =>
      .call (.receive (.field scalarDomain) (deliverySite ctx) (ctx.roles 1)) fun challenge =>
      .done (result raw point challenge) := by
  simp only [GkrRoundsNormalForms.proverProcess]
  rw [show invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
      GkrSourceBodies.helper41Helper
      (.cons raw.add (.cons raw.mul (.cons raw.left (.cons raw.right .nil)))) = _ from
    HonestHelpers.round_coefficients raw state decoded capacity]
  simp only [PIR.Process.bind]
  congr 1; funext _; congr 1; funext _; congr 1; funext _; congr 1; funext challenge
  rw [show invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
      GkrSourceBodies.helper45Helper
      (.cons raw.add (.cons raw.mul (.cons raw.left (.cons raw.right (.cons challenge .nil))))) = _ from
    HonestHelpers.round_restriction raw state decoded capacity challenge]
  simp only [PIR.Process.bind, Values.get, append_plain]
  rfl

/-- The existing runner uses each actually reached state. A stopped send or
receive remains stopped, with its state and events. No state is rebased. -/
theorem run {n : Nat} {H E : Type} (ctx : ProtocolContext)
    (raw : GkrRoundsRealization.RawState F) (state : GkrRoundsReference.State F (n + 1))
    (decoded : GkrRoundsRealization.Decodes raw state)
    (capacity : 2 ^ n < indexLimit) (point : List F)
    (handler : PIR.Handler (participantInterface F G) H E) (initial : H) :
    (GkrRoundsNormalForms.proverProcess ctx
      (some raw.add) (some raw.mul) (some raw.left) (some raw.right) (some point)).run handler initial =
      (handler (.send (ty := .field scalarDomain) (round0Site ctx) (ctx.roles 1)
        (GkrRoundsReference.message state).constant) initial).follow fun _ afterConstant =>
      (handler (.send (ty := .field scalarDomain) (round1Site ctx) (ctx.roles 1)
        (GkrRoundsReference.message state).linear) afterConstant).follow fun _ afterLinear =>
      (handler (.send (ty := .field scalarDomain) (round2Site ctx) (ctx.roles 1)
        (GkrRoundsReference.message state).quadratic) afterLinear).follow fun _ afterQuadratic =>
      (handler (.receive (.field scalarDomain) (deliverySite ctx) (ctx.roles 1)) afterQuadratic).follow
        fun challenge reached => ⟨.returned (result raw point challenge), reached, []⟩ := by
  rw [process ctx raw state decoded capacity point]
  rfl

end ZkcSecurity.Realizations.Gkr.HonestRound
