module

public import ZkcSecurity.Realizations.Gkr.HonestHelpersRounds
public import ZkcSecurity.Realizations.Gkr.HonestProducerRoundAlgorithm
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

variable {F G : Type} [Field F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Exact transport of an already proved current helper law into the source's
plain participant table. This does not assume success of any producer. -/
theorem helper_plain (helper : Helper) (arguments : Values (assignment F G) helper.inputs)
    (results : Values (assignment F G) helper.outputs)
    (law : invoke (GkrSourceLaws.helpers (F := F) (G := G)) helper arguments = .done results) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed helper arguments = .done results := by
  rw [closed_invoke_plain]
  change (invoke (GkrSourceLaws.helpers (F := F) (G := G)) helper arguments).interpret _ = _
  rw [law]
  rfl

theorem empty_plain :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
      GkrSourceBodies.emptyHelper .nil = .done (.cons [] .nil) :=
  helper_plain _ _ _ GkrSourceLaws.empty_equation

open GkrRoundsNormalForms

def round_result (raw : GkrRoundsRealization.RawState F) (point : List F) (challenge : F) : Result F :=
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
theorem round_process {n : Nat} (ctx : ProtocolContext) (raw : GkrRoundsRealization.RawState F)
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
      .done (round_result raw point challenge) := by
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


/-- The source ABI carries exactly the four mathematical vectors. -/
def sourceRaw (raw : Raw F) : GkrRoundsRealization.RawState F :=
  ⟨raw.add, raw.mul, raw.left, raw.right⟩

/-- Exact source loop equality: neither a transcript nor successful helper
execution is supplied by the caller. -/
theorem fold (ctx : ProtocolContext) (start count : Nat) {n : Nat}
    (state : GkrRoundsReference.State F (n + count)) (raw : Raw F)
    (decoded : Decodes raw state)
    (capacity : 2 ^ (n + count) < indexLimit) (point : List F) :
    Finite.fold (fun result _ => GkrRoundsNormalForms.proverProcess (G := G) ctx
      result.1 result.2.1 result.2.2.1 result.2.2.2.1 result.2.2.2.2)
      (List.range' start count) (values raw point) = loop ctx count state raw point := by
  induction count generalizing start raw point with
  | zero => rfl
  | succ count ih =>
    have smaller : 2 ^ (n + count) < indexLimit :=
      (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)).trans_lt capacity
    rw [List.range'_succ, Finite.fold]
    change (GkrRoundsNormalForms.proverProcess ctx (some raw.add) (some raw.mul)
      (some raw.left) (some raw.right) (some point)).bind _ = _
    have step := round_process (G := G) ctx (sourceRaw raw) state decoded smaller point
    dsimp only [sourceRaw] at step
    rw [step]
    simp only [PIR.Process.bind, loop]
    congr 1; funext _; congr 1; funext _; congr 1; funext _; congr 1; funext challenge
    exact ih (start + 1) (GkrRoundsReference.restrict state challenge) (raw.restrict challenge)
      (restriction_decodes raw state decoded challenge)
      smaller (point ++ [challenge])

/-- Returned source tuple, including the intentionally absent verifier slots. -/
def returned (result : Result F) :
    Values (Component (assignment F G)) GkrRoundsNormalForms.roundsOutputs :=
  .cons result.2.2.2.2 (.cons result.1 (.cons result.2.1
    (.cons result.2.2.1 (.cons result.2.2.2.1 (.cons none (.cons none .nil))))))

/-- Complete source producer call, with the original empty-point prelude and
actual repeat admission. -/
theorem source (ctx : ProtocolContext) (separate : ctx.roles 1 ≠ ctx.roles 0)
    (count : Nat) (bounded : count ≤ 4) {n : Nat}
    (state : GkrRoundsReference.State F (n + count)) (raw : Raw F)
    (decoded : Decodes raw state)
    (capacity : 2 ^ (n + count) < indexLimit) :
    GkrRoundsNormalForms.proverRoundsProcess (G := G) ctx
      (some raw.add) (some raw.mul) (some raw.left) (some raw.right) (some count) =
      (loop ctx count state raw []).bind fun result => .done (returned result) := by
  rw [GkrRoundsNormalForms.proverRoundsProcess, empty_plain]
  simp only [PIR.Process.bind, Values.get]
  have repeated := GkrRoundsNormalForms.prover_fold (F := F) (G := G) ctx separate none count bounded
    (GkrRoundsNormalForms.proverState (some raw.add) (some raw.mul) (some raw.left)
      (some raw.right) (some [])) (values raw [])
    (GkrRoundsNormalForms.proverState_masked ctx _ rfl _ _ _ _ _)
  dsimp only [values, GkrRoundsNormalForms.proverState] at repeated
  rw [repeated]
  have folded := fold (G := G) ctx 0 count state raw decoded capacity []
  dsimp only [values] at folded
  rw [folded]
  simp only [PIR.Process.bind_assoc]
  rfl

/-- Source association to the proof-state presentation erases only the ghost
reference. All four real vectors and the entire point remain in the return. -/
theorem source_execute (ctx : ProtocolContext) (separate : ctx.roles 1 ≠ ctx.roles 0)
    (count : Nat) (bounded : count ≤ 4) {n : Nat}
    (state : GkrRoundsReference.State F (n + count)) (raw : Raw F)
    (decoded : Decodes raw state)
    (capacity : 2 ^ (n + count) < indexLimit) :
    GkrRoundsNormalForms.proverRoundsProcess (G := G) ctx
      (some raw.add) (some raw.mul) (some raw.left) (some raw.right) (some count) =
      (execute ctx count state raw []).bind fun result =>
        .done (returned (values result.raw result.point)) := by
  rw [source ctx separate count bounded state raw decoded capacity, ← execute_erases,
    PIR.Process.bind_assoc]
  rfl

end ZkcSecurity.Realizations.Gkr.HonestProducerRounds
