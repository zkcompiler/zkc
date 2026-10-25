module

public import ZkcSecurity.Realizations.Sumcheck.OriginalRawSource
public import ZkcSecurity.Realizations.Sumcheck.ValidatorHelpers

@[expose] public section

/-! Total original closed-helper outcomes. Point overflow, dimension refusal,
and raw-vector overflow occur in source order, before the scalar comparison.
The same polynomial restriction function is shared with the table family. -/
set_option autoImplicit false
namespace ZkcSecurity.Realizations.Sumcheck.OriginalRaw
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open PrimitiveLibrary SumcheckHelperBodies SumcheckHelperLaws

variable {F G : Type} [Field F] [DecidableEq F]

noncomputable def terminal {I : PIR.Signature} (raw point : List F) (scalar : F) :
    PIR.Process I (Values (Component (assignment F G)) [.boolean]) :=
  if point.length < indexLimit then
    if point.length < 64 then
      if raw.length < indexLimit then
        .done (.cons (some (decide (HasShape raw point.length 1 ∧
          (Zkc.Polynomial.Multilinear.restrictPrefixValues raw point).sum = scalar))) .nil)
      else .halt .exhausted
    else .done (.cons (some false) .nil)
  else .halt .exhausted

variable [AddCommGroup G] [Module F G] [DecidableEq G]

/-- A total source-helper equation, with no vector, dimension, or shape premise. -/
theorem source_terminal (payload : UnitPayload)
    (bodies : OriginalSumcheckLibrary.TerminalBodies payload.definitions)
    (self : Nat) (raw point : List F) (scalar : F) :
    Participant.owned self self
      (invoke (OriginalSumcheckLibrary.helpers (G := G) payload).closed checkHelper)
      (.cons (some raw) (.cons (some point) (.cons (some scalar) .nil))) =
      terminal raw point scalar := by
  unfold terminal
  by_cases pointBound : point.length < indexLimit
  · rw [ite_eq_left pointBound]
    by_cases small : point.length < 64
    · rw [ite_eq_left small]
      by_cases rawBound : raw.length < indexLimit
      · rw [ite_eq_left rawBound]
        exact OriginalSumcheckLibrary.check_present payload bodies self raw point scalar rawBound pointBound
      · rw [ite_eq_right rawBound]
        simp only [Participant.owned, ↓reduceIte, RoleFamily.sequence]
        change (invoke (OriginalSumcheckLibrary.helpers (G := G) payload).closed checkHelper
          (checkInputs raw point scalar)).bind _ = _
        rw [← (OriginalSumcheckLibrary.helpers_lift payload).closed,
          SumcheckVerifierHelpers.closed_invoke_plain, bodies.check.invoke payload.linked]
        rw [check_vector_exhausted_generic_body _
          (lessAll_bounded _ (MapFirstContracts.less_all payload.linked bodies.first))
          (fun xs n w => bodies.first.shape.invoke payload.linked (inputs xs n w))
          raw point scalar small rawBound]
        rfl
    · rw [ite_eq_right small]
      simp only [Participant.owned, ↓reduceIte, RoleFamily.sequence]
      change (invoke (OriginalSumcheckLibrary.helpers (G := G) payload).closed checkHelper
        (checkInputs raw point scalar)).bind _ = _
      rw [← (OriginalSumcheckLibrary.helpers_lift payload).closed,
        SumcheckVerifierHelpers.closed_invoke_plain, bodies.check.invoke payload.linked]
      rw [check_large_dimension_generic_body _
        (lessAll_bounded _ (MapFirstContracts.less_all payload.linked bodies.first))
        (fun xs n w => bodies.first.shape.invoke payload.linked (inputs xs n w))
        raw point scalar pointBound small]
      rfl
  · rw [ite_eq_right pointBound]
    simp only [Participant.owned, ↓reduceIte, RoleFamily.sequence]
    change (invoke (OriginalSumcheckLibrary.helpers (G := G) payload).closed checkHelper
      (checkInputs raw point scalar)).bind _ = _
    rw [← (OriginalSumcheckLibrary.helpers_lift payload).closed,
      SumcheckVerifierHelpers.closed_invoke_plain, bodies.check.invoke payload.linked,
      (check_point_exhausted _ raw point scalar pointBound).1]
    rfl

end ZkcSecurity.Realizations.Sumcheck.OriginalRaw
