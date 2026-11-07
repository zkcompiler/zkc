module

public import Zkc.Construction.ConnectionLocalRange

@[expose] public section

/-! Resource adequacy for the existing conditional range. A branch invariant
and a decreasing amount of remaining work justify the final continuation flag.
This is a return property: stopping outcomes are preserved, not turned into
successful completion or a totality claim. -/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionLocalRange
open Zkc.Source
variable {carriers : Structured.Carriers} {A : Type}

/-- Every returned continuing state preserves the invariant and consumes work.
An inactive result preserves the invariant without needing a positive measure. -/
def StepProgress
    (step : A → Nat → PIR.Process (Domain.effects carriers) (Bool × A))
    (invariant : A → Prop) (remaining : A → Nat) : Prop :=
  ∀ value index, invariant value → PIR.Yields
    (fun result ↦ invariant result.2 ∧
      (result.1 = true → remaining result.2 < remaining value)) (step value index)

/-- If execution still requests another iteration, every performed iteration
has consumed at least one unit. The index schedule itself is arbitrary. -/
theorem fold_remaining
    {step : A → Nat → PIR.Process (Domain.effects carriers) (Bool × A)}
    {invariant : A → Prop} {remaining : A → Nat}
    (progress : StepProgress step invariant remaining) (indices : List Nat)
    (value : A) (held : invariant value) :
    PIR.Yields (fun result ↦ invariant result.2 ∧
      (result.1 = true → remaining result.2 + indices.length ≤ remaining value))
      (Finite.fold (gated step) indices (true, value)) := by
  induction indices generalizing value with
  | nil => exact ⟨held, by simp⟩
  | cons index rest ih =>
      change PIR.Yields _ ((step value index).bind (Finite.fold (gated step) rest))
      apply (progress value index held).bind
      rintro ⟨flag, next⟩ ⟨nextHeld, decrease⟩
      cases flag with
      | false =>
          rw [fold_inactive]
          exact ⟨nextHeld, by simp⟩
      | true =>
          apply (ih next nextHeld).mono
          intro result retained
          refine ⟨retained.1, ?_⟩
          intro active
          have smaller := decrease rfl
          have consumed := retained.2 active
          dsimp only at smaller
          simp only [List.length_cons]
          omega

/-- One more iteration than the initial remaining work forces an inactive
returned state. A halted process still halts and makes no returned-state claim. -/
theorem fold_finished
    {step : A → Nat → PIR.Process (Domain.effects carriers) (Bool × A)}
    {invariant : A → Prop} {remaining : A → Nat}
    (progress : StepProgress step invariant remaining) (indices : List Nat)
    (value : A) (held : invariant value) (enough : remaining value < indices.length) :
    PIR.Yields (fun result ↦ invariant result.2 ∧ result.1 = false)
      (Finite.fold (gated step) indices (true, value)) := by
  apply (fold_remaining progress indices value held).mono
  intro result retained
  refine ⟨retained.1, ?_⟩
  cases active : result.1 with
  | false => rfl
  | true =>
      have consumed := retained.2 active
      omega

end Zkc.Construction.ConnectionLocalRange
