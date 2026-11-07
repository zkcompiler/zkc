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

/-- Preserve the meaning of an inactive yield through all remaining skipped
iterations. A false flag by itself says nothing about the returned state. -/
theorem fold_exit
    {step : A → Nat → PIR.Process (Domain.effects carriers) (Bool × A)}
    {invariant finished : A → Prop}
    (exits : ∀ value index, invariant value → PIR.Yields
      (fun result ↦ invariant result.2 ∧ (result.1 = false → finished result.2))
      (step value index))
    (indices : List Nat) (value : A) (held : invariant value) :
    PIR.Yields (fun result ↦ invariant result.2 ∧
      (result.1 = false → finished result.2))
      (Finite.fold (gated step) indices (true, value)) := by
  induction indices generalizing value with
  | nil => exact ⟨held, by simp⟩
  | cons index rest ih =>
      change PIR.Yields _ ((step value index).bind (Finite.fold (gated step) rest))
      apply (exits value index held).bind
      rintro ⟨flag, next⟩ ⟨nextHeld, finished⟩
      cases flag with
      | false => rw [fold_inactive]; exact ⟨nextHeld, finished⟩
      | true => exact ih next nextHeld

/-- Progress and exit meaning have separate obligations. Together they prove
the returned state satisfies the completion condition; a source stop remains
a stop. This is the source fold used by the actual local-range connection. -/
theorem fold_completed
    {step : A → Nat → PIR.Process (Domain.effects carriers) (Bool × A)}
    {invariant finished : A → Prop} {remaining : A → Nat}
    (progress : StepProgress step invariant remaining)
    (exits : ∀ value index, invariant value → PIR.Yields
      (fun result ↦ invariant result.2 ∧ (result.1 = false → finished result.2))
      (step value index))
    (indices : List Nat) (value : A) (held : invariant value)
    (enough : remaining value < indices.length) :
    PIR.Yields (fun value ↦ invariant value ∧ finished value)
      ((Finite.fold (gated step) indices (true, value)).bind
        fun result ↦ .done result.2) := by
  apply ((fold_finished progress indices value held enough).and
    (fold_exit exits indices value held)).bind
  intro result established
  exact ⟨established.1.1, established.2.2 established.1.2⟩

/-- Discharge the range's final state obligation on its existing actual-body
certificate. No replacement range semantics or protocol-specific loop proof
is needed. The callback still proves actual branch correspondence and exit
meaning; rank arithmetic alone cannot supply either fact. -/
noncomputable def completedSimulation {B : Type}
    {step : A → Nat → PIR.Process (Domain.effects carriers) (Bool × A)}
    {invariant finished : A → Prop} {remaining : A → Nat}
    {returns nextReturns : A → B → Prop}
    {live : PIR.Process (Domain.effects carriers) A → Domain.Environment carriers → Prop}
    {target : PIR.Process (Domain.effects carriers) B}
    (progress : StepProgress step invariant remaining)
    (exits : ∀ value index, invariant value → PIR.Yields
      (fun result ↦ invariant result.2 ∧ (result.1 = false → finished result.2))
      (step value index))
    (indices : List Nat) (value : A) (held : invariant value)
    (enough : remaining value < indices.length)
    (certificate : Original.Simulation returns live
      ((Finite.fold (gated step) indices (true, value)).bind
        fun result ↦ .done result.2) target)
    (refine : ∀ value final, invariant value → finished value →
      returns value final → nextReturns value final) :
    Original.Simulation nextReturns live
      ((Finite.fold (gated step) indices (true, value)).bind
        fun result ↦ .done result.2) target :=
  certificate.refineReturns (fold_completed progress exits indices value held enough)
    (fun value final established ↦ refine value final established.1 established.2)

end Zkc.Construction.ConnectionLocalRange
