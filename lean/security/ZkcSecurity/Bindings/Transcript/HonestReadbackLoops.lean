module

public import ZkcSecurity.Bindings.Transcript.HonestReadback
public import Zkc.Construction.DomainView

@[expose] public section

/-! Honest read-back for the existing constructed loop with distinct producer
and validator frames. Captures, yields, exact sort checks and full body returns
remain in the statement. The shared index list supplies zero and partial loops.
-/

set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.Readback
open Zkc.Source Zkc.Construction

variable {carriers : Structured.Carriers}

theorem iterate
    (left right : Domain.View.Block carriers)
    (leftOuter rightOuter : Domain.Environment carriers)
    (leftYielded rightYielded : List Nat) (leftTypes rightTypes : List ValueSort)
    (invariant : List Nat → Domain.Environment carriers → Domain.Environment carriers → Prop)
    (body : ∀ index rest leftCarried rightCarried,
      invariant (index :: rest) leftCarried rightCarried →
      Readback
        (fun leftFinal rightFinal => ∃ leftNext rightNext,
          Domain.read leftFinal leftYielded = some leftNext ∧
          Domain.read rightFinal rightYielded = some rightNext ∧
          Domain.sortsMatch leftTypes leftNext = true ∧
          Domain.sortsMatch rightTypes rightNext = true ∧ invariant rest leftNext rightNext)
        (left (leftOuter ++ .data (.index index) :: leftCarried))
        (right (rightOuter ++ .data (.index index) :: rightCarried)))
    (indices : List Nat) (leftCarried rightCarried : Domain.Environment carriers)
    (holds : invariant indices leftCarried rightCarried) :
    Readback (invariant [])
      (Domain.iterate left leftOuter leftYielded leftTypes indices leftCarried)
      (Domain.iterate right rightOuter rightYielded rightTypes indices rightCarried) := by
  induction indices generalizing leftCarried rightCarried with
  | nil => exact .done holds
  | cons index rest ih =>
      simp only [Domain.iterate]
      apply (body index rest leftCarried rightCarried holds).bind
      intro leftFinal rightFinal returned
      obtain ⟨leftNext, rightNext, readLeft, readRight, sortsLeft, sortsRight, next⟩ := returned
      simp only [readLeft, readRight, sortsLeft, sortsRight, ite_true]
      exact ih leftNext rightNext next

end ZkcSecurity.FiatShamir.Readback
