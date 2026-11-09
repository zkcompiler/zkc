module

public import Zkc.Protocol.Components.Contract
public import PolyFun.PFunctor.Free.WP.Upstream

/-! The upstream quantitative WP interface for the public, failure-aware Process.

This is an adapter to the existing fold, not a second execution meaning. The exception
postcondition assigns a potential to every stop, with the reached state and complete history.
Interpretations are explicit values: importing this module does not choose an operation spec.
-/

@[expose] public section

open PIR Std.WP

namespace ProtocolProof

abbrev Potential (S L : Type) := (S × List L) → ENNReal

namespace OperationSpec

variable {I : Signature} {S L : Type}

/-- One outcome postcondition from separate returned and stopped postconditions. -/
def outcomePost {A : Type} (post : A → Potential S L)
    (stopped : Stop → Potential S L) : Outcome A → Potential S L
  | .returned value => post value
  | .stopped reason => stopped reason

/-- Preserve all outcomes, private state and observations in the core WP interface. -/
@[instance_reducible]
noncomputable def toWP (spec : OperationSpec I S L) (mono : spec.Monotone) (A : Type) :
    WP (Process I A) A (Potential S L) (Stop → Potential S L) where
  wpTrans program := ⟨fun post stopped => wpFold spec program (outcomePost post stopped)⟩
  wp_trans_monotone program post post' stopped stopped' hstop hpost := by
    apply PFunctor.FreeM.wpFold_mono mono
    intro outcome
    cases outcome with
    | returned value => exact hpost value
    | stopped reason => exact hstop reason

/-- The common `vcgen` monad interface; it does not assume independent operations. -/
@[instance_reducible]
noncomputable def toWPMonad (spec : OperationSpec I S L) (mono : spec.Monotone) :
    WPMonad (Process I) (Potential S L) (Stop → Potential S L) where
  toLawfulMonad := inferInstance
  toWP := toWP spec mono
  pure_le_wp_pure _ _ _ := Lean.Order.PartialOrder.rel_refl
  bind_le_wp_bind program next post stopped := by
    change wpFold spec program
      (outcomePost (fun value => wpFold spec (next value) (outcomePost post stopped)) stopped) ≤
        wpFold spec (program.bind next) (outcomePost post stopped)
    rw [wpFold_bind]
    exact le_rfl

instance instExactWPMonad (spec : OperationSpec I S L) (mono : spec.Monotone) :
    @ExactWPMonad (Process I) (Potential S L) (Stop → Potential S L)
      _ _ _ (spec.toWPMonad mono) := by
  let := spec.toWPMonad mono
  apply ExactWPMonad.of_eq
  · intros; rfl
  · intros A B program next post stopped
    change wpFold spec (program.bind next) (outcomePost post stopped) = _
    rw [wpFold_bind]
    rfl

/-- Upper contracts use the exact same interpretation in the order dual. -/
@[instance_reducible]
noncomputable def toUpperWPMonad (spec : OperationSpec I S L) (mono : spec.Monotone) :
    WPMonad (Process I) (Potential S L)ᵒᵈ (Stop → Potential S L)ᵒᵈ :=
  letI := spec.toWPMonad mono
  ExactWPMonad.dual

/-- Exact normalization of the upstream interface, retaining the complete outcome post. -/
theorem wp_lower (spec : OperationSpec I S L) (mono : spec.Monotone) {A : Type}
    (program : Process I A) (post : A → Potential S L) (stopped : Stop → Potential S L) :
    @wp _ _ _ _ _ _ ((spec.toWPMonad mono).toWP A) program post stopped =
      wpFold spec program (outcomePost post stopped) := rfl

theorem wp_upper (spec : OperationSpec I S L) (mono : spec.Monotone) {A : Type}
    (program : Process I A) (post : A → (Potential S L)ᵒᵈ)
    (stopped : (Stop → Potential S L)ᵒᵈ) :
    @wp _ _ _ _ _ _ ((spec.toUpperWPMonad mono).toWP A) program post stopped =
      OrderDual.toDual (wpFold spec program
        (outcomePost (fun value => OrderDual.ofDual (post value)) (OrderDual.ofDual stopped))) := rfl

theorem lowerBound_iff_triple (spec : OperationSpec I S L) (mono : spec.Monotone)
    {A : Type} (program : Process I A) (post : A → Potential S L)
    (stopped : Stop → Potential S L) (bound : Potential S L) :
    LowerBound spec program (outcomePost post stopped) bound ↔
      @Triple _ _ _ _ _ _ program ((spec.toWPMonad mono).toWP A) bound post stopped :=
  by
    let := spec.toWPMonad mono
    constructor
    · intro h; exact ⟨h⟩
    · intro h; exact h.le_wp

theorem upperBound_iff_triple (spec : OperationSpec I S L) (mono : spec.Monotone)
    {A : Type} (program : Process I A) (post : A → Potential S L)
    (stopped : Stop → Potential S L) (bound : Potential S L) :
    UpperBound spec program (outcomePost post stopped) bound ↔
      @Triple _ _ _ _ _ _ program ((spec.toUpperWPMonad mono).toWP A)
        (OrderDual.toDual bound) (fun a => OrderDual.toDual (post a))
        (OrderDual.toDual stopped) :=
  by
    let := spec.toUpperWPMonad mono
    constructor
    · intro h; exact ⟨h⟩
    · intro h; exact h.le_wp

end OperationSpec
/-- Export an upper verification condition in the ordinary pointwise mathematical order. -/
theorem upper_entailment {S L : Type} (left right : Potential S L) :
    Lean.Order.PartialOrder.rel (OrderDual.toDual left) (OrderDual.toDual right) ↔
      right ≤ left := Iff.rfl

/-- Export a lower verification condition without introducing new state assumptions. -/
theorem lower_entailment {S L : Type} (left right : Potential S L) :
    Lean.Order.PartialOrder.rel left right ↔ left ≤ right := Iff.rfl

/-- Exact interpretation commutes with a selected pure branch. -/
theorem wpFold_ite {I : Signature} {S L A : Type} (spec : OperationSpec I S L)
    (condition : Prop) [Decidable condition] (yes no : Process I A)
    (post : Outcome A → Potential S L) :
    wpFold spec (if condition then yes else no) post =
      if condition then wpFold spec yes post else wpFold spec no post := by
  split <;> rfl

end ProtocolProof
