module

public import ZkcSecurity.Families.Gkr.Circuit
public import ZkcSecurity.Examples.Components.GkrRoundsLayout

public section

/-! Attach the independent circuit reference to the existing four-factor GKR
Sumcheck realization. Example-owned reference data stays outside the generic
circuit, output and combination mathematics.
-/

namespace ZkcSecurity.Realizations.Gkr
open Zkc.Polynomial Zkc.Polynomial.Multilinear Zkc.Protocols.Gkr
open Zkc.Obligations ZkcSecurity.Families.Gkr
open ZkcSecurity.Examples.Components

variable {F : Type} [Field F] {width : Nat}

namespace Circuit

@[expose] def factors (circuit : Circuit F width) (remaining index : Nat)
    (point : Fin width → F) : GkrRoundsReference.State F (width + width) :=
  GkrRoundsLayout.state (fixPrefix width (circuit.add index) point)
    (fixPrefix width (circuit.mul index) point)
    (circuit.wires remaining (index + 1)) (circuit.wires remaining (index + 1))

theorem layout_front (x y : Nat) (bits : Fin (y + x) → Bool) :
    GkrRoundsLayout.leading x y bits = front x bits := by
  induction x with
  | zero => rfl
  | succ x ih =>
    change Fin.cons (α := fun _ => Bool) (bits 0) (GkrRoundsLayout.leading x y (bits ∘ Fin.succ)) = _
    rw [ih]
    rfl

theorem layout_back (x y : Nat) (bits : Fin (y + x) → Bool) :
    GkrRoundsLayout.trailing x y bits = back x bits := by
  induction x with
  | zero => rfl
  | succ x ih => exact ih (bits ∘ Fin.succ)

theorem factors_admissible (circuit : Circuit F width) (remaining index : Nat)
    (point : Fin width → F) : GkrRoundsReference.admissible (factors circuit remaining index point) :=
  GkrRoundsLayout.admissible_state _ _ _ _ _ _

/-- The registered layer identity, independent of the scalar claim. -/
theorem layer_identity (circuit : Circuit F width) (remaining index : Nat)
    (point : Fin width → F) :
    extension width (circuit.wires (remaining + 1) index) point =
      GkrRoundsReference.total (factors circuit remaining index point) := by
  rw [Families.Gkr.Circuit.wires, values_succ, extension_layer]
  unfold GkrRoundsReference.total factors GkrRoundsLayout.state
  congr 1
  funext bits
  simp only [gates, sumTable, productTable, GkrRoundsLayout.replicate,
    GkrRoundsLayout.tile, layout_front, layout_back,
    Zkc.Protocols.AlgebraicRounds.Gate.value, Families.Gkr.Circuit.wires]
  ring

/-- Complete-point adequacy keeps the four extensions separate. In particular
this is not the extension of a pointwise product table. -/
theorem factors_evaluation (circuit : Circuit F width) (remaining index : Nat)
    (point left right : Fin width → F) :
    let s := factors circuit remaining index point
    let pair := Quadratic.point width left right
    Zkc.Protocols.AlgebraicRounds.Gate.value
        (extension (width + width) s.add pair) (extension (width + width) s.mul pair)
        (extension (width + width) s.left pair) (extension (width + width) s.right pair) =
      Zkc.Protocols.AlgebraicRounds.Gate.value
        (extension (width + width + width) (circuit.add index) (Quadratic.point width point pair))
        (extension (width + width + width) (circuit.mul index) (Quadratic.point width point pair))
        (extension width (circuit.wires remaining (index + 1)) left)
        (extension width (circuit.wires remaining (index + 1)) right) := by
  dsimp only [factors, GkrRoundsLayout.state]
  have leftEq : GkrRoundsLayout.replicate width width (circuit.wires remaining (index + 1)) =
      fun bits => circuit.wires remaining (index + 1) (front width bits) := by
    funext bits; simp only [GkrRoundsLayout.replicate, layout_front]
  have rightEq : GkrRoundsLayout.tile width width (circuit.wires remaining (index + 1)) =
      fun bits => circuit.wires remaining (index + 1) (back width bits) := by
    funext bits; simp only [GkrRoundsLayout.tile, layout_back]
  rw [extension_fixPrefix, extension_fixPrefix, leftEq, rightEq, extension_front, extension_back]

end Circuit

open Circuit

@[expose] def sumRelation (n : Nat) :
    ClaimRelation (GkrRoundsReference.State F n × F) Unit where
  Holds statement _ := GkrRoundsReference.admissible statement.1 ∧
    statement.2 = GkrRoundsReference.total statement.1
  No statement := GkrRoundsReference.admissible statement.1 ∧
    statement.2 ≠ GkrRoundsReference.total statement.1
  no_excludes _ _ wrong yes := wrong.2 yes.2

@[expose] def toSum (circuit : Circuit F width) (remaining index : Nat)
    (evaluation : Evaluation F width) : GkrRoundsReference.State F (width + width) × F :=
  (factors circuit remaining index evaluation.point, evaluation.claim)

theorem layer_sound (circuit : Circuit F width) (remaining index : Nat) :
    (evaluationRelation (circuit.wires (remaining + 1) index)).SoundLink
      (sumRelation (width + width)) (toSum circuit remaining index) := by
  intro evaluation wrong
  refine ⟨factors_admissible circuit _ _ _, ?_⟩
  intro same
  exact wrong ⟨(), same.trans (layer_identity circuit _ _ _).symm⟩

theorem layer_honest (circuit : Circuit F width) (remaining index : Nat) :
    (evaluationRelation (circuit.wires (remaining + 1) index)).HonestLink
      (sumRelation (width + width)) (toSum circuit remaining index) := by
  rintro evaluation ⟨_, correct⟩
  exact ⟨(), factors_admissible circuit _ _ _, correct.trans (layer_identity circuit _ _ _)⟩

end ZkcSecurity.Realizations.Gkr
