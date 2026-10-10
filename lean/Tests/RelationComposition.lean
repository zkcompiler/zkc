import Zkc.Realization.Acceptance

namespace Tests.RelationComposition

open PIR.Relation

/-- Hiding a shared boundary before connecting components loses consistency. -/
theorem closed_validity_insufficient :
    ((∃ b : Bool, b = false) ↔ ∃ b : Bool, b = true) ∧
    Connected (fun b : Bool => b = false) Eq (fun b => b = false) ∧
    ¬ Connected (fun b : Bool => b = false) Eq (fun b => b = true) := by
  unfold Connected
  decide

/-- The left boundary changes carrier to Nat; only its inhabited image matters. -/
theorem heterogeneous_reencoding :
    Connected (fun u : Nat => u = 1) (fun u v : Nat => u = v + 1) (fun v => v = 0) ↔
      Connected (fun a : Bool => a = false) (fun a b : Bool => a = b) (fun b => b = false) := by
  apply Connected.represented
    (fun a : Bool => a = false) (fun b : Bool => b = false)
    (fun u : Nat => u = 1) (fun v : Nat => v = 0)
    (fun a u => u = if a then 2 else 1) (fun b v => v = if b then 1 else 0)
  · intro a _; exact ⟨if a then 2 else 1, rfl⟩
  · intro b _; exact ⟨if b then 1 else 0, rfl⟩
  · intro u; simp
  · intro v; simp
  · intro a b u v ha hb hu hv
    subst a; subst b
    simp only [Bool.false_eq_true, ↓reduceIte] at hu hv
    subst u; subst v
    simp

theorem literal_target_equality_wrong :
    ¬ Connected (fun u : Nat => u = 1) Eq (fun v => v = 0) := by
  intro h
  obtain ⟨u, v, hu, huv, hv⟩ := h
  omega

/-- One source boundary may have several admitted target representations.
The common relation law supports both, rather than selecting one encoder image. -/
theorem multiple_target_representations :
    Connected (fun _ : Bool => True) (fun (_ : Bool) (_ : Unit) => True) (fun _ => True) ↔
      Connected (fun _ : Unit => True) (fun _ _ : Unit => True) (fun _ => True) := by
  apply Connected.represented
    (fun _ : Unit => True) (fun _ : Unit => True)
    _ _ (fun (_ : Unit) (_ : Bool) => True) (fun (_ : Unit) (_ : Unit) => True)
  · intro _ _; exact ⟨false, trivial⟩
  · intro _ _; exact ⟨(), trivial⟩
  · intro _; exact ⟨fun _ => ⟨(), trivial, trivial⟩, fun _ => trivial⟩
  · intro _; exact ⟨fun _ => ⟨(), trivial, trivial⟩, fun _ => trivial⟩
  · intro _ _ _ _ _ _ _ _; rfl

theorem one_encoder_does_not_cover_both :
    ¬ ∃ encode : Unit → Bool, ∀ u, True ↔ ∃ a, True ∧ encode a = u := by
  rintro ⟨encode, image⟩
  obtain ⟨a, _, ha⟩ := (image false).mp trivial
  obtain ⟨b, _, hb⟩ := (image true).mp trivial
  cases a; cases b
  cases ha.symm.trans hb

/-- Empty images alone are compatible with an empty representation. Without
coverage they do not preserve an inhabited source connection. -/
theorem image_laws_without_coverage_insufficient :
    (∀ u : Unit, False ↔ ∃ a : Unit, True ∧ (fun _ _ => False) a u) ∧
    Connected (fun _ : Unit => True) (fun _ _ : Unit => True) (fun _ => True) ∧
    ¬ Connected (fun _ : Unit => False) (fun _ _ : Unit => True) (fun _ => False) := by
  exact ⟨fun _ => ⟨False.elim, fun ⟨_, _, h⟩ => h⟩,
    ⟨(), (), trivial, trivial, trivial⟩, fun ⟨_, _, h, _⟩ => h⟩

/-- A range check can be removed from the left because the right still checks
the same connected value. Neither source nor target changes its input domain. -/
theorem redundant_check_elimination (input : Nat) :
    Connected (fun a => a < 4 ∧ a = input) Eq (fun b => b < 4 ∧ b = input) ↔
      Connected (fun a => a = input) Eq (fun b => b < 4 ∧ b = input) := by
  apply Connected.replace Eq
  · intro a b same right
    subst b
    exact ⟨And.right, fun h => ⟨right.1, h⟩⟩
  · intro _ _ _ _; rfl

theorem redundant_check_not_unconditionally_removable :
    ¬ ∀ a : Nat, (a < 4 ∧ a = 4) ↔ a = 4 := by
  intro h
  have impossible := (h 4).mpr rfl
  omega

/-- Relying on the old other component twice would permit deleting both checks.
The staged premise in Connected.replace rules out this circular justification. -/
theorem mutually_assumed_checks_insufficient :
    (∀ _ : Unit, False → (False ↔ True)) ∧
    ¬ Connected (fun _ : Unit => False) Eq (fun _ => False) ∧
    Connected (fun _ : Unit => True) Eq (fun _ => True) :=
  ⟨fun _ h => False.elim h, fun ⟨_, _, h, _⟩ => h, ⟨(), (), trivial, rfl, trivial⟩⟩

end Tests.RelationComposition
