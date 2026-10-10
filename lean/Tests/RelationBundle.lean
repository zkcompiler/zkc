import Zkc.Relation.Bundle.AIR
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation

set_option autoImplicit false

namespace Tests.RelationBundle

open Zkc.Relation Zkc.Relation.Bundle
open Zkc.Algebra.RingExpression (Expr)

abbrev F := ZMod 5

private def x : Term F := .input (.read 0 0 0)

/-- One fixed-height table: each row contributes `(x)` with a constant count
on channel 0, with the given locality. -/
private def contributor (count : F) (locality : Locality) : Table F where
  optional := false
  height := .fixed 2
  readModel := .finite
  groups := [⟨.witness, 1⟩]
  assertions := []
  fieldInteractions := [⟨0, locality, .all, [x], .constant count⟩]
  multisetInteractions := []

private def pair (locality : Locality) : Bundle F :=
  ⟨[contributor 1 locality, contributor (-1) locality]⟩

/-- Table 0 holds rows 1, 2 and table 1 holds rows 2, 1. -/
private def rows : Data F where
  config := ⟨fun _ => 0, fun _ _ _ _ => 0⟩
  statement := ⟨fun _ => true, fun _ => 0, fun _ => 0, fun _ _ _ _ => 0⟩
  witness := ⟨fun t _ _ r => if (t = 0) = (r = 0) then 1 else 2⟩

-- Global contributions of opposite sign at equal tuples cancel across tables.
example : FieldBalanced ((pair .global).fieldContributions rows) :=
  (fieldBalanced_iff _).mpr (by decide)

-- The same contributions in table-local groups never cancel across tables.
example : ¬ FieldBalanced ((pair (.inTable 0)).fieldContributions rows) := by
  rw [fieldBalanced_iff]
  decide

/-- With table 1 absent, its rows contribute nothing. -/
private def withoutSecond : Data F :=
  { rows with statement := { rows.statement with present := fun t => t = 0 } }

example : ¬ FieldBalanced ((pair .global).fieldContributions withoutSecond) := by
  rw [fieldBalanced_iff]
  decide

example : ((pair .global).fieldContributions withoutSecond).length = 2 ∧
    ((pair .global).fieldContributions rows).length = 4 := by
  decide

/-! Natural multiplicities: the field element `4 = -1` is a field weight, not
a natural count. -/

private def counted (side : Side) (bound : Nat) : Table F where
  optional := false
  height := .fixed 1
  readModel := .finite
  groups := [⟨.witness, 2⟩]
  assertions := []
  fieldInteractions := []
  multisetInteractions := [⟨0, .global, .all, side, [x], .input (.read 0 0 1), bound⟩]

private def countRows (push pull : F) : Data F where
  config := ⟨fun _ => 0, fun _ _ _ _ => 0⟩
  statement := ⟨fun _ => true, fun _ => 0, fun _ => 0, fun _ _ _ _ => 0⟩
  witness := ⟨fun t _ c _ => if c = 0 then 3 else if t = 0 then push else pull⟩

private def natural : F → Nat := ZMod.val

example : MultisetHolds natural
    ((⟨[counted .push 3, counted .pull 3]⟩ : Bundle F).multiplicities (countRows 2 2)) :=
  (multisetHolds_iff _ _).mpr (by decide)

example : ¬ MultisetHolds natural
    ((⟨[counted .push 3, counted .pull 3]⟩ : Bundle F).multiplicities (countRows 4 4)) := by
  rw [multisetHolds_iff]
  decide

example : ¬ MultisetHolds natural
    ((⟨[counted .push 3, counted .pull 3]⟩ : Bundle F).multiplicities (countRows 2 1)) := by
  rw [multisetHolds_iff]
  decide

/-! Signed finite and cyclic reads. -/

example : resolve .finite 4 0 (-1) = none ∧ resolve .cyclic 4 0 (-1) = some 3 ∧
    resolve .finite 4 3 1 = none ∧ resolve .cyclic 4 3 1 = some 0 ∧
    resolve .cyclic 3 1 5 = some 0 ∧ resolve .cyclic 0 0 0 = none := by
  decide

example : (Scope.interior 1 1).Active 4 1 ∧ (Scope.interior 1 1).Active 4 2 ∧
    ¬ (Scope.interior 1 1).Active 4 3 ∧ ¬ (Scope.interval 0 5).Defined 4 ∧
    Scope.last.Active 1 0 ∧ Scope.first.Active 1 0 := by
  decide

/-! The finite AIR recurrence of `Tests.RelationAIR` through the embedding. -/

private def step : AIR.Expr F 2 1 :=
  .add (.read 1 0) (.mul (.constant (-1)) (.add (.read 0 0) (.constant 1)))
private def boundary (j : Fin 2) : AIR.Expr F 2 1 :=
  .add (.read 0 0) (.mul (.constant (-1)) (.publicInput j))
private def constraints : List (AIR.Constraint F 2 1) :=
  [⟨.transition 1, step⟩, ⟨.first, boundary 0⟩, ⟨.last, boundary 1⟩]
private def trace : Fin 3 → Fin 1 → F := fun i _ => (![3, 4, 0] : Fin 3 → F) i

example : (FiniteAIR.bundle constraints 8).Holds natural
    (FiniteAIR.data (![3, 0] : Fin 2 → F) trace) := by
  rw [FiniteAIR.holds_iff constraints 8 2 (by decide)]
  change ∀ constraint ∈ constraints, constraint.Holds _ trace
  simp only [constraints, List.mem_cons, List.not_mem_nil, or_false]
  intro constraint h
  rcases h with rfl | rfl | rfl <;> unfold AIR.Constraint.Holds <;> decide

example : ¬ (FiniteAIR.bundle constraints 8).Holds natural
    (FiniteAIR.data (![3, 1] : Fin 2 → F) trace) := by
  rw [FiniteAIR.holds_iff constraints 8 2 (by decide)]
  intro holds
  have last := holds ⟨.last, boundary 1⟩ (by simp [constraints])
  revert last
  unfold AIR.Constraint.Holds
  decide

end Tests.RelationBundle
