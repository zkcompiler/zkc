module

public import Zkc.Program.Execution
public import Std.WP
public import Mathlib.Basic.ENNReal.Basic

/-! The assertion carrier of proposition-valued readings.

`construct_region` keeps every goal in the shape `pre ⊑ wp program post stopped` and derives
intermediate bounds as lattice elements. Upstream VC generation treats an assertion lattice that is
syntactically `σ → Prop` specially: it introduces the state and turns the precondition into a
hypothesis, which removes that shape. `Truth` is a one-field structure around `Prop`, ordered by
implication. It is the same lattice as `Prop`, but it is opaque to that treatment, exactly as
`ENNReal` potentials are. It is a presentation carrier only: each reading built on it is connected
to an existing proposition-valued judgment, so endpoint statements do not mention it.
-/

@[expose] public section
open Lean.Order Std.WP

namespace ProtocolProof

/-- A proposition as an element of an assertion lattice. -/
structure Truth where
  holds : Prop

namespace Truth

/-- Implication order; the supremum of a family is the existence of a member that holds. -/
instance instCompleteLattice : Lean.Order.CompleteLattice Truth where
  rel left right := left.holds → right.holds
  rel_refl := id
  rel_trans first second := second ∘ first
  rel_antisymm := by
    rintro ⟨left⟩ ⟨right⟩ forward backward
    exact congrArg Truth.mk (propext ⟨forward, backward⟩)
  has_sup chosen := ⟨⟨∃ member, chosen member ∧ member.holds⟩, fun upper =>
    ⟨fun below member inside holds => below ⟨member, inside, holds⟩,
      fun above ⟨member, inside, holds⟩ => above member inside holds⟩⟩

theorem holds_mk (proposition : Prop) : (Truth.mk proposition).holds = proposition := rfl

theorem rel_iff (left right : Truth) : left ⊑ right ↔ (left.holds → right.holds) := Iff.rfl

/-- The order on state-indexed assertions is pointwise implication. -/
theorem rel_fun_iff {σ : Type} (left right : σ → Truth) :
    left ⊑ right ↔ ∀ state, (left state).holds → (right state).holds := Iff.rfl

/-- The order on doubly indexed assertions, such as a history and a remaining budget. -/
theorem rel_fun₂_iff {σ τ : Type} (left right : σ → τ → Truth) :
    left ⊑ right ↔ ∀ first second, (left first second).holds → (right first second).holds :=
  Iff.rfl

theorem holds_ite (condition : Prop) [Decidable condition] (yes no : Truth) :
    (if condition then yes else no).holds = if condition then yes.holds else no.holds := by
  split <;> rfl

theorem holds_dite (condition : Prop) [Decidable condition] (yes : condition → Truth)
    (no : ¬ condition → Truth) :
    (if h : condition then yes h else no h).holds =
      if h : condition then (yes h).holds else (no h).holds := by
  split <;> rfl

/-- Entailment between explicit propositions is implication. -/
theorem mk_rel_mk (left right : Prop) : (Truth.mk left ⊑ Truth.mk right) = (left → right) := rfl

/-- Entailment between explicit state-indexed propositions is pointwise implication. -/
theorem mk_rel_mk_fun {σ : Type} (left right : σ → Prop) :
    ((fun state => Truth.mk (left state)) ⊑ fun state => Truth.mk (right state)) =
      ∀ state, left state → right state := rfl

/-- The doubly indexed form, for a history and a remaining budget. -/
theorem mk_rel_mk_fun₂ {σ τ : Type} (left right : σ → τ → Prop) :
    ((fun first second => Truth.mk (left first second)) ⊑
        fun first second => Truth.mk (right first second)) =
      ∀ first second, left first second → right first second := rfl

end Truth

/-- An assertion on the absorbed transcript history. -/
abbrev Assert (E : Type) := List E → Truth

/-- The stop postcondition: an assertion for each explicit stop reason. -/
abbrev StopAssert (E : Type) := EStack⟨PIR.Stop → List E → Truth⟩

/-- A cost assertion: on the absorbed transcript history and the remaining credit. -/
abbrev CostAssert (E : Type) := List E → ENNReal → Truth

/-- The cost stop postcondition: a cost assertion for each explicit stop reason. -/
abbrev CostStopAssert (E : Type) := EStack⟨PIR.Stop → List E → ENNReal → Truth⟩

end ProtocolProof
