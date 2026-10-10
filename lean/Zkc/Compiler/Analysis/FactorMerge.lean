import Zkc.Modules.FactorContract

/-! Conservative merging of conjunctive factor facts and available coordinates.

The result retains the left list's order and multiplicity. A retained assertion
must hold on either incoming alternative. This is not the union used for a
cover of possible phases, nor a claim of the most precise semantic merge.
-/

set_option autoImplicit false

namespace Zkc.Compiler.FactorMerge

open Zkc.Modules.Factor Zkc.Modules.FactorState

variable {A K : Type} [DecidableEq A]

def common (left right : List A) : List A :=
  left.filter (fun a => decide (a ∈ right))

theorem mem_common {left right : List A} {a : A} :
    a ∈ common left right ↔ a ∈ left ∧ a ∈ right := by
  simp [common]

theorem common_length (left right : List A) :
    (common left right).length ≤ left.length := List.length_filter_le _ _

/-- A conjunction of retained assertions is valid on either entry alternative. -/
theorem common_sound (P : A → Prop) (left right : List A)
    (valid : (∀ a ∈ left, P a) ∨ (∀ a ∈ right, P a)) :
    ∀ a ∈ common left right, P a := by
  intro a member
  have both := mem_common.mp member
  rcases valid with first | second
  · exact first a both.1
  · exact second a both.2

theorem common_valid (state : State K) (left right : List Fact)
    (valid : Valid state left ∨ Valid state right) :
    Valid state (common left right) := common_sound (Means state) left right valid

theorem common_known (state : World K) (left right : List Nat)
    (known : Known state left ∨ Known state right) :
    Known state (common left right) := common_sound (fun i => i ∈ state.known) left right known

def facts (summaries : Bool → Summary) (before : List Fact) : List Fact :=
  common (nextFacts (summaries true) before) (nextFacts (summaries false) before)

def available (summaries : Bool → Summary) (before : List Nat) : List Nat :=
  common (nextKnown (summaries true) before) (nextKnown (summaries false) before)

theorem facts_valid (summaries : Bool → Summary) (before after : World K)
    (outcome : Bool) (law : Justifies (summaries outcome) before after)
    (old : List Fact) (valid : Valid before.values old) :
    Valid after.values (facts summaries old) := by
  apply common_valid
  have transferred := nextFacts_valid _ before after old law valid
  cases outcome
  · exact Or.inr transferred
  · exact Or.inl transferred

theorem available_known (summaries : Bool → Summary) (before after : World K)
    (outcome : Bool) (law : Justifies (summaries outcome) before after)
    (old : List Nat) (known : Known before old) :
    Known after (available summaries old) := by
  apply common_known
  have transferred := nextKnown_sound _ before after old law known
  cases outcome
  · exact Or.inr transferred
  · exact Or.inl transferred

end Zkc.Compiler.FactorMerge
