module

public import Zkc.Realization.QueryWork

@[expose] public section
set_option autoImplicit false
namespace Tests.QueryWork
open Zkc.Realization.QueryWork

/-- Two occurrences of the same base are separate queries, not a set of
handles. Their answers and saved continuation instances are charged twice. -/
def repeated : Shape := .virtual [.base, .base]

theorem repeated_complete : Prefix (.enter repeated []) .completed 6 2 3 2 := by
  exact .advance (.advance (.respond (.advance (.advance (.respond
    (.advance (.advance (.nil _) (.children _ _ _)) (.base _)) (.base _))
      (.sibling _ _ _)) (.base _)) (.base _)) (.parent _)) .finish

theorem repeated_counts : repeated.nodes = 3 ∧ repeated.leaves = 2 := by decide

/-- The common accounting refutes deduplication, independently of answer
values and without assuming that the two requests have distinct handles. -/
theorem duplicate_charge_cannot_disappear :
    ¬ Prefix (.enter repeated []) .completed 6 1 3 2 := by
  intro finished
  have counted := finished.completed
  norm_num [repeated, Shape.leaves, leaves] at counted

/-- A zero-query virtual computes an answer without consulting a provider. -/
theorem empty_complete : Prefix (.enter (.virtual []) []) .completed 2 0 1 0 :=
  .advance (.advance (.nil _) (.empty _)) .finish

theorem empty_is_not_base :
    ¬ Prefix (.enter (.virtual []) []) .completed 2 1 1 0 := by
  intro finished
  have counted := finished.completed
  simp [Shape.leaves, leaves] at counted

/-- An incomplete return still owes the root's final phase transition. -/
theorem root_return_is_pending :
    Position.transitions (.returned []) = 1 ∧ Position.transitions .completed = 0 := by decide

theorem no_extra_base_answer :
    ¬ ∃ current, Prefix (.enter .base []) current 1 2 2 0 := by
  rintro ⟨current, execution⟩
  have bounded := execution.bounds
  norm_num [Shape.leaves] at bounded

/-- An unequal-arity tree keeps both the empty virtual and the duplicated
subtree. Neither is erased by the generated schedule's work accounting. -/
def nonuniform : Shape := .virtual [.virtual [], repeated, .base]

theorem nonuniform_counts : nonuniform.nodes = 6 ∧ nonuniform.leaves = 3 := by decide

#print axioms repeated_complete
#print axioms duplicate_charge_cannot_disappear
#print axioms no_extra_base_answer
#print axioms Prefix.bounds
#print axioms advance_progress
#print axioms advance_completed
#print axioms evaluation_completed
end Tests.QueryWork
