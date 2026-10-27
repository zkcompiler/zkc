module

public import Zkc.Executable.Relation

@[expose] public section

/-! Result schemas for the scalar helper ABI. These are representation facts
about typed helper results, independent of instruction normalization or execution. -/
set_option autoImplicit false
namespace Zkc.Executable
open Zkc.Construction Zkc.Source
variable {F G : Type}

/-- Scalar ABI values at their declared sorts. -/
@[reducible] def SortedValues (values : List (Value F G)) (sorts : List ValueSort) : Prop :=
  values.length = sorts.length ∧
    ∀ (index : Nat) (value : Value F G) (sort : ValueSort), values[index]? = some value →
      sorts[index]? = some sort → HasSort value sort


/-- A helper returns values of the declared result sorts. -/
def HelperSorted (table : Structured.Evaluation.Meanings F G Structured.closedInterface) (name : String)
    (declared : List ValueSort) : Prop :=
  ∀ (arguments values : List (Value F G)), callHelper table name arguments = .returned values →
    values.length = declared.length → SortedValues values declared


/-- A helper of a closed table returns values of its declared output types. -/
theorem helperSorted_of_outputs {table : Structured.Evaluation.Meanings F G Structured.closedInterface}
    {name : String} {declared : List ValueSort}
    (outputs : ∀ entry, table.find? (fun entry => entry.helper.name == name) = some entry →
      entry.helper.outputs.map .data = declared) :
    HelperSorted table name declared := by
  intro arguments values called lengths
  unfold callHelper at called
  cases found : table.find? (fun entry => entry.helper.name == name) with
  | none => simp [found] at called
  | some entry =>
      simp only [found] at called
      cases decoded : decodeValues entry.helper.inputs arguments with
      | none => simp [decoded] at called
      | some decodedValues =>
          simp only [decoded] at called
          cases invoked : closedOutcome (entry.invoke decodedValues) with
          | stopped => simp [invoked] at called
          | returned results =>
              simp only [invoked, PIR.Outcome.returned.injEq] at called
              subst called
              rw [← outputs entry found]
              exact ⟨by simp [Zkc.Construction.Uniform.encodeValues_length], encodeValues_sorted results⟩


end Zkc.Executable
