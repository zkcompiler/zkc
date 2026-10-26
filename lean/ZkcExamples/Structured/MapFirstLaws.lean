module

public import ZkcExamples.Structured.MapSourceExpansions
public import ZkcExamples.Structured.PrimitiveLibrary
public import Zkc.Polynomial.Multilinear.ListRestriction

@[expose] public section

/-! Conditional equations for exact First bodies. Every helper premise is
supplied separately by each complete retained Payload in the table modules. -/
namespace ZkcExamples.Structured.MapFirstLaws
open Zkc.Source Zkc.Source.Structured PrimitiveLibrary MapFirstBodies
open Zkc.Polynomial.Multilinear (restrictValues)
set_option smartUnfolding true

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

def firstInputs (xs : List F) (dimension columns : Nat) (r : F) :
    Values (assignment F G) [vector, .index, .index, scalar] :=
  .cons xs (.cons dimension (.cons columns (.cons r .nil)))

/-- This premise names the full invocation and its ordered scalar formula. -/
def MapLaw (table : Meanings F G)
    (bindings : MultilinearCollectBodies.Bindings := MapFirstBodies.bindings) : Prop :=
  ∀ (low high : List F) (r : F), low.length = high.length → low.length < indexLimit →
    invoke table (MultilinearCollectBodies.mapHelper bindings) (.cons low (.cons high (.cons r .nil))) =
      .done (.cons (List.zipWith (fun lo hi => lo + (hi - lo) * r) low high) .nil)

def HalvesLaw (table : Meanings F G) : Prop :=
  ∀ (xs : List F) (dimension columns : Nat), dimension < indexLimit →
    invoke table halvesHelper (inputs xs dimension columns) =
      if 0 < dimension then
        if 0 < xs.length ∧ xs.length % 2 = 0 then
          .done (.cons (xs.take (xs.length / 2)) (.cons (xs.drop (xs.length / 2)) .nil))
        else .halt .refused
      else .halt .reject

/-- Split guard, exact two-row map, checked subtraction, and ordered triple. -/
theorem first_body {bindings : MultilinearCollectBodies.Bindings}
    (table : Meanings F G) (halves : HalvesLaw table) (map : MapLaw table bindings)
    (xs : List F) (dimension columns : Nat) (r : F)
    (shape : HasShape xs dimension columns) (lengthBound : xs.length < indexLimit) :
    (MultilinearCollectBodies.firstBody bindings).denote (meaning F G table) (firstInputs xs dimension columns r).get =
      if 0 < dimension then
        .done (inputs (restrictValues xs r) (dimension - 1) columns)
      else .halt .reject := by
  have dimensionBound : dimension < indexLimit :=
    Nat.lt_trans shape.2.1 (by decide +kernel)
  dsimp only [firstInputs, vector, scalar]
  rw [MapSourceExpansions.first_first]
  have splitLaw := halves xs dimension columns dimensionBound
  dsimp only [inputs, vector] at splitLaw
  rw [splitLaw]
  by_cases positive : 0 < dimension
  · have splitShape := shape.split_valid positive
    have shapes := shape.halves positive
    have sameLength : (xs.take (xs.length / 2)).length =
        (xs.drop (xs.length / 2)).length := shapes.1.length.trans shapes.2.1.length.symm
    have lowBound : (xs.take (xs.length / 2)).length < indexLimit :=
      Nat.lt_of_le_of_lt (by simp only [List.length_take]; exact Nat.min_le_right _ _) lengthBound
    have mapped := map (xs.take (xs.length / 2)) (xs.drop (xs.length / 2)) r sameLength lowBound
    have subBound : dimension - 1 < indexLimit := Nat.lt_of_le_of_lt (Nat.sub_le _ _) dimensionBound
    simp only [positive, splitShape, ite_true, PIR.Process.bind, Values.get, Primitive.evaluate, checkedIndices, dimensionBound,
      show 1 < indexLimit by decide +kernel, and_self, ite_true, primitiveOutcome]
    simp only [show 1 ≤ dimension by omega, ite_true, PIR.Process.bind, Values.get, inputs, restrictValues]
    change (invoke table (MultilinearCollectBodies.mapHelper bindings)
      (.cons (xs.take (xs.length / 2)) (.cons (xs.drop (xs.length / 2)) (.cons r .nil)))).bind
      (fun result => .done (inputs (result.get .here) (dimension - 1) columns)) =
      .done (inputs (restrictValues xs r) (dimension - 1) columns)
    rw [mapped]
    rfl
  · simp only [positive, ite_false, PIR.Process.bind]

omit [DecidableEq F] in
/-- The result keeps every column and removes exactly one leading row bit. -/
theorem restrict_shape (xs : List F) (dimension columns : Nat) (r : F)
    (shape : HasShape xs dimension columns) (positive : 0 < dimension) :
    HasShape (restrictValues xs r) (dimension - 1) columns := by
  have size : xs.length = 2 * (2 ^ (dimension - 1) * columns) := by
    have dim : dimension = dimension - 1 + 1 := by omega
    rw [shape.length]
    conv_lhs => rw [dim, Nat.pow_succ]
    simp only [Nat.mul_left_comm, Nat.mul_comm]
  exact hasShape_of_length _ _ _ shape.1 (by have := shape.2.1; omega)
    (Zkc.Polynomial.Multilinear.restrictValues_length xs r size)

omit [DecidableEq F] in
theorem restrict_length_bound (xs : List F) (r : F) (bound : xs.length < indexLimit) :
    (restrictValues xs r).length < indexLimit := by
  apply Nat.lt_of_le_of_lt _ bound
  simp only [restrictValues, List.length_zipWith, List.length_take, List.length_drop]
  exact le_trans (Nat.min_le_left _ _) (Nat.min_le_right _ _)

theorem wrapper_body (table : Meanings F G)
    (tableLaw : ∀ (xs : List F) (dimension columns : Nat),
      xs.length < indexLimit → dimension < indexLimit → columns < indexLimit →
      invoke table tableHelper (inputs xs dimension columns) =
        if HasShape xs dimension columns then .done (inputs xs dimension columns) else .halt .reject)
    (valuesLaw : ∀ (xs : List F) (dimension columns : Nat),
      invoke table valuesRealizationHelper (inputs xs dimension columns) = .done (.cons xs .nil))
    (variablesLaw : ∀ (xs : List F) (dimension columns : Nat),
      invoke table variablesRealizationHelper (inputs xs dimension columns) = .done (.cons dimension .nil))
    (widthLaw : ∀ (xs : List F) (dimension columns : Nat),
      invoke table widthRealizationHelper (inputs xs dimension columns) = .done (.cons columns .nil))
    (firstLaw : ∀ (xs : List F) (dimension columns : Nat) (r : F),
      HasShape xs dimension columns → xs.length < indexLimit →
      invoke table firstHelper (firstInputs xs dimension columns r) =
        if 0 < dimension then .done (inputs (restrictValues xs r) (dimension - 1) columns)
        else .halt .reject)
    (xs : List F) (dimension columns : Nat) (r : F)
    (lengthBound : xs.length < indexLimit) (dimensionBound : dimension < indexLimit)
    (columnsBound : columns < indexLimit) :
    wrapperBody.denote (meaning F G table) (firstInputs xs dimension columns r).get =
      if HasShape xs dimension columns then
        if 0 < dimension then .done (inputs (restrictValues xs r) (dimension - 1) columns)
        else .halt .reject
      else .halt .reject := by
  dsimp only [firstInputs, vector, scalar]
  rw [MapSourceExpansions.first_wrapper]
  have tableLaw := tableLaw xs dimension columns lengthBound dimensionBound columnsBound
  dsimp only [inputs, vector] at tableLaw
  rw [tableLaw]
  by_cases shape : HasShape xs dimension columns
  · simp only [shape, ite_true, PIR.Process.bind, Values.get]
    have firstLaw := firstLaw xs dimension columns r shape lengthBound
    change (invoke table firstHelper (firstInputs xs dimension columns r)).bind _ = _
    rw [firstLaw]
    by_cases positive : 0 < dimension
    · simp only [positive, ite_true, PIR.Process.bind]
      change (invoke table valuesRealizationHelper
        (inputs (restrictValues xs r) (dimension - 1) columns)).bind _ = _
      rw [valuesLaw]
      simp only [PIR.Process.bind, Values.get]
      change (invoke table variablesRealizationHelper
        (inputs (restrictValues xs r) (dimension - 1) columns)).bind _ = _
      rw [variablesLaw]
      simp only [PIR.Process.bind, Values.get]
      change (invoke table widthRealizationHelper
        (inputs (restrictValues xs r) (dimension - 1) columns)).bind _ = _
      rw [widthLaw]
      rfl
    · simp only [positive, ite_false, PIR.Process.bind]
  · simp only [shape, ite_false, PIR.Process.bind]


theorem entry_body (table : Meanings F G) (xs : List F) (dimension columns : Nat) (r : F) :
    entryBody.denote (meaning F G table) (firstInputs xs dimension columns r).get =
      invoke table wrapperHelper (firstInputs xs dimension columns r) := by
  dsimp only [firstInputs, vector, scalar]
  rw [MapSourceExpansions.first_entry]
  have eta : ∀ result : Values (assignment F G) [vector, .index, .index],
      Values.cons (result.get .here) (.cons (result.get (.there .here))
        (.cons (result.get (.there (.there .here))) .nil)) = result := by
    intro result
    cases result with | cons a rest => cases rest with | cons b rest => cases rest with
      | cons c rest => cases rest; rfl
  simp only [eta, PIR.Process.bind_done]

end ZkcExamples.Structured.MapFirstLaws
