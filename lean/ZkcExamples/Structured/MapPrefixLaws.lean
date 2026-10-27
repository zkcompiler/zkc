module

public import ZkcExamples.Structured.MapFirstLaws
public import Zkc.Source.Structured.Laws

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! Exact finite-fold body equations and the reached-state restriction invariant.
The fold is the existing Source.Finite.fold over the existing helper invocation. -/
namespace ZkcExamples.Structured.MapPrefixLaws
open Zkc.Source Zkc.Source.Structured PrimitiveLibrary MapFirstLaws MapPrefixBodies
open Zkc.Polynomial.Multilinear (restrictValues restrictPrefixValues)
set_option smartUnfolding true

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

def prefixInputs (xs : List F) (dimension columns : Nat) (point : List F) :
    Values (assignment F G) [vector, .index, .index, vector] :=
  .cons xs (.cons dimension (.cons columns (.cons point .nil)))

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The actual finite domain admits the point before any callback. -/
theorem domain_admit (point : List F) :
    foldSpec.domain.admit (.cons point (.nil : Values (assignment F G) [])) =
      if point.length < indexLimit then .returned (point.map fun r => .cons r .nil)
      else .stopped .exhausted := by
  simp [foldSpec, DomainSpec.admit_elements, Collection.values, Values.get]

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem triple_eta {Value : Ty → Type} {a b c : Ty} (value : Values Value [a,b,c]) :
    Values.cons (value.get .here) (.cons (value.get (.there .here))
      (.cons (value.get (.there (.there .here))) .nil)) = value := by
  cases value with | cons a rest => cases rest with | cons b rest => cases rest with
    | cons c rest => cases rest; rfl

theorem step_body (table : Meanings F G) (xs : List F) (dimension columns : Nat) (r : F) :
    stepBody.denote (meaning F G table) (firstInputs xs dimension columns r).get =
      invoke table firstHelper (firstInputs xs dimension columns r) := by
  dsimp only [firstInputs, vector, scalar]
  rw [MapSourceExpansions.prefix_step]
  simp only [triple_eta, PIR.Process.bind_done]

theorem foldStep_body (table : Meanings F G) (xs : List F) (dimension columns : Nat)
    (r : F) (point : List F) :
    foldStepBody.denote (meaning F G table)
      (Values.cons xs (.cons dimension (.cons columns (.cons r (.cons point .nil))))).get =
      invoke table stepHelper (firstInputs xs dimension columns r) := by
  rw [MapSourceExpansions.prefix_foldStep]
  simp only [triple_eta, PIR.Process.bind_done]
  rfl

theorem prefix_body (table : Meanings F G) (xs : List F) (dimension columns : Nat) (point : List F) :
    prefixBody.denote (meaning F G table) (prefixInputs xs dimension columns point).get =
      invoke table foldWrapperHelper (prefixInputs xs dimension columns point) := by
  dsimp only [prefixInputs, vector]
  rw [MapSourceExpansions.prefix_prefix]
  simp only [triple_eta, PIR.Process.bind_done]

theorem foldWrapper_body (table : Meanings F G) {computation : String} (xs : List F) (dimension columns : Nat) (point : List F) :
    (MultilinearPrefixBodies.foldWrapperBody computation).denote (meaning F G table) (prefixInputs xs dimension columns point).get =
      invoke table (MultilinearPrefixBodies.foldHelper computation) (.cons point (.cons xs (.cons dimension (.cons columns .nil)))) := by
  dsimp only [prefixInputs, vector]
  rw [MapSourceExpansions.prefix_foldWrapper]
  simp only [triple_eta, PIR.Process.bind_done]

theorem fold_body (table : Meanings F G) (xs : List F) (dimension columns : Nat) (point : List F) :
    foldBody.denote (meaning F G table)
      (Values.cons point (.cons xs (.cons dimension (.cons columns .nil)))).get =
      Evaluation.denoteFold table foldSpec
        (.cons point (.cons xs (.cons dimension (.cons columns .nil)))) := by
  simp only [foldBody, MultilinearPrefixBodies.foldBody, Region.denote, meaning, Evaluation.meaning, Evaluation.operation,
    Operands.eval, Regions.denote, Values.get_cons, Environment.push, Environment.push]
  trans (Evaluation.denoteFold table foldSpec
    (.cons point (.cons xs (.cons dimension (.cons columns .nil))))).bind .done
  · congr 1
    funext result
    cases result with | cons a rest => cases rest with | cons b rest => cases rest with
      | cons c rest => cases rest; rfl
  · exact PIR.Process.bind_done _

/-- The invariant only requires the First law on shaped, representable reached states. -/
def FirstLaw (table : Meanings F G) : Prop :=
  ∀ (xs : List F) (dimension columns : Nat) (r : F),
    HasShape xs dimension columns → xs.length < indexLimit →
    invoke table firstHelper (firstInputs xs dimension columns r) =
      if 0 < dimension then .done (inputs (restrictValues xs r) (dimension - 1) columns)
      else .halt .reject

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- Ordered composition, including the first reached zero-dimension rejection. -/
theorem fold_restriction (table : Meanings F G) (law : FirstLaw table)
    (xs : List F) (dimension columns : Nat) (point : List F)
    (shape : HasShape xs dimension columns) (lengthBound : xs.length < indexLimit) :
    Finite.fold (fun (state : Values (assignment F G) [vector, .index, .index]) r =>
      invoke table firstHelper (state.append (.cons r .nil))) point (inputs xs dimension columns) =
      if point.length ≤ dimension then
        .done (inputs (restrictPrefixValues xs point) (dimension - point.length) columns)
      else .halt .reject := by
  induction point generalizing xs dimension with
  | nil => simp only [Finite.fold, List.length_nil, Nat.zero_le, ite_true,
      Nat.sub_zero, restrictPrefixValues, List.foldl_nil]
  | cons r point ih =>
    rw [Finite.fold]
    change (invoke table firstHelper (firstInputs xs dimension columns r)).bind _ = _
    rw [law xs dimension columns r shape lengthBound]
    by_cases positive : 0 < dimension
    · simp only [positive, ite_true, PIR.Process.bind]
      rw [ih (restrictValues xs r) (dimension - 1)
        (restrict_shape xs dimension columns r shape positive)
        (restrict_length_bound xs r lengthBound)]
      have order : point.length ≤ dimension - 1 ↔ (r :: point).length ≤ dimension := by
        simp only [List.length_cons]; omega
      have remaining : dimension - 1 - point.length = dimension - (r :: point).length := by
        simp only [List.length_cons]; omega
      simp only [order, remaining, restrictPrefixValues, List.foldl_cons]
    · have tooLong : ¬ (r :: point).length ≤ dimension := by
        simp only [List.length_cons]; omega
      simp only [positive, tooLong, ite_false, PIR.Process.bind]

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
    (prefixLaw : ∀ (xs : List F) (dimension columns : Nat) (point : List F),
      HasShape xs dimension columns → xs.length < indexLimit → point.length < indexLimit →
      invoke table prefixHelper (prefixInputs xs dimension columns point) =
        if point.length ≤ dimension then
          .done (inputs (restrictPrefixValues xs point) (dimension - point.length) columns)
        else .halt .reject)
    (exhaustedLaw : ∀ (xs : List F) (dimension columns : Nat) (point : List F),
      ¬ point.length < indexLimit →
      invoke table prefixHelper (prefixInputs xs dimension columns point) = .halt .exhausted)
    (xs : List F) (dimension columns : Nat) (point : List F)
    (lengthBound : xs.length < indexLimit) (dimensionBound : dimension < indexLimit)
    (columnsBound : columns < indexLimit) :
    wrapperBody.denote (meaning F G table) (prefixInputs xs dimension columns point).get =
      if HasShape xs dimension columns then
        if point.length < indexLimit then
          if point.length ≤ dimension then .done (inputs (restrictPrefixValues xs point) (dimension - point.length) columns)
          else .halt .reject
        else .halt .exhausted
      else .halt .reject := by
  dsimp only [prefixInputs, vector, scalar]
  rw [MapSourceExpansions.prefix_wrapper]
  have tableLaw := tableLaw xs dimension columns lengthBound dimensionBound columnsBound
  dsimp only [inputs, vector] at tableLaw
  rw [tableLaw]
  by_cases shape : HasShape xs dimension columns
  · simp only [shape, ite_true, PIR.Process.bind, Values.get]
    by_cases pointBound : point.length < indexLimit
    · simp only [pointBound, ite_true]
      have prefixLaw := prefixLaw xs dimension columns point shape lengthBound pointBound
      change (invoke table prefixHelper (prefixInputs xs dimension columns point)).bind _ = _
      rw [prefixLaw]
      by_cases fits : point.length ≤ dimension
      · simp only [fits, ite_true, PIR.Process.bind]
        change (invoke table valuesRealizationHelper
          (inputs (restrictPrefixValues xs point) (dimension - point.length) columns)).bind _ = _
        rw [valuesLaw]
        simp only [PIR.Process.bind, Values.get]
        change (invoke table variablesRealizationHelper
          (inputs (restrictPrefixValues xs point) (dimension - point.length) columns)).bind _ = _
        rw [variablesLaw]
        simp only [PIR.Process.bind, Values.get]
        change (invoke table widthRealizationHelper
          (inputs (restrictPrefixValues xs point) (dimension - point.length) columns)).bind _ = _
        rw [widthLaw]
        rfl
      · simp only [fits, ite_false, PIR.Process.bind]
    · have exhausted := exhaustedLaw xs dimension columns point pointBound
      change (invoke table prefixHelper (prefixInputs xs dimension columns point)).bind _ = _
      rw [exhausted]
      simp only [pointBound, ite_false, PIR.Process.bind]
  · simp only [shape, ite_false, PIR.Process.bind]


theorem entry_body (table : Meanings F G) (xs : List F) (dimension columns : Nat) (point : List F) :
    entryBody.denote (meaning F G table) (prefixInputs xs dimension columns point).get =
      invoke table wrapperHelper (prefixInputs xs dimension columns point) := by
  dsimp only [prefixInputs, vector, scalar]
  rw [MapSourceExpansions.prefix_entry]
  have eta : ∀ result : Values (assignment F G) [vector, .index, .index],
      Values.cons (result.get .here) (.cons (result.get (.there .here))
        (.cons (result.get (.there (.there .here))) .nil)) = result := by
    intro result
    cases result with | cons a rest => cases rest with | cons b rest => cases rest with
      | cons c rest => cases rest; rfl
  simp only [eta, PIR.Process.bind_done]

/-- Actual finite domain and callback ABI, including the full captured point. -/
def FoldStepLaw (table : Meanings F G) : Prop :=
  ∀ (xs : List F) (dimension columns : Nat) (r : F) (point : List F),
    invoke table foldStepHelper (.cons xs (.cons dimension (.cons columns (.cons r (.cons point .nil))))) =
      invoke table firstHelper (firstInputs xs dimension columns r)

/-- Reusable complete finite-body equation, not merely a fold over an ideal helper. -/
theorem finite_prefix_generic_body (table : Meanings F G) (first : FirstLaw table)
    (step : FoldStepLaw table) (xs : List F) (dimension columns : Nat) (point : List F)
    (shape : HasShape xs dimension columns) (vectorBound : xs.length < indexLimit) :
    foldBody.denote (meaning F G table)
      (Values.cons point (.cons xs (.cons dimension (.cons columns .nil)))).get =
      if point.length < indexLimit then
        if point.length ≤ dimension then
          .done (inputs (restrictPrefixValues xs point) (dimension - point.length) columns)
        else .halt .reject
      else .halt .exhausted := by
  rw [fold_body]
  change Evaluation.denoteFold table foldSpec
    ((Values.cons point Values.nil).append ((inputs xs dimension columns).append Values.nil)) = _
  rw [Evaluation.denoteFold_pack, domain_admit]
  split
  · simp only [Finite.admitThen, Finite.fold_map]
    have transition : (fun state r => Evaluation.foldTransition table foldSpec (.cons point .nil) .nil state (.cons r .nil)) =
        fun (state : Values (assignment F G) [vector, .index, .index]) r =>
          invoke table firstHelper (state.append (.cons r .nil)) := by
      funext state r
      cases state with | cons xs rest => cases rest with | cons n rest => cases rest with
        | cons w rest => cases rest; exact step xs n w r point
    rw [transition]
    exact fold_restriction table first xs dimension columns point shape vectorBound
  · rfl

end ZkcExamples.Structured.MapPrefixLaws
