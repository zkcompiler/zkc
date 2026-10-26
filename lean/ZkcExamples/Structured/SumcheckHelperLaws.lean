module

public import ZkcExamples.Structured.SumcheckHelperExpansions
public import ZkcExamples.Structured.MapPrefixContracts

@[expose] public section
namespace ZkcExamples.Structured.SumcheckHelperLaws
open Zkc.Source Zkc.Source.Structured PrimitiveLibrary MapPrefixBodies MapFirstLaws
open SumcheckHelperBodies MapPrefixLaws
open Zkc.Polynomial.Multilinear (restrictPrefixValues)

variable {bindings : MultilinearPrefixBodies.Bindings}
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- Arbitrary raw triples: no shape, width, or vector-length premise is smuggled in. -/
theorem sums_generic_body (table : Meanings F G) (halves : HalvesLaw table)
    (xs : List F) (dimension columns : Nat) (dimensionBound : dimension < indexLimit) :
    sumsBody.denote (meaning F G table) (inputs xs dimension columns).get =
      if 0 < dimension then
        if 0 < xs.length ∧ xs.length % 2 = 0 then
          .done (messageResult (xs.take (xs.length / 2)).sum (xs.drop (xs.length / 2)).sum)
        else .halt .refused
      else .halt .reject := by
  rw [sums_expansion, halves xs dimension columns dimensionBound]
  split
  · split <;> rfl
  · rfl

/-- Any actual split stop suppresses both subsequent sums. -/
theorem sums_stopped (table : Meanings F G) (xs : List F) (dimension columns : Nat)
    (reason : PIR.Stop)
    (stopped : invoke table halvesHelper (inputs xs dimension columns) = .halt reason) :
    sumsBody.denote (meaning F G table) (inputs xs dimension columns).get = .halt reason := by
  rw [sums_expansion, stopped]; rfl

/-- A shaped positive-dimensional input returns the two ordered half sums. -/
theorem sums_shaped (table : Meanings F G) (halves : HalvesLaw table)
    (xs : List F) (dimension columns : Nat) (shape : HasShape xs dimension columns)
    (positive : 0 < dimension) :
    sumsBody.denote (meaning F G table) (inputs xs dimension columns).get =
      .done (messageResult (xs.take (xs.length / 2)).sum (xs.drop (xs.length / 2)).sum) := by
  rw [sums_generic_body table halves xs dimension columns
    (Nat.lt_trans shape.2.1 (by decide +kernel)), ite_eq_left positive, ite_eq_left (shape.split_valid positive)]

/-- Complete constructor → finite prefix → realization → sum → equality equation. -/
theorem checkTable_generic_body (table : Meanings F G) (laws : MapPrefixContracts.Laws table bindings)
    (xs point : List F) (claim : F) (vectorBound : xs.length < indexLimit)
    (pointBound : point.length < indexLimit) :
    (checkTableBody bindings).denote (meaning F G table) (checkInputs xs point claim).get =
      if HasShape xs point.length 1 then
        .done (boolResult (decide ((restrictPrefixValues xs point).sum = claim)))
      else .halt .reject := by
  rw [checkTable_expansion, ite_eq_left pointBound,
    laws.tableLaw xs point.length 1 vectorBound pointBound (by decide +kernel)]
  by_cases shape : HasShape xs point.length 1
  · simp only [shape, ite_true, PIR.Process.bind]
    change (invoke table prefixHelper (prefixInputs xs point.length 1 point)).bind _ = _
    rw [laws.fixPrefix xs point.length 1 point shape vectorBound pointBound]
    simp only [Nat.le_refl, ite_true, Nat.sub_self, PIR.Process.bind]
    rw [laws.values]
    rfl
  · simp only [shape, ite_false, PIR.Process.bind]

/-- No semantic premise about check_table is needed for the malformed branch. -/
theorem check_malformed_generic_body (table : Meanings F G)
    (shapeLaw : ∀ (xs : List F) (dimension columns : Nat),
      xs.length < indexLimit → dimension < indexLimit → columns < indexLimit →
      invoke table shapeHelper (inputs xs dimension columns) =
        .done (boolResult (decide (HasShape xs dimension columns))))
    (xs point : List F) (claim : F) (vectorBound : xs.length < indexLimit)
    (pointBound : point.length < indexLimit) (malformed : ¬ HasShape xs point.length 1) :
    checkBody.denote (meaning F G table) (checkInputs xs point claim).get = .done (boolResult false) := by
  rw [check_expansion, ite_eq_left pointBound,
    shapeLaw xs point.length 1 vectorBound pointBound (by decide +kernel)]
  simp only [boolResult, PIR.Process.bind, Values.get, decide_eq_false malformed, Bool.false_eq_true, ite_false]

/-- The only callback premise is an exact body equation; no intended result is assumed. -/
theorem check_generic_body (table : Meanings F G) (laws : MapPrefixContracts.Laws table bindings)
    (callback : ∀ (xs point : List F) (claim : F),
      invoke table checkTableHelper (checkInputs xs point claim) =
        (checkTableBody bindings).denote (meaning F G table) (checkInputs xs point claim).get)
    (xs point : List F) (claim : F) (vectorBound : xs.length < indexLimit)
    (pointBound : point.length < indexLimit) :
    checkBody.denote (meaning F G table) (checkInputs xs point claim).get =
      .done (boolResult (decide (HasShape xs point.length 1 ∧
        (restrictPrefixValues xs point).sum = claim))) := by
  rw [check_expansion, ite_eq_left pointBound,
    laws.shape xs point.length 1 vectorBound pointBound (by decide +kernel)]
  by_cases shape : HasShape xs point.length 1
  · simp only [boolResult, PIR.Process.bind, Values.get, decide_eq_true shape, ite_true]
    rw [callback, checkTable_generic_body table laws xs point claim vectorBound pointBound, ite_eq_left shape]
    simp only [shape, true_and, boolResult]
  · simp only [boolResult, PIR.Process.bind, Values.get,
      shape, false_and, decide_false, Bool.false_eq_true, ite_false]

/-- Point-length exhaustion occurs before shape or constructor in both bodies. -/
theorem check_point_exhausted (table : Meanings F G) (xs point : List F) (claim : F)
    (overflow : ¬ point.length < indexLimit) :
    checkBody.denote (meaning F G table) (checkInputs xs point claim).get = .halt .exhausted ∧
    (checkTableBody bindings).denote (meaning F G table) (checkInputs xs point claim).get = .halt .exhausted := by
  simp only [check_expansion, checkTable_expansion, ite_eq_right overflow, and_self]

/-- Exact source body association, not an assumption of a helper's intended result. -/
def HalvesBodyLaw (table : Meanings F G) : Prop :=
  ∀ (xs : List F) (n w : Nat), invoke table halvesHelper (inputs xs n w) =
    halvesBody.denote (meaning F G table) (inputs xs n w).get

def ShapeBodyLaw (table : Meanings F G) : Prop :=
  ∀ (xs : List F) (n w : Nat), invoke table shapeHelper (inputs xs n w) =
    shapeBody.denote (meaning F G table) (inputs xs n w).get

/-- Full generic raw-triple contract, including checked-index refusal. -/
theorem sums_generic_body_all (table : Meanings F G) (less : LessAllLaw table)
    (association : HalvesBodyLaw table) (xs : List F) (dimension columns : Nat) :
    sumsBody.denote (meaning F G table) (inputs xs dimension columns).get =
      if dimension < indexLimit then
        if 0 < dimension then
          if 0 < xs.length ∧ xs.length % 2 = 0 then
            .done (messageResult (xs.take (xs.length / 2)).sum (xs.drop (xs.length / 2)).sum)
          else .halt .refused
        else .halt .reject
      else .halt .refused := by
  rw [sums_expansion, association, halves_generic_body_all table less]
  split
  · split
    · split <;> rfl
    · rfl
  · rfl

/-- Too-large dimensions return false before reading xs.length; no vector bound is needed. -/
theorem check_large_dimension_generic_body (table : Meanings F G) (less : LessLaw table)
    (association : ShapeBodyLaw table) (xs point : List F) (claim : F)
    (pointBound : point.length < indexLimit) (large : ¬ point.length < 64) :
    checkBody.denote (meaning F G table) (checkInputs xs point claim).get = .done (boolResult false) := by
  rw [check_expansion, ite_eq_left pointBound, association,
    shape_large_dimension table less xs point.length 1 (by decide) (by decide +kernel) pointBound large]
  rfl

/-- A small dimension reaches the independent vector-length check, which may exhaust. -/
theorem check_vector_exhausted_generic_body (table : Meanings F G) (less : LessLaw table)
    (association : ShapeBodyLaw table) (xs point : List F) (claim : F)
    (small : point.length < 64) (vectorOverflow : ¬ xs.length < indexLimit) :
    checkBody.denote (meaning F G table) (checkInputs xs point claim).get = .halt .exhausted := by
  have pointBound : point.length < indexLimit := Nat.lt_trans small (by decide +kernel)
  rw [check_expansion, ite_eq_left pointBound, association,
    shape_length_exhausted table less xs point.length 1 (by decide) (by decide +kernel) small vectorOverflow]
  rfl

/-- A constructor stop suppresses prefix, projection, sum and equality. -/
theorem checkTable_constructor_stopped (table : Meanings F G) (xs point : List F)
    (claim : F) (pointBound : point.length < indexLimit) (reason : PIR.Stop)
    (stopped : invoke table tableHelper (inputs xs point.length 1) = .halt reason) :
    (checkTableBody bindings).denote (meaning F G table) (checkInputs xs point claim).get = .halt reason := by
  rw [checkTable_expansion, ite_eq_left pointBound, stopped]
  rfl


theorem empty_body (table : Meanings F G) :
    emptyBody.denote (meaning F G table) Values.nil.get = .done (.cons [] .nil) := rfl

/-- The actual append body has no allocation or checked-length premise. -/
theorem append_body (table : Meanings F G) (xs : List F) (x : F) :
    appendBody.denote (meaning F G table) (Values.cons xs (.cons x .nil)).get =
      .done (.cons (xs ++ [x]) .nil) := rfl

/-- A later length operation can exhaust after append itself succeeds. -/
theorem append_then_length (table : Meanings F G) (xs : List F) (x : F) :
    (appendBody.denote (meaning F G table) (Values.cons xs (.cons x .nil)).get).bind
      (fun result => Evaluation.operation SiteObservations.closed table
        (.exec (.vectorLength "bls12-381.fr")) result .nil) =
      if (xs ++ [x]).length < indexLimit then .done (.cons (xs ++ [x]).length .nil)
      else .halt .exhausted := by
  rw [append_body]
  simp only [PIR.Process.bind, Evaluation.operation, Primitive.evaluate]
  split <;> rfl

/-- Pure component arithmetic preserves independent absent operands. -/
theorem scalar_add_components (tables : Evaluation.ComponentTables F G closedInterface)
    (left right : Option F) :
    Evaluation.componentOperation SiteObservations.closed tables (.fieldAdd "bls12-381.fr")
      (.cons left (.cons right .nil)) .nil =
      .done (.cons (Option.map₂ (· + ·) left right) .nil) := by
  cases left <;> cases right <;> rfl

/-- The primitive sum requires its operand when that operation is reached. -/
theorem vector_sum_absent (tables : Evaluation.ComponentTables F G closedInterface) :
    Evaluation.componentOperation SiteObservations.closed tables (.exec (.vectorSum "bls12-381.fr"))
      (.cons none .nil) .nil = .halt .incomplete := rfl

end ZkcExamples.Structured.SumcheckHelperLaws
