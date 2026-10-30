module

public import Zkc.Protocols.Multilinear.Source.PrimitiveShapeBodies
public import Zkc.Source.Structured.PrimitiveLaws
public import Zkc.Source.RegionContracts
public import Zkc.Source.Structured.MultilinearAdmissionReference
public import Zkc.Protocols.Multilinear.Source.Bindings

@[expose] public section

/-! Conditional equations for the actual unchanged multilinear library bodies.
The reusable body laws require explicit helper equations; each consumer below
supplies them from its full admitted table and exact raw-body equality. -/

namespace ZkcExamples.Structured.PrimitiveLibrary
open Zkc.Source Zkc.Source.Structured
open PrimitiveShapeViews (lessBody lessHelper rowsBody rowsHelper shapeBody shapeHelper)

-- Local transparency options below elaborate dependent source-view aliases;
-- every resulting equation is still checked by the kernel.
-- Uniform source-reduction lists are reused across different checked bodies.

abbrev vector : Ty := .vector "bls12-381.fr"
abbrev scalar : Ty := .field "bls12-381.fr"

def inputs {F G : Type} (xs : List F) (dimension columns : Nat) :
    Values (assignment F G) [vector, .index, .index] :=
  .cons xs (.cons dimension (.cons columns .nil))

def boolResult {F G : Type} (value : Bool) : Values (assignment F G) [.boolean] :=
  .cons value .nil

def indexResult {F G : Type} (value : Nat) : Values (assignment F G) [.index] :=
  .cons value .nil

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- The source library guard's exact checked comparison. -/
theorem less_body (table : Meanings F G) (a b : Nat)
    (aBound : a < indexLimit) (bBound : b < indexLimit) :
    lessBody.denote (meaning F G table) (Values.cons a (.cons b .nil)).get =
      .done (boolResult (decide (a < b))) := by
  simp [lessBody, Region.denote, meaning, Evaluation.meaning, Evaluation.operation,
    Operands.eval, Regions.denote, Values.get_cons, Environment.prepend, Environment.push,
    SiteObservations.closed, SiteObservations.silent, PIR.Process.bind,
    Primitive.evaluate, primitiveOutcome, checkedIndices, aBound, bBound, boolResult]

/-- This assumption is discharged from the retained declaration, not its name. -/
def LessLaw (table : Meanings F G) : Prop :=
  ∀ a b, a < indexLimit → b < indexLimit →
    invoke table lessHelper (.cons a (.cons b .nil)) =
      .done (boolResult (decide (a < b)))

theorem power_bound (dimension : Nat) (bound : dimension < 64) :
    2 ^ dimension < indexLimit :=
  Nat.pow_lt_pow_right (by decide) bound

set_option backward.isDefEq.respectTransparency false in
/-- The rows loop doubles the entire current singleton state. Its indexed
invariant proves every intermediate multiplication is representable. -/
theorem rows_body (table : Meanings F G) (less : LessLaw table) (dimension : Nat)
    (bound : dimension < 64) :
    rowsBody.denote (meaning F G table) (indexResult dimension).get =
      .done (indexResult (2 ^ dimension)) := by
  rw [Evaluation.denote_meaning_eq_meaningOn]
  apply ReferenceLibrary.Multilinear.Admission.rows_body (ringModel F G) "bls12-381.fr"
    MultilinearSourceBindings.common table dimension bound
  simpa [ReferenceLibrary.Multilinear.Admission.boolResult, boolResult, bound,
    ReferenceLibrary.Multilinear.lessHelper, PrimitiveShapeViews.lessHelper, MultilinearSourceBindings.common] using
    less dimension 64 (Nat.lt_trans bound (by decide +kernel)) (by decide +kernel)



set_option backward.isDefEq.respectTransparency false in
/-- The checked source rejects its guard before creating or entering the loop. -/
theorem rows_rejected (table : Meanings F G) (less : LessLaw table) (dimension : Nat)
    (bound : dimension < indexLimit) (large : ¬ dimension < 64) :
    rowsBody.denote (meaning F G table) (indexResult dimension).get = .halt .reject := by
  have comparison := less dimension 64 bound (by decide +kernel)
  simp [rowsBody, Region.denote, meaning, Evaluation.meaning, Evaluation.operation,
    Operands.eval, Regions.denote, Values.get_cons, Environment.prepend,
    Environment.push, indexResult, SiteObservations.closed, SiteObservations.silent,
    PIR.Process.bind, Primitive.evaluate, primitiveOutcome, comparison, boolResult, large,
    Evaluation.invokeCallback, show 64 < indexLimit by decide +kernel]

def RowsLaw (table : Meanings F G) : Prop :=
  ∀ dimension, dimension < 64 →
    invoke table rowsHelper (indexResult dimension) = .done (indexResult (2 ^ dimension))

/-- Actual library predicate, with the authored short-circuit guards. -/
def HasShape {A : Type} (xs : List A) (dimension columns : Nat) : Prop :=
  0 < columns ∧ dimension < 64 ∧ xs.length % columns = 0 ∧ xs.length / columns = 2 ^ dimension

instance {A : Type} (xs : List A) (dimension columns : Nat) :
    Decidable (HasShape xs dimension columns) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))


/-- Row-major size consequence of the exact authored modulus/quotient checks. -/
theorem HasShape.length {A : Type} {xs : List A} {dimension columns : Nat}
    (shape : HasShape xs dimension columns) : xs.length = 2 ^ dimension * columns := by
  have equation := Nat.mod_add_div xs.length columns
  rw [shape.2.2.1, shape.2.2.2, Nat.zero_add, Nat.mul_comm] at equation
  exact equation.symm

/-- The size equation is sufficient for the authored shape predicate. -/
theorem hasShape_of_length {A : Type} (xs : List A) (dimension columns : Nat)
    (positive : 0 < columns) (small : dimension < 64)
    (length : xs.length = 2 ^ dimension * columns) : HasShape xs dimension columns := by
  refine ⟨positive, small, ?_, ?_⟩
  · simp [length]
  · simp [length, positive]

/-- A positive-dimensional shaped table has a positive even flattened length. -/
theorem HasShape.split_valid {A : Type} {xs : List A} {dimension columns : Nat}
    (shape : HasShape xs dimension columns) (positive : 0 < dimension) :
    0 < xs.length ∧ xs.length % 2 = 0 := by
  have dimensionEq : dimension = dimension - 1 + 1 := by omega
  have size : xs.length = (2 ^ (dimension - 1) * columns) * 2 := by
    rw [shape.length, dimensionEq, Nat.pow_succ]
    simp [Nat.mul_comm, Nat.mul_left_comm]
  constructor
  · rw [shape.length]
    exact Nat.mul_pos (Nat.pow_pos (by decide)) shape.1
  · simp [size]

/-- Exact ordered split lengths, with each result preserving the same columns. -/
theorem HasShape.halves {A : Type} {xs : List A} {dimension columns : Nat}
    (shape : HasShape xs dimension columns) (positive : 0 < dimension) :
    HasShape (xs.take (xs.length / 2)) (dimension - 1) columns ∧
      HasShape (xs.drop (xs.length / 2)) (dimension - 1) columns ∧
      xs.take (xs.length / 2) ++ xs.drop (xs.length / 2) = xs := by
  have dimensionEq : dimension = dimension - 1 + 1 := by omega
  have size : xs.length = (2 ^ (dimension - 1) * columns) * 2 := by
    rw [shape.length, dimensionEq, Nat.pow_succ]
    simp [Nat.mul_comm, Nat.mul_left_comm]
  have half : xs.length / 2 = 2 ^ (dimension - 1) * columns := by simp [size]
  have low : (xs.take (xs.length / 2)).length = 2 ^ (dimension - 1) * columns := by
    rw [List.length_take, Nat.min_eq_left (Nat.div_le_self _ _), half]
  have high : (xs.drop (xs.length / 2)).length = 2 ^ (dimension - 1) * columns := by
    rw [List.length_drop, half]
    omega
  exact ⟨hasShape_of_length _ _ _ shape.1 (by have := shape.2.1; omega) low,
    hasShape_of_length _ _ _ shape.1 (by have := shape.2.1; omega) high,
    List.take_append_drop _ _⟩

/-- Checked integer inputs, unlike arbitrary mathematical Nat, are u64 values. -/
theorem less_generic_body_all (table : Meanings F G) (a b : Nat) :
    lessBody.denote (meaning F G table) (Values.cons a (.cons b .nil)).get =
      if a < indexLimit ∧ b < indexLimit then .done (boolResult (decide (a < b)))
      else .halt .refused := by
  simp only [lessBody, Region.denote, meaning,
    Evaluation.meaning, Evaluation.operation, Operands.eval, Regions.denote,
    Values.get_cons, Environment.prepend, Environment.push,
    SiteObservations.closed, SiteObservations.silent, Primitive.evaluate, checkedIndices,
    PIR.Process.bind]
  split <;> rfl

def LessAllLaw (table : Meanings F G) : Prop :=
  ∀ a b : Nat, invoke table lessHelper (.cons a (.cons b .nil)) =
    if a < indexLimit ∧ b < indexLimit then .done (boolResult (decide (a < b)))
    else .halt .refused

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem lessAll_bounded (table : Meanings F G) (law : LessAllLaw table) : LessLaw table := by
  intro a b ha hb
  rw [law, ite_eq_left ⟨ha,hb⟩]


/-- A representable scalar table cannot encode 64 or more binary dimensions. -/
theorem dimension_bound_of_length {A : Type} (xs : List A) (dimension : Nat)
    (vectorBound : xs.length < indexLimit) (length : xs.length = 2 ^ dimension) :
    dimension < 64 := by
  by_contra large
  have power : 2 ^ 64 ≤ 2 ^ dimension := Nat.pow_le_pow_right (by decide) (by omega)
  rw [← length] at power
  exact (Nat.not_lt_of_ge power) vectorBound

/-- On representable scalar vectors, the success shape has no extra dimension premise. -/
theorem hasShape_iff_length {A : Type} (xs : List A) (dimension : Nat)
    (vectorBound : xs.length < indexLimit) :
    HasShape xs dimension 1 ↔ xs.length = 2 ^ dimension := by
  constructor
  · intro shape
    simpa only [Nat.mul_one] using shape.length
  · intro length
    exact hasShape_of_length xs dimension 1 (by decide)
      (dimension_bound_of_length xs dimension vectorBound length)
      (by simpa only [Nat.mul_one] using length)

end ZkcExamples.Structured.PrimitiveLibrary
