import Zkc.Algebra.RingExpression.Pointwise

/-! Finite sums and products after a checked pointwise map.

Every original operand participates in map admission before reduction. The dot
law compares indexed expression evaluation with the separate checked-zip model
in `FiniteVectors.dot`; it retains admission of unused rows and scalar operands.
These are independent list value laws, not native compiler, capture, failure-code,
resource or security correspondence. -/

set_option autoImplicit false

namespace Zkc.Algebra.RingExpression

open FiniteVectors (Result limit)

variable {F : Type} [CommRing F]

/-- Sum every row of a checked map, propagating its refusal before reduction. -/
def mapSum (e : Expr F Nat) (operands : List (Operand F)) : Result F :=
  match map e operands with
  | .error code => .error code
  | .ok values => .ok values.sum

/-- Multiply every row of a checked map; an admitted empty map has product one. -/
def mapProduct (e : Expr F Nat) (operands : List (Operand F)) : Result F :=
  match map e operands with
  | .error code => .error code
  | .ok values => .ok values.prod

/-- Successful sum denotation, retaining signature and full operand admission. -/
theorem mapSum_ok (e : Expr F Nat) (operands : List (Operand F)) (value : F)
    (success : mapSum e operands = .ok value) :
    (∀ j ∈ e.inputs, j < operands.length) ∧
      ∃ n, rowCount operands = .ok n ∧
        value = ((List.range n).map fun i => e.eval fun j => Operand.read operands j i).sum := by
  cases mapped : map e operands with
  | error code => simp [mapSum, mapped] at success
  | ok values =>
    have value_eq : values.sum = value := by simpa [mapSum, mapped] using success
    obtain ⟨signature, n, count, rfl⟩ := map_ok e operands values mapped
    exact ⟨signature, n, count, value_eq.symm⟩

/-- Successful product denotation, retaining signature and full operand admission. -/
theorem mapProduct_ok (e : Expr F Nat) (operands : List (Operand F)) (value : F)
    (success : mapProduct e operands = .ok value) :
    (∀ j ∈ e.inputs, j < operands.length) ∧
      ∃ n, rowCount operands = .ok n ∧
        value = ((List.range n).map fun i => e.eval fun j => Operand.read operands j i).prod := by
  cases mapped : map e operands with
  | error code => simp [mapProduct, mapped] at success
  | ok values =>
    have value_eq : values.prod = value := by simpa [mapProduct, mapped] using success
    obtain ⟨signature, n, count, rfl⟩ := map_ok e operands values mapped
    exact ⟨signature, n, count, value_eq.symm⟩

theorem mapSum_eq (e : Expr F Nat) (operands : List (Operand F)) (n : Nat)
    (signature : ∀ j ∈ e.inputs, j < operands.length)
    (count : rowCount operands = .ok n) :
    mapSum e operands =
      .ok (((List.range n).map fun i => e.eval fun j => Operand.read operands j i).sum) := by
  rw [mapSum, map_eq e operands n signature count]

theorem mapProduct_eq (e : Expr F Nat) (operands : List (Operand F)) (n : Nat)
    (signature : ∀ j ∈ e.inputs, j < operands.length)
    (count : rowCount operands = .ok n) :
    mapProduct e operands =
      .ok (((List.range n).map fun i => e.eval fun j => Operand.read operands j i).prod) := by
  rw [mapProduct, map_eq e operands n signature count]

/-- Empty identities require admitted zero-length rows, not merely no inputs. -/
theorem mapSum_empty (e : Expr F Nat) (operands : List (Operand F))
    (signature : ∀ j ∈ e.inputs, j < operands.length)
    (count : rowCount operands = .ok 0) : mapSum e operands = .ok 0 := by
  simpa using mapSum_eq e operands 0 signature count

theorem mapProduct_empty (e : Expr F Nat) (operands : List (Operand F))
    (signature : ∀ j ∈ e.inputs, j < operands.length)
    (count : rowCount operands = .ok 0) : mapProduct e operands = .ok 1 := by
  simpa using mapProduct_eq e operands 0 signature count

/-- Any map refusal is propagated verbatim within this model. -/
theorem mapSum_error (e : Expr F Nat) (operands : List (Operand F)) (code : String)
    (refused : map e operands = .error code) : mapSum e operands = .error code := by
  simp [mapSum, refused]

theorem mapProduct_error (e : Expr F Nat) (operands : List (Operand F)) (code : String)
    (refused : map e operands = .error code) : mapProduct e operands = .error code := by
  simp [mapProduct, refused]

/-- Mismatched rows prevent success even when neither row occurs in the formula. -/
theorem mapSum_shape (e : Expr F Nat) (operands : List (Operand F)) (left right : List F)
    (hl : .rows left ∈ operands) (hr : .rows right ∈ operands)
    (ne : left.length ≠ right.length) (value : F) : mapSum e operands ≠ .ok value := by
  intro success
  obtain ⟨_, n, count, _⟩ := mapSum_ok e operands value success
  exact rowCount_shape operands left right hl hr ne n count

theorem mapProduct_shape (e : Expr F Nat) (operands : List (Operand F)) (left right : List F)
    (hl : .rows left ∈ operands) (hr : .rows right ∈ operands)
    (ne : left.length ≠ right.length) (value : F) : mapProduct e operands ≠ .ok value := by
  intro success
  obtain ⟨_, n, count, _⟩ := mapProduct_ok e operands value success
  exact rowCount_shape operands left right hl hr ne n count

/-- The specific shape code requires the earlier signature and limit checks. -/
theorem mapSum_shape_code (e : Expr F Nat) (operands : List (Operand F)) (left right : List F)
    (hl : .rows left ∈ operands) (hr : .rows right ∈ operands)
    (ne : left.length ≠ right.length)
    (signature : ∀ j ∈ e.inputs, j < operands.length)
    (bounded : (operands.filterMap Operand.rowLength).all (· ≤ limit) = true) :
    mapSum e operands = .error "vector-shape" :=
  mapSum_error e operands _ (map_shape_code e operands left right hl hr ne signature bounded)

theorem mapProduct_shape_code (e : Expr F Nat) (operands : List (Operand F)) (left right : List F)
    (hl : .rows left ∈ operands) (hr : .rows right ∈ operands)
    (ne : left.length ≠ right.length)
    (signature : ∀ j ∈ e.inputs, j < operands.length)
    (bounded : (operands.filterMap Operand.rowLength).all (· ≤ limit) = true) :
    mapProduct e operands = .error "vector-shape" :=
  mapProduct_error e operands _ (map_shape_code e operands left right hl hr ne signature bounded)

/-- Multiplication followed by sum has the value of the independent checked dot.
The row count admits the entire original operand list, including unused rows
and scalars; the two selected operands alone are not a sufficient premise. -/
theorem mapSum_mul_eq_dot (operands : List (Operand F)) (leftIndex rightIndex : Nat)
    (left right : List F) (n : Nat)
    (leftOperand : operands[leftIndex]? = some (.rows left))
    (rightOperand : operands[rightIndex]? = some (.rows right))
    (count : rowCount operands = .ok n) :
    mapSum (.mul (.input leftIndex) (.input rightIndex)) operands =
      FiniteVectors.dot left right := by
  obtain ⟨bound, _, agree⟩ := rowCount_ok operands n count
  have leftLength : left.length = n := agree left (List.mem_of_getElem? leftOperand)
  have rightLength : right.length = n := agree right (List.mem_of_getElem? rightOperand)
  have leftInside : leftIndex < operands.length := (List.getElem?_eq_some_iff.mp leftOperand).1
  have rightInside : rightIndex < operands.length := (List.getElem?_eq_some_iff.mp rightOperand).1
  have signature : ∀ j ∈ (Expr.mul (.input leftIndex) (.input rightIndex) : Expr F Nat).inputs,
      j < operands.length := by
    intro j hj
    simp [Expr.inputs] at hj
    rcases hj with rfl | rfl
    · exact leftInside
    · exact rightInside
  have rows : (List.range n).map (fun i =>
      (Expr.mul (.input leftIndex) (.input rightIndex) : Expr F Nat).eval
        fun j => Operand.read operands j i) =
      (left.zip right).map (fun pair => pair.1 * pair.2) := by
    apply List.ext_getElem (by simp [leftLength, rightLength])
    intro i inside _
    simp only [List.length_map, List.length_range] at inside
    simp only [List.getElem_map, List.getElem_range, Expr.eval, List.getElem_zip]
    rw [Operand.read_rows operands leftIndex i left leftOperand (by omega),
      Operand.read_rows operands rightIndex i right rightOperand (by omega)]
  rw [mapSum_eq _ operands n signature count, rows]
  simp [FiniteVectors.dot, FiniteVectors.zipExact, FiniteVectors.bounded,
    FiniteVectors.check, leftLength, rightLength, bound]
  rfl

end Zkc.Algebra.RingExpression
