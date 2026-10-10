import Zkc.Algebra.RingExpression.Reductions
import Tests.Checks
import Tools.DeclarationAudit

/-! Controls for independent finite map/reduction values and their admission
premises. These do not exercise the native parser, capture extraction or runtime. -/

set_option autoImplicit false

namespace Tests.RingExpressionReductions

open Zkc.Algebra.RingExpression
open Zkc.Algebra.FiniteVectors (dot limit product product_append product_replicate product_zero_of_mem)

private def multiply : Expr Int Nat := .mul (.input 0) (.input 1)
private def affine : Expr Int Nat :=
  .add (.input 0) (.mul (.add (.input 1) (.neg (.input 0))) (.input 2))

private def rows : List (Operand Int) := [.rows [2, 3], .rows [5, 7]]
private def captured : List (Operand Int) := rows ++ [.scalar 3, .rows [8, 9], .scalar 99]
private def mismatched : List (Operand Int) := rows ++ [.scalar 3, .rows [8], .scalar 99]

example : mapSum multiply rows = .ok 31 := by decide
example : mapProduct multiply rows = .ok 210 := by decide
example : mapSum affine captured = .ok 26 := by decide
example : mapProduct affine captured = .ok 165 := by decide

-- Exercise the general dot law with interleaved captures and an ignored row.
example : mapSum (.mul (.input 1) (.input 3))
      [.scalar 99, .rows [2, 3], .scalar 3, .rows [5, 7], .rows [8, 9]] =
    dot ([2, 3] : List Int) [5, 7] :=
  mapSum_mul_eq_dot _ 1 3 _ _ 2 rfl rfl (by decide)

-- Empty identities are obtained from admitted empty rows, even with captures.
example : mapSum affine [.rows [], .rows [], .scalar 3, .rows [], .scalar 99] = .ok 0 :=
  mapSum_empty _ _ (by decide) (by decide)
example : mapProduct affine [.rows [], .rows [], .scalar 3, .rows [], .scalar 99] = .ok 1 :=
  mapProduct_empty _ _ (by decide) (by decide)

-- The shape-code theorems retain bounds and signature admission explicitly.
example : mapSum affine mismatched = .error "vector-shape" :=
  mapSum_shape_code _ _ [2, 3] [8] (by decide) (by decide) (by decide)
    (by decide)
    (by decide)
example : mapProduct affine mismatched = .error "vector-shape" :=
  mapProduct_shape_code _ _ [2, 3] [8] (by decide) (by decide) (by decide)
    (by decide)
    (by decide)

-- Dropping an unused original row invalidates the unrestricted dot equation.
example : mapSum multiply mismatched ≠ dot ([2, 3] : List Int) [5, 7] := by decide
example : mapSum multiply [.rows [], .rows [], .rows [9], .scalar 3] ≠
    dot ([] : List Int) [] := by decide

-- Replacing shape admission by a truncating zip gives a value on a refused map.
example : mapSum multiply [.rows [2, 3], .rows [5]] ≠
    .ok ((([2, 3] : List Int).zip [5]).map (fun pair => pair.1 * pair.2)).sum := by decide
example : mapProduct multiply [.rows [2, 3], .rows [5]] ≠
    .ok ((([2, 3] : List Int).zip [5]).map (fun pair => pair.1 * pair.2)).prod := by decide

-- Limits precede shape agreement, even for an ignored row. The proof uses a
-- length hypothesis, without constructing a million-element control.
private theorem oversized_refuses (values : List Int) (large : limit < values.length) :
    map (.constant (1 : Int)) [.rows [], .rows values] =
      .error "vector-limit" := by
  have outside : ¬ values.length ≤ limit := Nat.not_le.mpr large
  simp [map, Expr.inputs, rowCount, Operand.rowLength, outside]

example (values : List Int) (large : limit < values.length) :
    mapSum (.constant (1 : Int)) [.rows [], .rows values] = .error "vector-limit" :=
  mapSum_error _ _ _ (oversized_refuses values large)
example (values : List Int) (large : limit < values.length) :
    mapProduct (.constant (1 : Int)) [.rows [], .rows values] = .error "vector-limit" :=
  mapProduct_error _ _ _ (oversized_refuses values large)

-- The native product companion model has its own bounded list contract.
example : product ([2, 3] ++ [5, 7] : List Int) = (do
    let left ← product [2, 3]
    let right ← product [5, 7]
    return left * right) := product_append _ _ (by decide)
example : product (List.replicate 4 (3 : Int)) = .ok 81 :=
  product_replicate _ _ (by decide)
example : product ([2, 0, 5] : List Int) = .ok 0 :=
  product_zero_of_mem _ (by decide) (by decide)

def run : IO Unit := do
  let checks ← Tests.Checks.start
  checks.holds (mapSum multiply rows == .ok 31) "sum of products is 31"
  checks.holds (mapProduct multiply rows == .ok 210) "product of products is 210"
  checks.holds (mapSum multiply captured == dot [2, 3] [5, 7])
    "dot value with an ignored row and captures"
  checks.holds (mapSum affine captured == .ok 26) "affine captured sum"
  checks.holds (mapProduct affine captured == .ok 165) "affine captured product"
  let empty : List (Operand Int) := [.rows [], .rows [], .scalar 3, .rows [], .scalar 99]
  checks.holds (mapSum affine empty == .ok 0) "admitted empty sum identity"
  checks.holds (mapProduct affine empty == .ok 1) "admitted empty product identity"
  checks.holds (mapSum affine mismatched == .error "vector-shape") "ignored row blocks sum"
  checks.holds (mapProduct affine mismatched == .error "vector-shape") "ignored row blocks product"
  checks.holds (mapSum multiply mismatched != dot [2, 3] [5, 7])
    "counterexample to erasing unused row guards before dot"
  checks.holds (mapSum multiply [.rows [], .rows [], .rows [9], .scalar 3] != dot [] [])
    "empty selected rows do not erase extra row guards"
  checks.holds (mapProduct (.constant (0 : Int)) [.rows [], .rows [9]] == .error "vector-shape")
    "constant expression does not erase any row guard"
  checks.holds (mapSum multiply [.rows [2, 3], .rows [5]] == .error "vector-shape")
    "unequal selected rows refuse sum"
  checks.holds (mapProduct multiply [.rows [2, 3], .rows [5]] == .error "vector-shape")
    "unequal selected rows refuse product"
  checks.holds (mapSum multiply [.scalar 2, .scalar 3] == .error "map-rows")
    "all-scalar sum has no row count"
  checks.holds (mapProduct (.constant (1 : Int)) [] == .error "map-rows")
    "absent rows are not an admitted empty product"
  checks.holds (mapSum (.input 4 : Expr Int Nat) [.rows [], .rows [9]] == .error "map-signature")
    "signature refusal precedes shape refusal for sum"
  checks.holds (mapProduct (.input 4 : Expr Int Nat) [.rows [], .rows [9]] == .error "map-signature")
    "signature refusal precedes shape refusal for product"
  checks.holds (product ([] : List Int) == .ok 1) "bounded product empty identity"
  checks.holds (product ([7] : List Int) == .ok 7) "bounded product singleton"
  checks.holds (product ([2, 3, 5] : List Int) == .ok 30) "bounded product every entry"
  checks.holds (product ([2, 0, 5] : List Int) == .ok 0) "bounded product zero factor"
  checks.holds (product (List.replicate 4 (3 : Int)) == .ok 81) "bounded repeated product"
  checks.finish "ring-expression reduction controls"

#eval run

end Tests.RingExpressionReductions

run_cmd
  Tools.DeclarationAudit.check [`Zkc.Algebra.RingExpression.Reductions, `Zkc.Algebra.FiniteVectors] "RING-EXPRESSION-REDUCTIONS-AUDIT-PASS" true

#print axioms Zkc.Algebra.RingExpression.mapSum_mul_eq_dot
