import Zkc.Algebra.RingExpression.Pointwise
import Zkc.Algebra.RingExpression.Sharing
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Ring
import Tests.Checks
import Tools.DeclarationAudit

/-! Executable controls for checked pointwise maps: the formulas of the native
map tests, shape refusals including an operand the formula never reads, fusion
of an inlined helper, hoisting of a scalar subformula, dead-node restriction of
an arena, and the off-domain counterexample that separates a formal product
from the interpolant of pointwise products. -/

set_option autoImplicit false

namespace Tests.PointwiseMap

open Zkc.Algebra.RingExpression

/-- `low + (high - low) * r`: inputs 0 and 1 rowwise, 2 the shared challenge. -/
private def affine : Expr Int Nat :=
  .add (.input 0) (.mul (.add (.input 1) (.neg (.input 0))) (.input 2))

/-- `square(a)` as the helper the residual inlines. -/
private def square : Expr Int Nat := .mul (.input 0) (.input 0)

/-- `(s + 1) * (square(a) - b) + s`; input 2 is a column the formula never reads. -/
private def residual : Expr Int Nat :=
  .add (.mul (.add (.input 3) (.constant 1)) (.add square (.neg (.input 1)))) (.input 3)

/-- The residual with the helper left as an outer input 0: the two-map form. -/
private def residualOuter : Expr Int Nat :=
  .add (.mul (.add (.input 3) (.constant 1)) (.add (.input 0) (.neg (.input 1)))) (.input 3)

/-- `s + 1`, ignoring the rowwise input 0: a scalar result broadcast to every row. -/
private def shifted : Expr Int Nat := .add (.input 1) (.constant 1)

private def a : List Int := [1, 2, 3]
private def b : List Int := [4, 5, 6]
private def c : List Int := [7, 8, 9]
private def operands : List (Operand Int) := [.rows a, .rows b, .rows c, .scalar 3]

-- The inner formulas of the fused residual: the helper at input 0, identities
-- elsewhere. The fusion law materializes every inner output as a column, so the
-- shared scalar reaches the outer map broadcast; the native two-map form keeps
-- it scalar. The rows are the same either way.
private def helpers (j : Nat) : Expr Int Nat := if j = 0 then square else .input j

-- Hoisting `s + 1`: the same residual with that subformula as a separate inner formula.
private def parts (j : Nat) : Expr Int Nat :=
  if j = 4 then .add (.input 3) (.constant 1) else .input j
private def hoisted (j : Nat) : Expr Int Nat :=
  if j = 4 then .constant 4 else .input j
private def residualSplit : Expr Int Nat :=
  .add (.mul (.input 4) (.add (.mul (.input 0) (.input 0)) (.neg (.input 1)))) (.input 3)

example : map affine [.rows a, .rows b, .scalar 3] = .ok [10, 11, 12] := by decide
example : map residual operands = .ok [-9, -1, 15] := by decide
example : map shifted [.rows a, .scalar 3] = .ok [4, 4, 4] := by decide
example : map affine [.rows [], .rows [], .scalar 3] = .ok [] := by decide
-- The unread third column still has to agree in length.
example : map residual [.rows a, .rows b, .rows [7, 8], .scalar 3] = .error "vector-shape" := by
  decide
example : map affine [.scalar 1, .scalar 2, .scalar 3] = .error "map-rows" := by decide
example : map affine [.rows a, .rows b] = .error "map-signature" := by decide

/-- The one-pass map of the composed formula equals the two-map form. -/
example : map residualOuter ((List.range 4).map fun j =>
    .rows ((map (helpers j) operands).toOption.getD [])) =
    map (residualOuter.substitute helpers) operands := by decide
example : residualOuter.substitute helpers = residual := by decide

/-- Dead scalar work: the residual arena with an unused product, its live
restriction, and the map between them. Node 2 is dead; live nodes are closed. -/
private def withDead : Arena Int Nat :=
  [.input 0, .input 3, .mul 1 1, .constant 1, .add 1 3, .mul 0 0, .input 1, .neg 6,
   .add 5 7, .mul 4 8, .add 9 1]
private def live (i : Nat) : Bool := i != 2
private def compact : Arena Int Nat :=
  [.input 0, .input 3, .constant 1, .add 1 2, .mul 0 0, .input 1, .neg 5, .add 4 6,
   .mul 3 7, .add 8 1]
private def image : List Nat := [0, 1, 0, 2, 3, 4, 5, 6, 7, 8, 9]
private def f (i : Nat) : Nat := image.getD i 0

example : withDead.WellFormed := by decide
example : withDead.Closed live := by decide
example : withDead.HomOn live f compact := by decide
-- The dead node has no image, so the unrestricted map is not a node map.
example : ¬ withDead.Hom f compact := by decide
-- Declaring the dead node live reinstates that obligation.
example : ¬ withDead.HomOn (fun _ => true) f compact := by decide
-- A live set that omits an operand of a live node is not closed.
example : ¬ withDead.Closed (fun i => i != 2 && i != 7) := by decide

section Counterexample

open Polynomial

private abbrev F := ZMod 17
private instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- `x * y`, the product arena of the native expression Sumcheck client. -/
private def product : Expr F Nat := .mul (.input 0) (.input 1)
private noncomputable def squares : Nat → F[X] := fun _ => X ^ 2
/-- The fourth roots of unity: a coset of size four with shift one. -/
private def four : Finset F := {1, 4, 16, 13}
/-- The eighth roots of unity. -/
private def eight : Finset F := {1, 2, 4, 8, 16, 15, 13, 9}

example : four.card = 4 := by decide
example : eight.card = 8 := by decide
example : product.degree (fun _ => 2) = 4 := by decide

private theorem product_polynomial : product.polynomial squares = X ^ 4 := by
  simp only [Expr.polynomial, Expr.map, Expr.eval, product, squares]
  ring

/-- On four nodes every pointwise product is one, so the interpolant is the
constant one: a different polynomial from the formal product `X^4`. -/
private theorem four_interpolant :
    Lagrange.interpolate four id (fun x => product.eval fun i => (squares i).eval x) = C 1 := by
  symm
  refine Lagrange.eq_interpolate_of_eval_eq _ (Set.injOn_id _) ?_ ?_
  · rw [degree_C one_ne_zero]
    show (0 : WithBot ℕ) < ((4 : ℕ) : WithBot ℕ)
    exact WithBot.coe_lt_coe.mpr (by norm_num)
  · intro x hx
    simp only [eval_C, product, Expr.eval, squares, eval_pow, eval_X, id]
    revert x
    decide

private theorem four_misses :
    Lagrange.interpolate four id (fun x => product.eval fun i => (squares i).eval x) ≠
      product.polynomial squares :=
  interpolate_ne_polynomial product squares four
    (by rw [product_polynomial, degree_X_pow]; decide)

/-- Below the node count the interpolant is the formal product. -/
private theorem eight_recovers :
    Lagrange.interpolate eight id (fun x => product.eval fun i => (squares i).eval x) =
      product.polynomial squares :=
  interpolate_polynomial product squares eight (fun _ => 2)
    (fun _ _ => natDegree_X_pow_le 2) (by decide)

end Counterexample

def run : IO Unit := do
  let checks ← Tests.Checks.start
  let fold := map affine [.rows a, .rows b, .scalar 3]
  checks.holds (fold == .ok (List.zipWith (fun low high => low + (high - low) * 3) a b))
    "fold rows computed one row at a time"
  checks.holds (map residual operands ==
      .ok (List.zipWith (fun x y => (3 + 1) * (x * x - y) + 3) a b))
    "residual with an unread column"
  checks.holds (map residual [.rows a, .rows b, .rows [7, 8], .scalar 3] == .error "vector-shape")
    "unread column of another length refuses"
  checks.holds (map residual [.rows a, .rows [4, 5], .rows c, .scalar 3] == .error "vector-shape")
    "read column of another length refuses"
  checks.holds (map residual [.rows [], .rows [], .rows [], .scalar 3] == .ok [])
    "empty columns succeed"
  let inner := fun j => (map (helpers j) operands).toOption.getD []
  checks.holds (inner 0 == [1, 4, 9] && inner 3 == [3, 3, 3]) "inner maps: helper and broadcast"
  checks.holds (map residualOuter ((List.range 4).map fun j => .rows (inner j)) ==
      map residual operands)
    "fused one-pass map equals the two-map form"
  checks.holds (map residualOuter [.rows (inner 0), .rows [4, 5], .rows c, .scalar 3] ==
      .error "vector-shape")
    "the two-map form refuses the same mismatch"
  checks.holds (map (residualSplit.substitute parts) operands ==
      map (residualSplit.substitute hoisted) operands)
    "hoisted scalar subformula gives the same rows"
  checks.holds ((residualSplit.substitute hoisted).inputs == [0, 0, 1, 3])
    "hoisting removes the scalar reads"
  let outputs := [10]
  checks.holds (outputs.map (withDead.unfold withDead.length) ==
      (outputs.map f).map (compact.unfold compact.length))
    "dead node removal keeps the output tree"
  checks.holds ((withDead.unfold withDead.length 10).map (Expr.eval fun i => ([1, 4, 7, 3] : List Int).getD i 0)
      == some (-9))
    "arena output agrees with the first mapped row"
  -- Coefficient objects of the two interpolants, evaluated by Horner's rule.
  let formal : List F := [0, 0, 0, 0, 1]
  let fourNodes : List F := [1, 4, 16, 13]
  checks.holds (fourNodes.all fun x =>
      Zkc.Algebra.FiniteVectors.evaluate formal x == Zkc.Algebra.FiniteVectors.evaluate [1] x)
    "formal product and constant one agree on the four nodes"
  checks.holds (Zkc.Algebra.FiniteVectors.evaluate formal 2 == 16 &&
      Zkc.Algebra.FiniteVectors.evaluate ([1] : List F) 2 == 1)
    "off the nodes the two polynomials differ"
  checks.finish "pointwise map controls"

#eval run

end Tests.PointwiseMap

run_cmd Tools.DeclarationAudit.check [`Zkc.Algebra.RingExpression.Pointwise] "POINTWISE-MAP-AUDIT-PASS"
