import Composition.Multilinear
import Examples.OpeningReduction.MultiplePoints

/-! Compare the independently authored table and virtual-expression models.
Build in the standalone Composition consumer; this is not a main dependency.
-/

set_option autoImplicit false

namespace OpeningComparison
open Examples.OpeningReduction

variable {F : Type}

def convert : {n : Nat} → Composition.Table F n → Table F n
  | 0, .leaf value => .scalar value
  | _ + 1, .fork lo hi => .node (convert lo) (convert hi)

variable [CommRing F]

theorem eval_convert {n : Nat} (table : Composition.Table F n) (point : Fin n → F) :
    (convert table).eval point = table.eval point := by
  induction table with
  | leaf value => rfl
  | fork lo hi il ih => simp only [convert, Table.eval, Composition.Table.eval, il, ih]

theorem equality_weight (n : Nat) (point query : Fin n → F) :
    (MultiplePoints.equalityTable n point).eval query = Composition.Table.eqWeight n point query := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [MultiplePoints.equalityTable, Table.eval, Table.eval_scale, ih, Composition.Table.eqWeight]
      ring

/-- The independent cubic engine and the specialized quadratic representation
denote the same two-point virtual expression in this common instance. -/
theorem same_virtual_expression {n : Nat} (table : Composition.Table F n)
    (alpha : F) (u v query : Fin n → F) :
    (MultiplePoints.reduction (convert table) alpha u v).eval query =
      (Zkc.Polynomial.Quadratic.add (table.weighted u)
        (Zkc.Polynomial.Quadratic.scale alpha (table.weighted v))).eval query := by
  simp only [MultiplePoints.reduction, Factors.eval, MultiplePoints.weight, Table.eval_add,
    Table.eval_scale, MultiplePoints.one_eval, mul_one, equality_weight, eval_convert,
    Zkc.Polynomial.Quadratic.eval_add, Zkc.Polynomial.Quadratic.eval_scale,
    Composition.Table.weighted_eval]
  ring

theorem same_boolean_sum {n : Nat} (table : Composition.Table F n)
    (alpha : F) (u v : Fin n → F) :
    (MultiplePoints.reduction (convert table) alpha u v).booleanSum =
      (Zkc.Polynomial.Quadratic.add (table.weighted u)
        (Zkc.Polynomial.Quadratic.scale alpha (table.weighted v))).booleanSum := by
  simp only [MultiplePoints.reduction_sum, eval_convert,
    Zkc.Polynomial.Quadratic.booleanSum_add, Zkc.Polynomial.Quadratic.booleanSum_scale,
    Composition.Table.weighted_sum]

end OpeningComparison
