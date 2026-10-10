import Zkc.Relation.AIR.ProductConnection
import Zkc.Relation.AIR.Polynomial
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false

namespace Tests.AIRProductConnection

open Polynomial Zkc.Relation.AIR Zkc.Relation.AIR.ProductConnection
open Zkc.Algebra.MultisetFingerprint

private abbrev F := ZMod 7
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

-- Statement index 0 is the challenge and 1 the terminal; column 0 holds values
-- and column 1 the accumulator.
private abbrev accumulator : List (Constraint F 2 2) := constraints 0 1 0 1

-- Honest, permuted columns: challenge 5 gives terminal 3 on both sides.
private def permutedLeft : Fin 3 → Fin 2 → F := ![![1, 4], ![2, 5], ![3, 3]]
private def permutedRight : Fin 3 → Fin 2 → F := ![![3, 2], ![1, 1], ![2, 3]]
private def permutedStatement : Fin 2 → F := ![5, 3]

private theorem permutedLeft_holds :
    (family accumulator 2).holds permutedStatement permutedLeft :=
  holds_of_prefix 0 1 0 1 2 _ _ (by decide) (by rw [eval_ofMultiset_rowValues]; decide)

private theorem permutedRight_holds :
    (family accumulator 2).holds permutedStatement permutedRight :=
  holds_of_prefix 0 1 0 1 2 _ _ (by decide) (by rw [eval_ofMultiset_rowValues]; decide)

-- Both honest traces above share one statement, so completeness publishes the
-- same terminal; the original relation holds independently of that challenge.
example : rowValues Finset.univ (fun row => permutedLeft row 0) =
    rowValues Finset.univ (fun row => permutedRight row 0) := by
  decide

-- A challenge chosen after the values are known can connect different
-- multisets: `{0, 1}` and `{0, 2}` both reach terminal 0 at challenge 0. The
-- theorem places that challenge among the roots of the nonzero difference.
private def collidingLeft : Fin 2 → Fin 2 → F := ![![0, 0], ![1, 0]]
private def collidingRight : Fin 2 → Fin 2 → F := ![![0, 0], ![2, 0]]
private def collidingStatement : Fin 2 → F := ![0, 0]

private theorem collidingLeft_holds :
    (family accumulator 1).holds collidingStatement collidingLeft :=
  holds_of_prefix 0 1 0 1 1 _ _ (by decide) (by rw [eval_ofMultiset_rowValues]; decide)

private theorem collidingRight_holds :
    (family accumulator 1).holds collidingStatement collidingRight :=
  holds_of_prefix 0 1 0 1 1 _ _ (by decide) (by rw [eval_ofMultiset_rowValues]; decide)

example : rowValues Finset.univ (fun row => collidingLeft row 0) ≠
      rowValues Finset.univ (fun row => collidingRight row 0) ∧
    (ofMultiset (rowValues Finset.univ fun row => collidingLeft row 0) -
      ofMultiset (rowValues Finset.univ fun row => collidingRight row 0)).IsRoot 0 := by
  have distinct : rowValues Finset.univ (fun row => collidingLeft row 0) ≠
      rowValues Finset.univ (fun row => collidingRight row 0) := by decide
  rcases connected_or_root 0 1 0 1 0 1 0 1 _ _ _ _ collidingLeft_holds collidingRight_holds
    rfl rfl with same | ⟨_, root⟩
  · exact absurd same distinct
  · exact ⟨distinct, root⟩

-- A fixed combination of constraints is weaker than all constraints. With one
-- row, value 1, accumulator 0 and challenge 3, the correct terminal is 2. The
-- claimed terminal 5 makes the first and last residuals 5 and 2; their unit
-- combination vanishes, yet the relation fails.
private def cancellingTrace : Fin 1 → Fin 2 → F := ![![1, 0]]
private def cancellingStatement : Fin 2 → F := ![3, 5]

example : (accumulator.filterMap fun constraint =>
    if constraint.scope.Active (0 : Fin 1) then
      constraint.expression.evaluateAt cancellingStatement cancellingTrace 0
    else none) = [5, 2] := by
  decide

example : ¬ (family accumulator 0).holds cancellingStatement cancellingTrace := by
  intro holds
  have terminal := terminal_eq_eval 0 1 0 1 0 _ _ holds
  rw [eval_ofMultiset_rowValues] at terminal
  revert terminal
  decide

-- The accumulator adds one degree-two transition; quotient degree bounds use
-- these expression degrees with the trace degree, as for any other constraint.
example : accumulator.map (·.expression.degree) = [1, 2, 1] := by decide

-- The active-row vanishing polynomial is the fingerprint of its row points.
example {K : Type} [Field K] {height : Nat} (rows : Finset (Fin height))
    (point : Fin height → K) : vanishing rows point = ofMultiset (rowValues rows point) := by
  rw [vanishing, ofMultiset_apply, rowValues, Multiset.map_map, Finset.prod_eq_multiset_prod]
  rfl

end Tests.AIRProductConnection
