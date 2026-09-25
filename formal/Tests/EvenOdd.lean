import Zkc.Polynomial.EvenOdd
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum
import Tools.DeclarationAudit

set_option autoImplicit false

namespace Tests.EvenOdd
open Polynomial Zkc.Polynomial.EvenOdd

private abbrev F := ZMod 17
private instance : Fact (Nat.Prime 17) := ⟨by decide⟩

example : fold (0 : F[X]) 7 = 0 := by simp
example : fold (C 9 : F[X]) 7 = C 9 := by simp
example : fold (X : F[X]) 7 = C 7 := by
  ext n
  simp only [coeff_fold, coeff_X, coeff_C]
  split_ifs <;> first | contradiction | omega | norm_num [F]


-- The coefficient calculation covers both parities, not a prover's sampled path.
example : fold (C 3 + C 4 * X + C 5 * X ^ 2 + C 6 * X ^ 3 : F[X]) 2 =
    C 11 + C 0 * X := by
  ext n
  simp only [coeff_fold, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  split_ifs <;> first | contradiction | omega | (norm_num [F] <;> decide)


example (p : F[X]) (x : F) (hx : x ≠ 0) :
    (fold p 7).eval (x ^ 2) =
      (p.eval x + p.eval (-x)) / 2 + 7 * (p.eval x - p.eval (-x)) / (2 * x) :=
  eval_fold_sq p 7 x (by decide) hx

-- Coefficient reconstruction works in characteristic two too; the division
-- formula deliberately does not claim to do so.
example (p : (ZMod 2)[X]) :
    p = (even p).comp (X ^ 2) + X * (odd p).comp (X ^ 2) :=
  reconstruction p

example (p : F[X]) (h : p.natDegree ≤ 7) : (fold p 3).natDegree ≤ 3 :=
  (natDegree_fold_le p 3).trans (by omega)

end Tests.EvenOdd

-- A module is not in its own environment while it elaborates, so it cannot
-- audit itself; Tests/Audit.lean covers the Tests family from a module that
-- imports them all.
run_cmd Tools.DeclarationAudit.check [`Zkc.Polynomial.EvenOdd] "EVEN-ODD-AUDIT-PASS"
