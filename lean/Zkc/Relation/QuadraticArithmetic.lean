import Zkc.Relation.Padding
import Zkc.Relation.AIR.Polynomial
import Mathlib.LinearAlgebra.Lagrange

/-! Ordered sparse R1CS and its exact interpolated polynomial residual.

This is a relation-algebra boundary: it constructs the three interpolants from
actual sparse rows, proves divisibility equivalent to satisfaction, and retains
ONE/public binding separately. It does not mention a proof, pairing equation,
setup distribution or native FFT implementation. -/

set_option autoImplicit false

namespace Zkc.Relation.RankOne.System
open Polynomial

variable {F : Type} [Field F] {m n p w : Nat}

/-- Interpolate the actual ordered matrix product at the selected row points. -/
noncomputable def interpolateRows (matrix : Sparse.Matrix F m n)
    (point : Fin m → F) (z : Fin n → F) : Polynomial F :=
  Lagrange.interpolate Finset.univ point (fun i => Sparse.eval matrix.rows[i] z)

/-- The QAP residual uses all three source matrices, including the source C. -/
noncomputable def residual (system : System F m n) (point : Fin m → F)
    (z : Fin n → F) : Polynomial F :=
  interpolateRows system.A point z * interpolateRows system.B point z -
    interpolateRows system.C point z

/-- On a satisfying assignment, interpolating the source C agrees with
interpolating rowwise A-times-B values. This is the algebraic premise required
by the prepared-key numerator convention; it does not verify native transforms. -/
theorem interpolateC_eq_rowProducts (system : System F m n) (point : Fin m → F)
    (z : Fin n → F) (satisfied : system.Satisfies z) :
    interpolateRows system.C point z = Lagrange.interpolate Finset.univ point
      (fun i => Sparse.eval system.A.rows[i] z * Sparse.eval system.B.rows[i] z) := by
  exact congrArg (Lagrange.interpolate Finset.univ point)
    (funext fun i => (satisfied i).symm)

/-- Distinct points retain the association of each interpolated value to its row. -/
theorem eval_interpolateRows (matrix : Sparse.Matrix F m n) (point : Fin m → F)
    (distinct : Function.Injective point) (z : Fin n → F) (i : Fin m) :
    (interpolateRows matrix point z).eval (point i) = Sparse.eval matrix.rows[i] z := by
  exact Lagrange.eval_interpolate_at_node _ (distinct.injOn) (Finset.mem_univ i)

/-- A nonzero row residual cannot disappear under exact interpolation and division.
This includes the empty system and does not assume the final equation holds. -/
theorem satisfies_iff_vanishing_dvd (system : System F m n) (point : Fin m → F)
    (distinct : Function.Injective point) (z : Fin n → F) :
    system.Satisfies z ↔ AIR.vanishing Finset.univ point ∣ system.residual point z := by
  rw [AIR.vanishing_dvd_iff _ _ distinct]
  simp only [residual, eval_sub, eval_mul, eval_interpolateRows _ _ distinct,
    sub_eq_zero, Finset.mem_univ, forall_const, Satisfies]

/-- The full relation still binds ONE and each ordered public coordinate.
Polynomial divisibility alone does not bind a statement. -/
theorem bound_iff_vanishing_dvd (system : System F m n) (layout : Layout p w n)
    (point : Fin m → F) (distinct : Function.Injective point)
    (statement : Fin p → F) (z : Fin n → F) :
    (system.boundFamily layout).holds statement z ↔
      Bound layout statement z ∧ AIR.vanishing Finset.univ point ∣ system.residual point z := by
  exact and_congr_right fun _ => system.satisfies_iff_vanishing_dvd point distinct z

/-- Added zero rows/columns impose no accidental extra condition. The target's
new columns may contain arbitrary values; the conclusion restricts them away. -/
theorem padded_vanishing_dvd_iff (system : System F m n) (extraRows extraColumns : Nat)
    (point : Fin (m + extraRows) → F) (distinct : Function.Injective point)
    (z : Fin (n + extraColumns) → F) :
    AIR.vanishing Finset.univ point ∣ (system.pad extraRows extraColumns).residual point z ↔
      system.Satisfies (z ∘ Fin.castAdd extraColumns) := by
  rw [← satisfies_iff_vanishing_dvd _ point distinct, satisfies_pad]

/-- Added A-only rows change interpolation data while preserving the relation.
This covers the algebraic form of a prepared key's appended public rows. It
does not certify that a binary key actually implements this convention. -/
theorem appended_vanishing_dvd_iff {k : Nat} (system : System F m n)
    (extra : Sparse.Matrix F k n) (point : Fin (m + k) → F)
    (distinct : Function.Injective point) (z : Fin n → F) :
    AIR.vanishing Finset.univ point ∣ (system.appendTrivialRows extra).residual point z ↔
      system.Satisfies z := by
  rw [← satisfies_iff_vanishing_dvd _ point distinct, satisfies_appendTrivialRows]

end Zkc.Relation.RankOne.System
