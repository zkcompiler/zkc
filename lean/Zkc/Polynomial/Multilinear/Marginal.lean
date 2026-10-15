module

public import Zkc.Polynomial.Multilinear.Prefix

@[expose] public section

/-! Ordered marginal tables. The first coordinates remain in the existing MSB
order; summing the suffix connects their extension to original-table residual
truth. No protocol or security backend is needed for these laws. -/

set_option autoImplicit false

namespace Zkc.Polynomial.Multilinear

variable {F : Type} {remaining count : Nat}

/-- Keep the first coordinates in their existing order and sum the suffix. -/
def sumRemaining [Add F] (remaining count : Nat) (table : Table F (remaining + count)) :
    Table F count :=
  fun bits => booleanSum (fun rest => table (Quadratic.point count bits rest))

theorem booleanSum_sumRemaining [Add F] (table : Table F (remaining + count)) :
    booleanSum (sumRemaining remaining count table) = booleanSum table := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change booleanSum (sumRemaining remaining count (half table false)) +
        booleanSum (sumRemaining remaining count (half table true)) = _
      rw [ih, ih]
      rfl

theorem fixFirst_sumRemaining [Ring F] (table : Table F (remaining + (count + 1))) (r : F) :
    fixFirst (sumRemaining remaining (count + 1) table) r =
      sumRemaining remaining count (fixFirst table r) := by
  funext bits
  change (1 - r) * booleanSum (fun rest => table
      (Fin.cons false (Quadratic.point count bits rest))) +
    r * booleanSum (fun rest => table
      (Fin.cons true (Quadratic.point count bits rest))) =
    booleanSum (fun rest => (1 - r) * table
      (Fin.cons false (Quadratic.point count bits rest)) +
      r * table (Fin.cons true (Quadratic.point count bits rest)))
  rw [booleanSum_add, booleanSum_scale, booleanSum_scale]

theorem extension_sumRemaining [CommRing F] (table : Table F (remaining + count))
    (point : Fin count → F) :
    extension count (sumRemaining remaining count table) point =
      booleanSum (fixPrefix count table point) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      calc
        _ = extension count (fixFirst (sumRemaining remaining (count + 1) table) (point 0))
            (point ∘ Fin.succ) := by
          rw [extension_fixFirst]
          congr 1
          exact (Fin.cons_self_tail point).symm
        _ = booleanSum (fixPrefix count (fixFirst table (point 0)) (point ∘ Fin.succ)) := by
          rw [fixFirst_sumRemaining, ih]
        _ = _ := rfl

end Zkc.Polynomial.Multilinear
