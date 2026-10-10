import Zkc.Polynomial.Quadratic
import Mathlib.Data.List.OfFn

/-! Bridge ordered coordinate lists to indexed polynomial points.

The fallback value makes the interpretation total. Actual source requests retain
an arity/readiness guard; the laws identifying a complete point require its
declared length. No missing coordinate is silently admitted by these laws.
-/

set_option autoImplicit false

namespace Zkc.Polynomial

variable {F : Type} [CommSemiring F] {n : Nat}

def coordinates (n : Nat) (values : List F) : Fin n → F :=
  fun i => values[i.val]?.getD 0

theorem coordinates_ofFn (values : Fin n → F) :
    coordinates n (List.ofFn values) = values := by
  funext i
  simp [coordinates]

theorem ofFn_coordinates (values : List F) (size : values.length = n) :
    List.ofFn (coordinates n values) = values := by
  subst n
  apply List.ext_getElem
  · simp
  · intro i left right
    simp [coordinates, right]

omit [CommSemiring F] in
theorem ofFn_point (m : Nat) (fixed : Fin m → F) (tail : Fin n → F) :
    List.ofFn (Quadratic.point m fixed tail) = List.ofFn fixed ++ List.ofFn tail := by
  induction m with
  | zero => simp [Quadratic.point]
  | succ m ih =>
      simp only [Quadratic.point, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
      exact congrArg (List.cons (fixed 0)) (ih (fixed ∘ Fin.succ))

theorem point_coordinates (m : Nat) (fixed tail : List F)
    (fixedSize : fixed.length = m) (tailSize : tail.length = n) :
    Quadratic.point m (coordinates m fixed) (coordinates n tail) =
      coordinates (n + m) (fixed ++ tail) := by
  apply List.ofFn_injective
  rw [ofFn_point, ofFn_coordinates fixed fixedSize, ofFn_coordinates tail tailSize,
    ofFn_coordinates (fixed ++ tail) (by simp [fixedSize, tailSize, Nat.add_comm])]

theorem materialize_coordinates (m : Nat) (p : Quadratic F (n + m))
    (fixed tail : List F) (fixedSize : fixed.length = m) (tailSize : tail.length = n) :
    (p.materialize m (coordinates m fixed)).eval (coordinates n tail) =
      p.eval (coordinates (n + m) (fixed ++ tail)) := by
  rw [Quadratic.materialize_eval, point_coordinates m fixed tail fixedSize tailSize]

end Zkc.Polynomial
