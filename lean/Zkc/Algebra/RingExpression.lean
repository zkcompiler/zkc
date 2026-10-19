module

public import Zkc.Algebra.RingExpression.Basic
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Eval.Defs

@[expose] public section

/-! Formal ring expressions shared by relation and polynomial interpretations.
This tree model states the substitution laws. A native DAG/decoder correspondence
is a separate obligation; these theorems do not establish that correspondence.
-/

set_option autoImplicit false

namespace Zkc.Algebra.RingExpression

namespace Expr

variable {R S I J : Type*}

theorem eval_hom [CommRing R] [CommRing S] (e : Expr R I)
    (f : R →+* S) (assignment : I → R) :
    (e.map f).eval (fun i => f (assignment i)) = f (e.eval assignment) := by
  induction e <;> simp [map, eval, *]

/-- Packed interpretation is pointwise scalar interpretation. Lane selection
and the native SIMD representation still require their own correspondence. -/
theorem eval_lanes [CommRing R] {Lane : Type*} (e : Expr R I)
    (assignment : I → Lane → R) (lane : Lane) :
    (e.map (fun value _ => value)).eval assignment lane =
      e.eval (fun i => assignment i lane) := by
  induction e <;> simp [map, eval, *]

/-- Exact coefficient-ring interpretation. Multiplication remains multiplication
of the substituted polynomials, regardless of their values on a finite domain. -/
noncomputable def polynomial [CommRing R] (e : Expr R I)
    (assignment : I → Polynomial R) : Polynomial R :=
  (e.map Polynomial.C).eval assignment

theorem polynomial_eval [CommRing R] (e : Expr R I)
    (assignment : I → Polynomial R) (point : R) :
    Polynomial.eval point (e.polynomial assignment) =
      e.eval (fun i => Polynomial.eval point (assignment i)) := by
  induction e <;> simp_all [polynomial, map, eval, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_neg]

theorem polynomial_degree [CommRing R] (e : Expr R I)
    (assignment : I → Polynomial R) (inputDegree : I → Nat)
    (bound : ∀ i ∈ e.inputs, (assignment i).natDegree ≤ inputDegree i) :
    (e.polynomial assignment).natDegree ≤ e.degree inputDegree := by
  induction e with
  | constant value => simp [polynomial, map, eval, degree]
  | input i => exact bound i (by simp [inputs])
  | add a b iha ihb =>
      exact (Polynomial.natDegree_add_le _ _).trans (max_le_max
        (iha fun i h => bound i (List.mem_append_left _ h))
        (ihb fun i h => bound i (List.mem_append_right _ h)))
  | mul a b iha ihb =>
      exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add
        (iha fun i h => bound i (List.mem_append_left _ h))
        (ihb fun i h => bound i (List.mem_append_right _ h)))
  | neg a ih => simpa [polynomial, map, eval, degree] using ih bound

end Expr
end Zkc.Algebra.RingExpression
