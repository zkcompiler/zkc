import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! Formal ring expressions shared by relation and polynomial interpretations.
This tree model states the substitution laws. A native DAG/decoder correspondence
is a separate obligation; these theorems do not establish that correspondence.
-/

set_option autoImplicit false

namespace Zkc.Algebra.RingExpression

inductive Expr (R : Type*) (Input : Type*) where
  | constant (value : R)
  | input (index : Input)
  | add (left right : Expr R Input)
  | mul (left right : Expr R Input)
  | neg (operand : Expr R Input)

namespace Expr

variable {R S I J : Type*}

def inputs : Expr R I → List I
  | .constant _ => []
  | .input i => [i]
  | .add left right | .mul left right => left.inputs ++ right.inputs
  | .neg operand => operand.inputs

def degree (inputDegree : I → Nat) : Expr R I → Nat
  | .constant _ => 0
  | .input i => inputDegree i
  | .add left right => max (left.degree inputDegree) (right.degree inputDegree)
  | .mul left right => left.degree inputDegree + right.degree inputDegree
  | .neg operand => operand.degree inputDegree

def map (coefficient : R → S) : Expr R I → Expr S I
  | .constant value => .constant (coefficient value)
  | .input i => .input i
  | .add left right => .add (left.map coefficient) (right.map coefficient)
  | .mul left right => .mul (left.map coefficient) (right.map coefficient)
  | .neg operand => .neg (operand.map coefficient)

def substitute (assignment : I → Expr R J) : Expr R I → Expr R J
  | .constant value => .constant value
  | .input i => assignment i
  | .add left right => .add (left.substitute assignment) (right.substitute assignment)
  | .mul left right => .mul (left.substitute assignment) (right.substitute assignment)
  | .neg operand => .neg (operand.substitute assignment)

def eval [CommRing R] (assignment : I → R) : Expr R I → R
  | .constant value => value
  | .input i => assignment i
  | .add left right => left.eval assignment + right.eval assignment
  | .mul left right => left.eval assignment * right.eval assignment
  | .neg operand => -(operand.eval assignment)

theorem eval_local [CommRing R] (e : Expr R I) (left right : I → R)
    (agree : ∀ i ∈ e.inputs, left i = right i) : e.eval left = e.eval right := by
  induction e with
  | constant _ => rfl
  | input i => exact agree i (by simp [inputs])
  | add a b iha ihb =>
      exact congrArg₂ (· + ·) (iha fun i h => agree i (List.mem_append_left _ h))
        (ihb fun i h => agree i (List.mem_append_right _ h))
  | mul a b iha ihb =>
      exact congrArg₂ (· * ·) (iha fun i h => agree i (List.mem_append_left _ h))
        (ihb fun i h => agree i (List.mem_append_right _ h))
  | neg a ih => exact congrArg Neg.neg (ih agree)

theorem eval_substitute [CommRing R] (e : Expr R I)
    (replacement : I → Expr R J) (assignment : J → R) :
    (e.substitute replacement).eval assignment =
      e.eval (fun i => (replacement i).eval assignment) := by
  induction e <;> simp [substitute, eval, *]

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
