module

public import Mathlib.Algebra.Ring.Defs

@[expose] public section

/-! Formal ring expressions: the tree, its inputs, degree, coefficient map,
substitution and evaluation in a commutative ring. `Zkc.Algebra.RingExpression`
adds the homomorphism, lane and polynomial laws. This module imports only the
ring structure, so that the executable stage can read native expressions
without the polynomial library.
-/

set_option autoImplicit false

namespace Zkc.Algebra.RingExpression

inductive Expr (R : Type*) (Input : Type*) where
  | constant (value : R)
  | input (index : Input)
  | add (left right : Expr R Input)
  | mul (left right : Expr R Input)
  | neg (operand : Expr R Input)
  deriving DecidableEq, Repr

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

end Expr
end Zkc.Algebra.RingExpression
