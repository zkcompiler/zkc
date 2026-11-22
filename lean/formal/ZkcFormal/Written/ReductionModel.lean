module

public import ZkcFormal.Written.ArithmeticModel
public import ZkcFormal.Written.SumcheckRows
public import Mathlib.Algebra.Polynomial.Eval.Defs

@[expose] public section
namespace ZkcFormal.Written.ArithmeticModel
open Zkc.Core Interactive.Sumcheck SumcheckRows

variable (F G : Type) [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

abbrev scalarRows := sourceRows {}
abbrev events := sourceEvents {}
abbrev sums := sumRow {}
abbrev vectors := vectorRows {}

scoped instance : DecidableEq (scalarRows.F (model F G)) := inferInstanceAs (DecidableEq F)
scoped instance : Lean.Grind.Field (scalarRows.F (model F G)) := inferInstanceAs (Lean.Grind.Field F)

/-- All row and literal premises for the joint Sumcheck reduction, for every table depth. -/
theorem reductionArithmetic (rounds : Nat) :
    HonestPairs.Arithmetic scalarRows sums vectors events rounds (model F G) where
  scalar _ := {
    one := by change ((1 : Nat) : F) = 1; exact Nat.cast_one
    add := by intros; rfl
    sub := by intros; rfl
    mul := by intros; rfl }
  sum := by intro _ _ xs _; rfl
  vector := by
    intros
    exact ⟨by intros; rfl, by intros; rfl, by intros; rfl⟩
  equal := by intro x y; rfl

/-- The univariate polynomial determined by the values at the two endpoints. -/
noncomputable def pairPolynomial (a b : F) : Polynomial F :=
  Polynomial.C a + Polynomial.C (b-a) * Polynomial.X

/-- The source pair-round evaluator computes Mathlib polynomial evaluation on every challenge
using the scalar and sequence interpretation that supplies the joint reduction. -/
theorem evaluatePair (k : Key) (a b r : F) :
    (scalarRows.evaluateBody [] k).denote (localSem (model F G) [] (Defs.fnTable _ .nil)) []
      (Env.positional (.cons (a,b,()) (.cons r .nil))) =
      .done (.cons (show F from (pairPolynomial F a b).eval r) .nil) := by
  have value := scalarRows.evaluate_value (model F G) (Defs.fnTable _ .nil) k a b r
    ((reductionArithmetic F G 1).scalar (by decide))
  have eq : line (a,b) r = (pairPolynomial F a b).eval r := by
    rw [line_normalForm, pairPolynomial, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_C_mul, Polynomial.eval_X, mul_comm]
  let returned (x : F) : Local (HList (model F G).Val [scalarTy]) := .done (.cons x .nil)
  exact value.trans (congrArg returned eq)

end ZkcFormal.Written.ArithmeticModel
