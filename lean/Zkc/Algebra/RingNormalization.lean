module

public import Zkc.Algebra.RingExpression
public import Mathlib.Algebra.BigOperators.Ring.Multiset
public import Mathlib.Data.Multiset.Bind

@[expose] public section

/-! Checked distributive normalization of local ring expressions.

Terms and factors are unordered; coefficients are multiplied and signs pushed
to coefficients. Like terms are not collected, so equality of normal forms is
a sufficient but incomplete ring-equivalence criterion. The checker is for
pure ring expressions; effects and guards must remain in their source context.
-/

namespace Zkc.Algebra.RingExpression

variable {R I : Type*} [CommRing R]

abbrev Terms (R I : Type*) := Multiset (R × Multiset I)

def termValue (assignment : I → R) (term : R × Multiset I) : R :=
  term.1 * (term.2.map assignment).prod

def termsValue (assignment : I → R) (terms : Terms R I) : R :=
  (terms.map (termValue assignment)).sum

def Expr.terms : Expr R I → Terms R I
  | .constant value => {(value, 0)}
  | .input index => {(1, {index})}
  | .add left right => left.terms + right.terms
  | .mul left right => left.terms.bind fun a =>
      right.terms.map fun b => (a.1 * b.1, a.2 + b.2)
  | .neg operand => operand.terms.map fun a => (-a.1, a.2)

theorem termValue_mul (assignment : I → R) (a b : R × Multiset I) :
    termValue assignment (a.1 * b.1, a.2 + b.2) =
      termValue assignment a * termValue assignment b := by
  simp only [termValue, Multiset.map_add, Multiset.prod_add]
  ac_rfl

theorem Expr.terms_sound (expression : Expr R I) (assignment : I → R) :
    termsValue assignment expression.terms = expression.eval assignment := by
  induction expression with
  | constant value => simp [terms, termsValue, termValue, Expr.eval]
  | input index => simp [terms, termsValue, termValue, Expr.eval]
  | add left right ihLeft ihRight =>
      simpa only [terms, termsValue, Multiset.map_add, Multiset.sum_add, Expr.eval] using
        congrArg₂ (· + ·) ihLeft ihRight
  | mul left right ihLeft ihRight =>
      simp only [terms, termsValue, Multiset.map_bind, Multiset.map_map,
        Function.comp_apply, termValue_mul, Multiset.sum_bind, Multiset.sum_map_mul_left,
        Multiset.sum_map_mul_right]
      exact congrArg₂ (· * ·) ihLeft ihRight
  | neg operand ih =>
      simp only [terms, termsValue, Multiset.map_map, Function.comp_def,
        termValue, neg_mul, Multiset.sum_map_neg]
      exact congrArg Neg.neg ih

def Expr.check [DecidableEq R] [DecidableEq I] (left right : Expr R I) : Bool :=
  decide (left.terms = right.terms)

theorem Expr.check_sound [DecidableEq R] [DecidableEq I] (left right : Expr R I)
    (checked : left.check right = true) (assignment : I → R) :
    left.eval assignment = right.eval assignment := by
  have same : left.terms = right.terms := of_decide_eq_true checked
  rw [← left.terms_sound assignment, ← right.terms_sound assignment, same]

/-- Integer-coefficient checking proves the same identity in every commutative
ring, including fields of positive characteristic. No sampling is involved. -/
theorem Expr.check_cast_sound {S : Type*} [CommRing S] [DecidableEq I]
    (left right : Expr ℤ I) (checked : left.check right = true) (assignment : I → S) :
    (left.map (Int.castRingHom S)).eval assignment =
      (right.map (Int.castRingHom S)).eval assignment := by
  have same : left.terms = right.terms := of_decide_eq_true checked
  have transport (expression : Expr ℤ I) :
      (expression.map (Int.castRingHom S)).terms =
        expression.terms.map (fun term => ((term.1 : S), term.2)) := by
    induction expression with
    | constant value => simp [Expr.map, Expr.terms]
    | input index => simp [Expr.map, Expr.terms]
    | add left right ihLeft ihRight =>
        simp only [Expr.map, Expr.terms, ihLeft, ihRight, Multiset.map_add]
    | mul left right ihLeft ihRight =>
        simp only [Expr.map, Expr.terms, ihLeft, ihRight]
        simp [Multiset.map_bind, Multiset.bind_map, Multiset.map_map]
    | neg operand ih =>
        simp only [Expr.map, Expr.terms, ih]
        simp [Multiset.map_map]
  rw [← Expr.terms_sound, ← Expr.terms_sound, transport, transport, same]

end Zkc.Algebra.RingExpression
