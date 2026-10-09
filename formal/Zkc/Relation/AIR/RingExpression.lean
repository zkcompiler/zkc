import Zkc.Relation.AIR
import Zkc.Algebra.RingExpression

/-! The existing finite AIR expression embeds into shared ring substitution.
Finite window and scope obligations remain owned by AIR; this translation does
not turn a noncyclic read into a cyclic one or discharge an out-of-range read.
-/

set_option autoImplicit false

namespace Zkc.Relation.AIR.Expr

variable {F : Type} {p c : Nat}

def toRing : Expr F p c → Algebra.RingExpression.Expr F (Fin p ⊕ (Nat × Fin c))
  | .constant value => .constant value
  | .publicInput index => .input (.inl index)
  | .read offset column => .input (.inr (offset, column))
  | .add left right => .add left.toRing right.toRing
  | .mul left right => .mul left.toRing right.toRing

theorem toRing_eval [CommRing F] (e : Expr F p c) (statement : Fin p → F)
    (read : Nat × Fin c → F) :
    e.toRing.eval (Sum.elim statement read) = e.eval statement read := by
  induction e <;> simp [toRing, Algebra.RingExpression.Expr.eval, eval, *]

theorem toRing_degree (e : Expr F p c) :
    e.toRing.degree (Sum.elim (fun _ => 0) (fun _ => 1)) = e.degree := by
  induction e <;> simp [toRing, Algebra.RingExpression.Expr.degree, degree, *]

theorem toRing_polynomial [CommRing F] (e : Expr F p c)
    (statement : Fin p → F) (read : Nat × Fin c → Polynomial F) :
    e.toRing.polynomial (Sum.elim (fun i => Polynomial.C (statement i)) read) =
      e.polynomial statement read := by
  induction e <;> simp_all [toRing, Algebra.RingExpression.Expr.polynomial,
    Algebra.RingExpression.Expr.map, Algebra.RingExpression.Expr.eval, polynomial]

end Zkc.Relation.AIR.Expr
