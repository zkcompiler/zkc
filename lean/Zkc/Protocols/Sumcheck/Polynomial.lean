import Zkc.Polynomial.Quadratic
import Zkc.Protocols.AlgebraicRounds.Source
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-! Honest round polynomials and the degree-two collision bound. -/

set_option autoImplicit false

namespace Zkc.Protocols.Sumcheck

open Zkc.Polynomial AlgebraicRounds

variable {F : Type} {n : Nat}

section Semiring
variable [CommSemiring F]

def roundPolynomial : Quadratic F (n + 1) → Message F
  | .node a b c => ⟨a.booleanSum, b.booleanSum, c.booleanSum⟩

theorem round_evaluate (p : Quadratic F (n + 1)) (r : F) :
    (roundPolynomial p).evaluate r = (p.restrict r).booleanSum := by
  cases p
  simp only [roundPolynomial, Message.evaluate, Quadratic.booleanSum_restrict]
  ring

theorem round_boundary (p : Quadratic F (n + 1)) :
    (roundPolynomial p).boundary = p.booleanSum := by
  rw [Message.boundary, round_evaluate, round_evaluate, Quadratic.booleanSum_split]

/-- The coefficient message denotes a univariate polynomial of degree at most two. -/
noncomputable def messagePolynomial (message : Message F) : _root_.Polynomial F :=
  _root_.Polynomial.C message.constant + _root_.Polynomial.C message.linear * _root_.Polynomial.X +
    _root_.Polynomial.C message.quadratic * _root_.Polynomial.X ^ 2

theorem messagePolynomial_eval (message : Message F) (r : F) :
    (messagePolynomial message).eval r = message.evaluate r := by
  simp only [messagePolynomial, _root_.Polynomial.eval_add, _root_.Polynomial.eval_mul,
    _root_.Polynomial.eval_C, _root_.Polynomial.eval_X,
    Message.evaluate, pow_two]
  ring

theorem messagePolynomial_degree (message : Message F) :
    (messagePolynomial message).natDegree ≤ 2 := by
  apply _root_.Polynomial.natDegree_add_le_of_degree_le
  · apply _root_.Polynomial.natDegree_add_le_of_degree_le
    · simp
    · exact (_root_.Polynomial.natDegree_C_mul_le _ _).trans
        (_root_.Polynomial.natDegree_X_le.trans (by omega))
  · exact _root_.Polynomial.natDegree_C_mul_X_pow_le _ _

end Semiring

variable [CommRing F]

/-- False boundary sums force a nonzero difference polynomial. This argument
also covers small fields where different coefficient vectors induce the same
function: such vectors cannot have different Boolean boundary sums. -/
theorem difference_nonzero (message : Message F) (p : Quadratic F (n + 1))
    (different : message.boundary ≠ p.booleanSum) :
    messagePolynomial message ≠ messagePolynomial (roundPolynomial p) := by
  intro same
  have atZero := congrArg (fun q : _root_.Polynomial F => q.eval 0) same
  have atOne := congrArg (fun q : _root_.Polynomial F => q.eval 1) same
  simp only [messagePolynomial_eval] at atZero atOne
  apply different
  rw [Message.boundary, atZero, atOne, ← Message.boundary, round_boundary]

/-- At most two fresh challenges can repair an already false scalar claim. -/
theorem collision_card [DecidableEq F] [IsDomain F] [Fintype F]
    (message : Message F) (p : Quadratic F (n + 1))
    (different : message.boundary ≠ p.booleanSum) :
    (Finset.univ.filter fun r => message.evaluate r = (p.restrict r).booleanSum).card ≤ 2 := by
  let delta := messagePolynomial message - messagePolynomial (roundPolynomial p)
  have nonzero : delta ≠ 0 := sub_ne_zero.mpr (difference_nonzero message p different)
  have roots : (Finset.univ.filter fun r =>
      message.evaluate r = (p.restrict r).booleanSum).val ⊆ delta.roots := by
    intro r member
    have same := (Finset.mem_filter.mp member).2
    apply (_root_.Polynomial.mem_roots nonzero).mpr
    simp only [_root_.Polynomial.IsRoot, delta, _root_.Polynomial.eval_sub,
      messagePolynomial_eval, round_evaluate, same, sub_self]
  exact (_root_.Polynomial.card_le_degree_of_subset_roots roots).trans
    ((_root_.Polynomial.natDegree_sub_le _ _).trans
      (max_le (messagePolynomial_degree _) (messagePolynomial_degree _)))

end Zkc.Protocols.Sumcheck
