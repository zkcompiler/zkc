import Zkc.Relation.AIR
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.RingDivision

/-! The finite AIR/polynomial boundary. Active rows, rather than an implicit
cyclic trace, determine the vanishing polynomial. The bridge requires explicit
read adequacy and legal windows. It is not a proximity or argument-soundness
theorem. -/

set_option autoImplicit false

namespace Zkc.Relation.AIR

open Polynomial

variable {F : Type} [Field F] {p c height : Nat}

noncomputable def activeRows (scope : Scope) (height : Nat) : Finset (Fin height) :=
  Finset.univ.filter fun row => scope.Active row

noncomputable def vanishing (rows : Finset (Fin height)) (point : Fin height → F) :
    Polynomial F :=
  ∏ row ∈ rows, (X - C (point row))

theorem vanishing_monic (rows : Finset (Fin height)) (point : Fin height → F) :
    (vanishing rows point).Monic := monic_prod_X_sub_C point rows

theorem vanishing_degree (rows : Finset (Fin height)) (point : Fin height → F) :
    (vanishing rows point).natDegree = rows.card := by
  classical
  rw [vanishing, natDegree_prod_of_monic _ _ (fun row _ => monic_X_sub_C (point row))]
  simp

/-- Multiplying by a nonzero complement selector permits a common vanishing
divisor without changing the exact obligation. Selecting the complement itself
and its row coverage is a separate, source-relative task. -/
theorem selector_divisibility (active selector numerator : Polynomial F)
    (nonzero : selector ≠ 0) :
    active * selector ∣ numerator * selector ↔ active ∣ numerator :=
  mul_dvd_mul_iff_right nonzero

/-- The zero quotient is deliberately excluded: its natural degree is zero,
even when the numerator degree bound is smaller than the vanishing degree. -/
theorem quotient_degree (e : Expr F p c) (statement : Fin p → F)
    (readPolynomial : Nat × Fin c → Polynomial F) (D : Nat)
    (bound : ∀ read ∈ e.reads, (readPolynomial read).natDegree ≤ D)
    (rows : Finset (Fin height)) (point : Fin height → F) (q : Polynomial F)
    (nonzero : q ≠ 0)
    (identity : e.polynomial statement readPolynomial = vanishing rows point * q) :
    rows.card + q.natDegree ≤ e.degree * D := by
  have degreeBound := e.polynomial_degree statement readPolynomial D bound
  rw [identity, natDegree_mul (vanishing_monic rows point).ne_zero nonzero,
    vanishing_degree] at degreeBound
  exact degreeBound

/-- Distinct row points turn pointwise constraint satisfaction into exact
polynomial divisibility, including the empty active-row set. -/
theorem vanishing_dvd_iff (rows : Finset (Fin height)) (point : Fin height → F)
    (distinct : Function.Injective point) (q : Polynomial F) :
    vanishing rows point ∣ q ↔ ∀ row ∈ rows, q.eval (point row) = 0 := by
  classical
  constructor
  · intro h row member
    have factor : X - C (point row) ∣ vanishing rows point :=
      Finset.dvd_prod_of_mem _ member
    exact (dvd_iff_isRoot.mp (factor.trans h))
  · intro h
    apply Finset.prod_dvd_of_coprime
    · intro a _ b _ different
      exact pairwise_coprime_X_sub_C distinct different
    · intro row member
      exact dvd_iff_isRoot.mpr (h row member)

/-- The connection is source-relative: only actual reads at active rows need
to agree, while out-of-range source accesses cannot acquire a cyclic meaning. -/
theorem Constraint.holds_iff_vanishing_dvd
    (constraint : Constraint F p c) (statement : Fin p → F)
    (trace : Fin height → Fin c → F) (point : Fin height → F)
    (distinct : Function.Injective point)
    (readPolynomial : Nat × Fin c → Polynomial F)
    (fits : ∀ row : Fin height, constraint.scope.Active row →
      row.val + constraint.expression.maxOffset < height)
    (adequate : ∀ row, constraint.scope.Active row →
      ∀ read ∈ constraint.expression.reads,
        (readPolynomial read).eval (point row) = Expr.traceRead trace row read) :
    constraint.Holds statement trace ↔
      vanishing (activeRows constraint.scope height) point ∣
        constraint.expression.polynomial statement readPolynomial := by
  rw [vanishing_dvd_iff _ _ distinct]
  have atRow (row : Fin height) (active : constraint.scope.Active row) :
      constraint.expression.evaluateAt statement trace row =
        some ((constraint.expression.polynomial statement readPolynomial).eval (point row)) := by
    rw [Expr.evaluateAt, if_pos (fits row active), Expr.polynomial_eval]
    congr 1
    exact constraint.expression.eval_local statement _ _
      (fun read member => (adequate row active read member).symm)
  constructor
  · intro holds row member
    have active : constraint.scope.Active row := (Finset.mem_filter.mp member).2
    exact Option.some.inj ((atRow row active).symm.trans (holds row active))
  · intro divisible row active
    rw [atRow row active, divisible row (Finset.mem_filter.mpr ⟨Finset.mem_univ _, active⟩)]

/-- A multiplicative shift realizes the original row offset only when the
source window fits. This theorem does not wrap the finite trace. -/
theorem shifted_eval {n : Nat} (g : F) (columns : Fin c → Polynomial F)
    (trace : Fin n → Fin c → F)
    (interpolates : ∀ row column, (columns column).eval (g ^ row.val) = trace row column)
    (row : Fin n) (offset : Nat) (column : Fin c) (fits : row.val + offset < n) :
    ((columns column).comp (C (g ^ offset) * X)).eval (g ^ row.val) =
      Expr.traceRead trace row (offset, column) := by
  simp only [eval_comp, eval_mul, eval_C, eval_X]
  rw [mul_comm, ← pow_add, interpolates ⟨row.val + offset, fits⟩ column]
  simp [Expr.traceRead, fits]

/-- A concrete multiplicative-domain instance of the abstract read bridge.
Interpolation and distinct domain points remain explicit preconditions. -/
theorem Constraint.holds_iff_shifted_divisibility
    (constraint : Constraint F p c) (statement : Fin p → F)
    (trace : Fin height → Fin c → F) (g : F) (columns : Fin c → Polynomial F)
    (distinct : Function.Injective (fun row : Fin height => g ^ row.val))
    (interpolates : ∀ row column, (columns column).eval (g ^ row.val) = trace row column)
    (fits : ∀ row : Fin height, constraint.scope.Active row →
      row.val + constraint.expression.maxOffset < height) :
    constraint.Holds statement trace ↔
      vanishing (activeRows constraint.scope height) (fun row => g ^ row.val) ∣
        constraint.expression.polynomial statement
          (fun read => (columns read.2).comp (C (g ^ read.1) * X)) := by
  apply constraint.holds_iff_vanishing_dvd statement trace _ distinct _ fits
  intro row active read member
  exact shifted_eval g columns trace interpolates row read.1 read.2
    (Expr.used_read_in_range constraint.expression row (fits row active) read member)

end Zkc.Relation.AIR
