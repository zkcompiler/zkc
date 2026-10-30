module

public import Mathlib.LinearAlgebra.Lagrange
public import ZkcSecurity.Algebra.Polynomial

@[expose] public section

/-! Constraint quotients and DEEP interpolation quotients over a typed finite
set. These are mathematical polynomials, not native polynomial representations.
Strict `degree` bounds include zero, even when the remaining budget is zero. -/

namespace ZkcSecurity.Families.Stark
open _root_.Polynomial

variable {F : Type} [Field F]

/-- Mathlib's monic polynomial vanishing exactly on the selected set. -/
noncomputable def vanishing (points : Finset F) : F[X] := Lagrange.nodal points id

theorem vanishing_monic (points : Finset F) : (vanishing points).Monic :=
  monic_prod_of_monic _ _ (fun x _ => monic_X_sub_C x)

theorem vanishing_natDegree (points : Finset F) : (vanishing points).natDegree = points.card :=
  Lagrange.natDegree_nodal

theorem vanishing_eval_zero_iff (points : Finset F) (x : F) :
    (vanishing points).eval x = 0 ↔ x ∈ points := by
  simp [vanishing, Lagrange.nodal, eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero]

/-- The quotient witness's degree must be admitted independently of its numerator.
This law also handles a zero witness and an exhausted degree budget. -/
theorem factor_degree_lt {points : Finset F} {p q : F[X]} {degree : ℕ}
    (bounded : p.degree < degree) (factor : p = vanishing points * q) :
    q.degree < ((degree - points.card : ℕ) : WithBot ℕ) := by
  by_cases zero : q = 0
  · simp [zero]
  have nonzero := mul_ne_zero (vanishing_monic points).ne_zero zero
  rw [factor, ← natDegree_lt_iff_degree_lt nonzero,
    natDegree_mul (vanishing_monic points).ne_zero zero, vanishing_natDegree] at bounded
  exact (natDegree_lt_iff_degree_lt zero).mp (by omega)

/-- Exact AIR divisibility with the remaining quotient budget. The application's
encoding of constraints into `p` is a separate obligation. -/
theorem vanishes_iff_exists_quotient {points : Finset F} {p : F[X]} {degree : ℕ}
    (bounded : p.degree < degree) :
    (∀ x ∈ points, p.eval x = 0) ↔
      ∃ q : F[X], p = vanishing points * q ∧
        q.degree < ((degree - points.card : ℕ) : WithBot ℕ) := by
  constructor
  · intro zeros
    obtain ⟨q, factor⟩ := prod_X_sub_C_dvd points id Function.injective_id.injOn p zeros
    exact ⟨q, factor, factor_degree_lt bounded factor⟩
  · rintro ⟨q, rfl, _⟩ x member
    rw [eval_mul, (vanishing_eval_zero_iff points x).mpr member, zero_mul]

/-- The residual tested by batching. A numerator degree check alone does not
bound this polynomial when the supplied quotient has excessive degree. -/
noncomputable def residual (points : Finset F) (p q : F[X]) : F[X] :=
  p - vanishing points * q

theorem residual_eq_zero_iff (points : Finset F) (p q : F[X]) :
    residual points p q = 0 ↔ p = vanishing points * q := sub_eq_zero

theorem residual_degree_le (points : Finset F) (p q : F[X]) :
    (residual points p q).natDegree ≤ max p.natDegree (points.card + q.natDegree) :=
  (natDegree_sub_le _ _).trans
    (max_le_max le_rfl (natDegree_mul_le.trans (by rw [vanishing_natDegree])))

variable [DecidableEq F]

/-- Answers are indexed by the actual set of evaluation points. -/
noncomputable def interpolate (points : Finset F) (answers : points → F) : F[X] :=
  Lagrange.interpolate points.attach (fun x => (x : F)) answers

theorem interpolate_eval (points : Finset F) (answers : points → F) (x : points) :
    (interpolate points answers).eval (x : F) = answers x :=
  Lagrange.eval_interpolate_at_node answers Subtype.val_injective.injOn
    (Finset.mem_attach points x)

theorem interpolate_degree_lt (points : Finset F) (answers : points → F) :
    (interpolate points answers).degree < points.card := by
  simpa [interpolate] using Lagrange.degree_interpolate_lt
    (s := points.attach) (v := fun x : points => (x : F)) answers Subtype.val_injective.injOn

/-- Mathlib Euclidean division after subtracting the true answer interpolant. -/
noncomputable def deepQuotient (points : Finset F) (p : F[X]) : F[X] :=
  (p - interpolate points (fun x => p.eval x)) /ₘ vanishing points

theorem deepQuotient_reconstruct (points : Finset F) (p : F[X]) :
    vanishing points * deepQuotient points p = p - interpolate points (fun x => p.eval x) := by
  have divides : vanishing points ∣ p - interpolate points (fun x => p.eval x) :=
    prod_X_sub_C_dvd points id Function.injective_id.injOn _ (by
      intro x member
      rw [eval_sub]
      change p.eval x - (interpolate points (fun x => p.eval x)).eval x = 0
      rw [interpolate_eval points _ ⟨x, member⟩, sub_self])
  have law := modByMonic_add_div (p - interpolate points (fun x => p.eval x)) (vanishing points)
  rw [(modByMonic_eq_zero_iff_dvd (vanishing_monic points)).mpr divides, zero_add] at law
  exact law

theorem deepQuotient_degree_lt {points : Finset F} {p : F[X]} {degree : ℕ}
    (size : points.card ≤ degree) (bounded : p.degree < degree) :
    (deepQuotient points p).degree < ((degree - points.card : ℕ) : WithBot ℕ) := by
  apply factor_degree_lt (p := p - interpolate points (fun x => p.eval x))
  · exact (degree_sub_le _ _).trans_lt
      (max_lt bounded ((interpolate_degree_lt points _).trans_le (by exact_mod_cast size)))
  · exact (deepQuotient_reconstruct points p).symm

theorem deepQuotient_eval {points : Finset F} (p : F[X]) {x : F} (outside : x ∉ points) :
    (deepQuotient points p).eval x =
      (p.eval x - (interpolate points (fun z => p.eval z)).eval x) / (vanishing points).eval x := by
  have nonzero : (vanishing points).eval x ≠ 0 :=
    fun zero => outside ((vanishing_eval_zero_iff points x).mp zero)
  rw [eq_div_iff nonzero, mul_comm, ← eval_mul, deepQuotient_reconstruct, eval_sub]

/-- Every claimed answer is recovered when a quotient is lifted back. -/
theorem lift_answers (points : Finset F) (answers : points → F) (q : F[X]) (x : points) :
    (vanishing points * q + interpolate points answers).eval (x : F) = answers x := by
  rw [eval_add, eval_mul, (vanishing_eval_zero_iff points x).mpr x.property,
    zero_mul, zero_add, interpolate_eval]

end ZkcSecurity.Families.Stark
