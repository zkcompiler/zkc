module

public import ZkcSecurity.Families.Stark.Batching

@[expose] public section

/-! Exact DEEP batching algebra. Quotienting by the *same* point set commutes
with power batching. Answers are evaluations of the fixed input polynomials;
adversarial answer claims need the separate quotienting proximity adapter. -/

namespace ZkcSecurity.Families.Stark
open _root_.Polynomial
open scoped BigOperators

variable {F : Type} [Field F] [DecidableEq F] {count : ℕ}

theorem interpolate_powerBatch (points : Finset F) (polynomials : Fin count → F[X])
    (challenge : F) :
    interpolate points (fun x => (powerBatch polynomials challenge).eval x) =
      powerBatch (fun i => interpolate points (fun x => (polynomials i).eval x)) challenge := by
  symm
  apply Lagrange.eq_interpolate_of_eval_eq _ Subtype.val_injective.injOn
  · simpa using powerBatch_degree_lt
      (fun i => interpolate points (fun x => (polynomials i).eval x))
      (fun _ => interpolate_degree_lt points _) challenge
  · intro x _
    simp only [powerBatch_eval, interpolate_eval]

theorem deepQuotient_powerBatch (points : Finset F) (polynomials : Fin count → F[X])
    (challenge : F) :
    deepQuotient points (powerBatch polynomials challenge) =
      powerBatch (fun i => deepQuotient points (polynomials i)) challenge := by
  apply mul_left_cancel₀ (vanishing_monic points).ne_zero
  rw [deepQuotient_reconstruct, interpolate_powerBatch]
  simp only [powerBatch, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_left_comm, deepQuotient_reconstruct, mul_sub]

/-- The low-degree target is the remaining budget after *all distinct points*
have been removed. Repeated OOD samples form a set for this purpose. -/
theorem deepBatch_degree_lt (points : Finset F) (polynomials : Fin count → F[X])
    {degree : ℕ} (size : points.card ≤ degree)
    (bounded : ∀ i, (polynomials i).degree < degree) (challenge : F) :
    (powerBatch (fun i => deepQuotient points (polynomials i)) challenge).degree <
      ((degree - points.card : ℕ) : WithBot ℕ) :=
  powerBatch_degree_lt _ (fun i => deepQuotient_degree_lt size (bounded i)) challenge

/-- The same quotient values lift to the same original values away from the
quotient points; this is the pointwise seam used by a later committed-word client. -/
theorem lift_agreement {Index : Type} (domain : Index ↪ F) (points : Finset F)
    (answers : points → F) (word : Index → F) (q : F[X]) (x : Index)
    (outside : domain x ∉ points)
    (agrees : q.eval (domain x) =
      (word x - (interpolate points answers).eval (domain x)) / (vanishing points).eval (domain x)) :
    (vanishing points * q + interpolate points answers).eval (domain x) = word x := by
  have nonzero : (vanishing points).eval (domain x) ≠ 0 :=
    fun zero => outside ((vanishing_eval_zero_iff points _).mp zero)
  rw [eval_add, eval_mul, agrees, mul_div_cancel₀ _ nonzero, sub_add_cancel]

end ZkcSecurity.Families.Stark
