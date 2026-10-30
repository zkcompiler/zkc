module

public import ZkcSecurity.Families.Stark.Quotient
public import Mathlib.Algebra.MvPolynomial.SchwartzZippel

@[expose] public section

/-! Power batching of fixed polynomial constraints. A uniform field challenge
is sampled after the polynomials have been fixed. This is an exact identity
test, not a proximity theorem for an adaptively chosen low-degree polynomial. -/

namespace ZkcSecurity.Families.Stark
open _root_.Polynomial OracleComp
open scoped BigOperators NNReal ENNReal

variable {F : Type} [Field F] {count : ℕ}

noncomputable def powerBatch (polynomials : Fin count → F[X]) (challenge : F) : F[X] :=
  ∑ i, C (challenge ^ i.val) * polynomials i

theorem powerBatch_eval (polynomials : Fin count → F[X]) (challenge x : F) :
    (powerBatch polynomials challenge).eval x = ∑ i, challenge ^ i.val * (polynomials i).eval x := by
  simp only [powerBatch, eval_finsetSum, eval_mul, eval_C]

/-- One coefficient of the batch, viewed as a polynomial in the challenge. -/
noncomputable def coefficientTest (polynomials : Fin count → F[X]) (coefficient : ℕ) : F[X] :=
  ∑ i, C ((polynomials i).coeff coefficient) * X ^ i.val

theorem coefficientTest_coeff (polynomials : Fin count → F[X]) (coefficient : ℕ)
    (i : Fin count) :
    (coefficientTest polynomials coefficient).coeff i.val = (polynomials i).coeff coefficient := by
  classical
  simp only [coefficientTest, finsetSum_coeff, coeff_C_mul_X_pow]
  simp [← Fin.ext_iff]

theorem coefficientTest_eval (polynomials : Fin count → F[X]) (coefficient : ℕ) (challenge : F) :
    (coefficientTest polynomials coefficient).eval challenge =
      (powerBatch polynomials challenge).coeff coefficient := by
  simp only [coefficientTest, powerBatch, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X,
    finsetSum_coeff, coeff_C_mul]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem powerBatch_degree_lt (polynomials : Fin count → F[X]) {degree : ℕ}
    (bounded : ∀ i, (polynomials i).degree < degree) (challenge : F) :
    (powerBatch polynomials challenge).degree < degree := by
  classical
  rw [degree_lt_iff_coeff_zero]
  intro coefficient high
  simp only [powerBatch, finsetSum_coeff, coeff_C_mul]
  apply Finset.sum_eq_zero
  intro i _
  rw [((degree_lt_iff_coeff_zero _ _).mp (bounded i)) coefficient high, mul_zero]

theorem powerBatch_residual [DecidableEq F] (points : Finset F)
    (numerators quotients : Fin count → F[X]) (challenge : F) :
    powerBatch (fun i => residual points (numerators i) (quotients i)) challenge =
      residual points (powerBatch numerators challenge) (powerBatch quotients challenge) := by
  simp only [powerBatch, residual, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A nonzero constraint gives a nonzero challenge polynomial. Its degree is
`count - 1`, regardless of the constraints' degrees in their other variable. -/
theorem powerBatch_zero_uniform_le [Fintype F] [DecidableEq F] [SampleableType F]
    (polynomials : Fin count → F[X]) (invalid : ∃ i, polynomials i ≠ 0) :
    Pr{let challenge ← $ᵗ F}[powerBatch polynomials challenge = 0] ≤
      ((count - 1 : ℕ) : ℝ≥0∞) / Fintype.card F := by
  classical
  obtain ⟨i, invalid⟩ := invalid
  obtain ⟨coefficient, nonzero⟩ : ∃ k, (polynomials i).coeff k ≠ 0 := by
    by_contra none
    exact invalid (Polynomial.ext (by simpa using none))
  have test_ne : coefficientTest polynomials coefficient ≠ 0 := by
    intro zero
    apply nonzero
    have equality := congrArg (fun p : F[X] => p.coeff i.val) zero
    simpa only [coefficientTest_coeff, coeff_zero] using equality
  have bounded : (coefficientTest polynomials coefficient).natDegree ≤ count - 1 := by
    have lt := (natDegree_lt_iff_degree_lt test_ne).mpr
      (degree_sum_fin_lt (fun j => (polynomials j).coeff coefficient))
    omega
  apply le_trans (prEvent_mono _ _ _ (fun challenge zero => ?_))
    (ZkcSecurity.Algebra.Polynomial.root_uniform_le _ test_ne bounded)
  rw [coefficientTest_eval, zero, coeff_zero]

/-- Multivariate constraints require the *total* degree. A bound on each
individual variable cannot be substituted for `totalDegree` here. The draw is
uniform on the full product, so its coordinates are independent. -/
theorem multivariate_zero_uniform_le [Fintype F] [SampleableType F] {dimension : ℕ}
    (p : MvPolynomial (Fin dimension) F) (nonzero : p ≠ 0) :
    Pr{let point ← $ᵗ (Fin dimension → F)}[MvPolynomial.eval point p = 0] ≤
      (p.totalDegree : ℝ≥0∞) / Fintype.card F := by
  classical
  rw [SampleableType.prEvent_uniformSample, Fintype.card_fun, Fintype.card_fin]
  have bound := MvPolynomial.schwartz_zippel_totalDegree nonzero (Finset.univ : Finset F)
  simp only [Fintype.piFinset_univ, Finset.card_univ] at bound
  have realBound := (NNRat.cast_le (K := ℝ≥0)).mpr bound
  push_cast at realBound
  have lifted := ENNReal.coe_le_coe.mpr realBound
  have size_ne : (Fintype.card F : ℝ≥0) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [ENNReal.coe_div (pow_ne_zero dimension size_ne), ENNReal.coe_div size_ne] at lifted
  simpa only [ENNReal.coe_natCast, ENNReal.coe_pow, Nat.cast_pow] using lifted

end ZkcSecurity.Families.Stark
