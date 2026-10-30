import ZkcSecurity.Families.Stark.ConstraintBatching
import ZkcSecurity.Families.Stark.DeepBatching
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import ZkcTools.DeclarationAudit

/-! Kernel-checked finite-field controls and instantiations. No native decision
procedure is used. These are mathematical controls, not STARK parameter claims. -/

namespace TestsSecurity.Stark
open Polynomial ZkcSecurity.Families.Stark OracleComp
open scoped BigOperators NNReal ENNReal

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
noncomputable local instance : SampleableType (ZMod 3) := SampleableType.ofFintype _
noncomputable local instance : SampleableType ↥(Finset.univ : Finset (ZMod 3)) :=
  SampleableType.finsetCoe _ ⟨0, Finset.mem_univ _⟩

/-- A degree equal to the field size can vanish everywhere without being zero. -/
theorem fieldSize_polynomial_nonzero : (X ^ 3 - X : Polynomial (ZMod 3)) ≠ 0 := by
  intro zero
  have coefficient := congrArg (fun p : Polynomial (ZMod 3) => p.coeff 3) zero
  norm_num [coeff_X] at coefficient

theorem fieldSize_polynomial_all_roots :
    ∀ x : ZMod 3, (X ^ 3 - X : Polynomial (ZMod 3)).eval x = 0 := by
  simp only [eval_sub, eval_pow, eval_X]
  decide

/-- The degree/field-size root bound is exactly one in this control. -/
theorem fieldSize_test_probability :
    Pr{let x ← $ᵗ (ZMod 3)}[(X ^ 3 - X : Polynomial (ZMod 3)).eval x = 0] = 1 :=
  (SampleableType.prEvent_uniformSample_eq_one_iff _).mpr fieldSize_polynomial_all_roots

/-- Two variables of individual degree one have total degree two. -/
theorem individual_degree_control (i : Fin 2) :
    (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X 1 : MvPolynomial (Fin 2) (ZMod 3)).degreeOf i ≤ 1 := by
  have bound := MvPolynomial.degreeOf_mul_le i
    (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) (ZMod 3)) (MvPolynomial.X 1)
  fin_cases i <;> norm_num [MvPolynomial.degreeOf_X] at bound ⊢ <;> exact bound

/-- An individual-degree numerator `1` would give the false bound `1/3`:
the independent two-coordinate uniform draw has five zeroes among nine points. -/
theorem multivariate_zero_probability :
    Pr{let x ← $ᵗ (Fin 2 → ZMod 3)}[
      MvPolynomial.eval x (MvPolynomial.X 0 * MvPolynomial.X 1) = 0] = 5 / 9 := by
  rw [SampleableType.prEvent_uniformSample]
  simp only [MvPolynomial.eval_mul, MvPolynomial.eval_X]
  have count : (Finset.univ.filter (fun x : Fin 2 → ZMod 3 => x 0 * x 1 = 0)).card = 5 := by decide
  rw [count]
  norm_num [Fintype.card_fun, ZMod.card]

theorem individual_degree_bound_false :
    ¬ Pr{let x ← $ᵗ (Fin 2 → ZMod 3)}[
      MvPolynomial.eval x (MvPolynomial.X 0 * MvPolynomial.X 1) = 0] ≤ 1 / 3 := by
  rw [multivariate_zero_probability]
  intro bad
  have realBad := (ENNReal.toReal_le_toReal (by finiteness : (5 / 9 : ℝ≥0∞) ≠ ⊤)
    (by finiteness : (1 / 3 : ℝ≥0∞) ≠ ⊤)).mpr bad
  norm_num [ENNReal.toReal_div] at realBad

/-- The correct reusable total-degree contract gives `2/3`. -/
theorem multivariate_bound :
    Pr{let x ← $ᵗ (Fin 2 → ZMod 3)}[
      MvPolynomial.eval x (MvPolynomial.X 0 * MvPolynomial.X 1) = 0] ≤ 2 / 3 := by
  have nonzero : (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X 1 :
      MvPolynomial (Fin 2) (ZMod 3)) ≠ 0 := mul_ne_zero (MvPolynomial.X_ne_zero 0) (MvPolynomial.X_ne_zero 1)
  have bound := multivariate_zero_uniform_le _ nonzero
  norm_num [MvPolynomial.totalDegree_mul_of_isDomain (MvPolynomial.X_ne_zero (0 : Fin 2))
    (MvPolynomial.X_ne_zero 1), MvPolynomial.totalDegree_X, ZMod.card] at bound ⊢
  exact bound

/-- A small numerator does not bound the residual of a large supplied quotient. -/
theorem quotient_degree_control :
    (0 : Polynomial (ZMod 3)).natDegree = 0 ∧
      (ZkcSecurity.Families.Stark.residual ({0} : Finset (ZMod 3))
        (0 : Polynomial (ZMod 3)) (X ^ 5)).natDegree = 6 := by
  simp [ZkcSecurity.Families.Stark.residual, vanishing, Lagrange.nodal, natDegree_mul]

/-- Exhausted strict budgets still admit the zero quotient. -/
theorem zero_remaining_budget :
    ∃ q : Polynomial (ZMod 3), 0 = vanishing ({0, 1} : Finset (ZMod 3)) * q ∧ q.degree < (0 : ℕ) := by
  exact ⟨0, by simp, by simp⟩

/-- A typed empty complement cannot be admitted as an OOD challenge carrier. -/
theorem full_domain_no_outside : outsidePoints (Function.Embedding.refl (ZMod 3)) = ∅ := by
  apply Finset.card_eq_zero.mp
  rw [outsidePoints_card, Nat.sub_self]

/-- One-point DEEP removal from a quadratic has a degree-below-two target. -/
theorem deep_quadratic_degree :
    (deepQuotient ({0} : Finset (ZMod 3)) (X ^ 2 + 1)).degree < (2 : ℕ) := by
  apply deepQuotient_degree_lt (degree := 3) (by simp)
  exact (degree_add_le _ _).trans_lt (by norm_num)

/-- The two-stage constraint theorem instantiates with explicit challenge and
residual degrees. A useful numerical bound still requires a large enough field. -/
theorem constraint_bound (polynomials : Fin 2 → Polynomial (ZMod 3))
    (invalid : ∃ i, polynomials i ≠ 0) (bounded : ∀ i, (polynomials i).natDegree ≤ 1) :
    Pr{let challenge ← $ᵗ (ZMod 3); let x ← $ᵗ ↥(Finset.univ : Finset (ZMod 3))}[
      (powerBatch polynomials challenge).eval (x : ZMod 3) = 0] ≤ 1 / 3 + 1 / 3 := by
  have bound := constraint_test_uniform_le polynomials invalid bounded (Finset.univ : Finset (ZMod 3))
  norm_num [ZMod.card] at bound ⊢
  exact bound

end TestsSecurity.Stark

run_cmd ZkcTools.DeclarationAudit.check [`ZkcSecurity.Families.Stark] "STARK-SECURITY-AUDIT-PASS"
run_cmd ZkcTools.DeclarationAudit.checkCurrent "STARK-CONTROLS-AXIOMS-PASS"
