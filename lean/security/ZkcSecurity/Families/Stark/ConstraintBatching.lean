module

public import ZkcSecurity.Families.Stark.Batching
public import ZkcSecurity.Families.Stark.OutOfDomain
public import VCVio.EvalDist.ProbabilityBounds

@[expose] public section

/-! A complete two-challenge constraint identity test. The polynomials and
their degree bounds are fixed before either draw. The same theorem applies
to quotient residuals, whose bounds must include the supplied quotients. -/

namespace ZkcSecurity.Families.Stark
open _root_.Polynomial OracleComp
open scoped BigOperators ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F] {count : ℕ}

/-- Independent uniform batching and evaluation, on an explicitly selected
finite carrier. The two losses account for a zero batch and for an accidental
evaluation root of a nonzero batch. -/
theorem constraint_test_uniform_le (polynomials : Fin count → F[X])
    (invalid : ∃ i, polynomials i ≠ 0) {degree : ℕ}
    (bounded : ∀ i, (polynomials i).natDegree ≤ degree)
    (points : Finset F) [SampleableType ↥points] :
    Pr{let challenge ← $ᵗ F; let x ← $ᵗ ↥points}[
      (powerBatch polynomials challenge).eval (x : F) = 0] ≤
        ((count - 1 : ℕ) : ℝ≥0∞) / Fintype.card F + (degree : ℝ≥0∞) / points.card := by
  have step := prEvent_bind_le_prEvent_add_of_support ($ᵗ F)
    (fun challenge => (fun x : points => (powerBatch polynomials challenge).eval (x : F)) <$>
      ($ᵗ ↥points))
    (fun challenge => powerBatch polynomials challenge = 0) (fun value => value = 0)
    (ε := (degree : ℝ≥0∞) / points.card) (by
      intro challenge _ nonzero
      have batchDegree : (powerBatch polynomials challenge).natDegree ≤ degree :=
        natDegree_sum_le_of_forall_le _ _ (fun i _ => (natDegree_C_mul_le _ _).trans (bounded i))
      have castDegree : ((powerBatch polynomials challenge).natDegree : ℝ≥0∞) ≤ (degree : ℝ≥0∞) := by
        exact_mod_cast batchDegree
      simpa only [prEvent_map, Function.comp_def] using
        (roots_on_set_uniform_le points _ nonzero).trans
          (ENNReal.div_le_div_right castDegree _))
  simpa only [map_bind, Functor.map_map, Function.comp_def] using
    step.trans (add_le_add (powerBatch_zero_uniform_le polynomials invalid) le_rfl)

end ZkcSecurity.Families.Stark
