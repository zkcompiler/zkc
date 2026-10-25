module

public import CompPoly.ToMathlib.Polynomial.Roots
public import VCVio.OracleComp.Constructions.SampleableType.Measure

@[expose] public section

/-! Uniform univariate polynomial tests, independent of a protocol family.
Both polynomials are fixed before sampling. Applying these bounds to an actual
protocol additionally requires its conditional-distribution and binding laws. -/
set_option autoImplicit false
namespace ZkcSecurity.Algebra.Polynomial
open _root_.Polynomial OracleComp OracleSpec
open scoped ENNReal
variable {F : Type} [Field F]

/-- CompPoly's root bound, with both polynomial degrees exposed independently. -/
theorem agreement_card_le [Fintype F] [DecidableEq F] (p q : Polynomial F)
    (different : p ≠ q) {leftDegree rightDegree : Nat}
    (left : p.natDegree ≤ leftDegree) (right : q.natDegree ≤ rightDegree) :
    (Finset.univ.filter (fun r => p.eval r = q.eval r)).card ≤
      max leftDegree rightDegree := by
  have nonzero : p - q ≠ 0 := sub_ne_zero.mpr different
  have roots := card_eval_zero_le_natDegree Finset.univ id
    (Function.injective_id.injOn) (p - q) nonzero
  simp only [id_eq, eval_sub, sub_eq_zero] at roots
  exact roots.trans ((natDegree_sub_le p q).trans (max_le_max left right))

theorem agreement_uniform_le [Fintype F] [DecidableEq F] [SampleableType F]
    (p q : Polynomial F) (different : p ≠ q) {leftDegree rightDegree : Nat}
    (left : p.natDegree ≤ leftDegree) (right : q.natDegree ≤ rightDegree) :
    Pr{let r ← $ᵗ F}[p.eval r = q.eval r] ≤
      ((max leftDegree rightDegree : Nat) : ℝ≥0∞) / Fintype.card F := by
  rw [SampleableType.prEvent_uniformSample]
  refine ENNReal.div_le_div_right ?_ _
  exact_mod_cast agreement_card_le p q different left right

theorem root_uniform_le [Fintype F] [DecidableEq F] [SampleableType F]
    (p : Polynomial F) (nonzero : p ≠ 0) {degree : Nat} (bounded : p.natDegree ≤ degree) :
    Pr{let r ← $ᵗ F}[p.eval r = 0] ≤ (degree : ℝ≥0∞) / Fintype.card F := by
  simpa only [eval_zero, max_self] using
    agreement_uniform_le p 0 nonzero bounded (show (0 : Polynomial F).natDegree ≤ degree by simp)

end ZkcSecurity.Algebra.Polynomial
