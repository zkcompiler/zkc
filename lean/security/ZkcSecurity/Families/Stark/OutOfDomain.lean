module

public import ZkcSecurity.Families.Stark.Quotient

@[expose] public section

/-! Typed out-of-domain challenges. Cardinality and uniformity are explicit;
an empty complement cannot be supplied with a lossless uniform sampler. -/

namespace ZkcSecurity.Families.Stark
open _root_.Polynomial OracleComp
open scoped ENNReal

variable {F Index : Type} [Fintype F] [DecidableEq F] [Fintype Index]

def outsidePoints (domain : Index ↪ F) : Finset F :=
  Finset.univ \ Finset.image domain Finset.univ

theorem mem_outsidePoints (domain : Index ↪ F) (x : F) :
    x ∈ outsidePoints domain ↔ ∀ i, domain i ≠ x := by
  simp [outsidePoints]

theorem outsidePoints_card (domain : Index ↪ F) :
    (outsidePoints domain).card = Fintype.card F - Fintype.card Index := by
  rw [outsidePoints, Finset.card_sdiff]
  simp only [Finset.inter_univ, Finset.card_univ,
    Finset.card_image_of_injective _ domain.injective]

theorem outsidePoints_nonempty_iff (domain : Index ↪ F) :
    (outsidePoints domain).Nonempty ↔ Fintype.card Index < Fintype.card F := by
  rw [← Finset.card_pos, outsidePoints_card, Nat.sub_pos_iff_lt]

omit [Fintype F] in
/-- The root bound on the actual finite sample carrier; its denominator is
the carrier size, not the size of the ambient field. -/
theorem roots_on_set_uniform_le [Field F] (points : Finset F) [SampleableType ↥points]
    (p : F[X]) (nonzero : p ≠ 0) :
    Pr{let x ← $ᵗ ↥points}[p.eval (x : F) = 0] ≤
      (p.natDegree : ℝ≥0∞) / points.card := by
  classical
  rw [SampleableType.prEvent_uniformSample, Fintype.card_coe]
  apply ENNReal.div_le_div_right
  exact_mod_cast card_eval_zero_le_natDegree Finset.univ
    (fun x : points => (x : F)) Subtype.val_injective.injOn p nonzero

/-- Two fixed degree-below-`degree` polynomials collide under a uniform
OOD draw with probability at most `(degree - 1) / (|F| - |Index|)`. -/
theorem outside_agreement_uniform_le [Field F] (domain : Index ↪ F)
    [SampleableType ↥(outsidePoints domain)] {p q : F[X]} {degree : ℕ}
    (different : p ≠ q) (left : p.degree < degree) (right : q.degree < degree) :
    Pr{let x ← $ᵗ ↥(outsidePoints domain)}[p.eval (x : F) = q.eval (x : F)] ≤
      ((degree - 1 : ℕ) : ℝ≥0∞) / (Fintype.card F - Fintype.card Index : ℕ) := by
  have nonzero : p - q ≠ 0 := sub_ne_zero.mpr different
  have bounded : (p - q).natDegree ≤ degree - 1 := by
    have lt := (natDegree_lt_iff_degree_lt nonzero).mpr
      ((degree_sub_le p q).trans_lt (max_lt left right))
    omega
  have roots := roots_on_set_uniform_le (outsidePoints domain) (p - q) nonzero
  simp only [eval_sub, sub_eq_zero, outsidePoints_card] at roots
  exact roots.trans (ENNReal.div_le_div_right (by exact_mod_cast bounded) _)

omit [DecidableEq F] in
/-- Useful admission gate: the stated error is nontrivial only when the
remaining root budget is smaller than the actual complement. -/
theorem outside_error_lt_one (_domain : Index ↪ F) {rootBudget : ℕ}
    (size : rootBudget < Fintype.card F - Fintype.card Index) :
    (rootBudget : ℝ≥0∞) / (Fintype.card F - Fintype.card Index : ℕ) < 1 := by
  have positive : ((Fintype.card F - Fintype.card Index : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (show Fintype.card F - Fintype.card Index ≠ 0 by omega)
  rw [ENNReal.div_lt_iff (Or.inl positive) (by simp), one_mul]
  exact_mod_cast size

end ZkcSecurity.Families.Stark
