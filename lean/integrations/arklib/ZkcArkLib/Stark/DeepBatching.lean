module

public import ZkcArkLib.Stark.Quotient
public import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.JointAgreement
public import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds.Powers

@[expose] public section

/-! Proved proximity seams for fixed words with a common target code: affine
two-word agreement and many-word power batching below the generalized Johnson
radius. The power bound is from pinned ArkLib's `CapacityBounds.Powers`, not
the admitted general STIR degree-corrected combination theorem. -/

namespace ZkcArkLib.Stark
open scoped NNReal ENNReal
open scoped BigOperators

variable {F Index : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype Index] [Nonempty Index]

/-- More than `|Index| / |F|` close affine combinations force the two words to
agree with codewords on one common set of at least `(1 - radius) |Index|`
coordinates. The target is the caller's chosen reduced-degree code. -/
theorem affine_jointAgreement [SampleableType F] (domain : Index ↪ F)
    (degree : ℕ) (radius : ℝ≥0) (words : Fin 2 → Index → F)
    (uniqueRadius : radius ≤ Code.relativeUniqueDecodingRadius
      (ReedSolomon.code domain degree : Set (Index → F)))
    (closeProbability :
      Pr{let challenge ← $ᵗ F}[
        Code.relDistFromCode (words 0 + challenge • words 1)
          (ReedSolomon.code domain degree) ≤ radius] >
            ((Fintype.card Index : ℝ≥0) / (Fintype.card F : ℝ≥0) : ℝ≥0∞)) :
    Code.jointAgreement (C := ReedSolomon.code domain degree) (δ := radius) (W := words) :=
  ProximityGap.RS_jointAgreement_of_goodCoeffs_card_gt uniqueRadius words
    (ProximityGap.card_RS_goodCoeffs_gt_of_prob_gt_n_div_q words closeProbability)

open LinearCode CoreDefinitions

omit [Fintype F] in
/-- A large projected codeword extension is exactly proximity to the code.
The real size threshold avoids rounding or silently changing the radius. -/
private theorem projected_close_iff (code : LinearCode Index F) (word : Index → F)
    (radius : ℝ≥0) :
    (∃ T : Finset Index, (T.card : ℝ) ≥ Fintype.card Index * (1 - (radius : ℝ)) ∧
      projectedWord word T ∈ projectedCodeSubmod code T) ↔
      Code.relDistFromCode word code ≤ radius := by
  classical
  constructor
  · rintro ⟨T, size, projected⟩
    obtain ⟨c, member, agrees⟩ := (mem_projectedCodeSubmod_iff code T _).mp projected
    apply (Code.relCloseToCode_iff_relCloseToCodeword_of_minDist word radius).mpr
    refine ⟨c, member, ?_⟩
    have count : T.card ≤ Code.agree word c := by
      apply Finset.card_le_card
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, congrFun agrees ⟨i, hi⟩⟩
    have total : (Code.agree word c : ℝ) + hammingDist word c = Fintype.card Index := by
      exact_mod_cast (Code.agree_add_hammingDist (u := word) (v := c))
    have countReal : (T.card : ℝ) ≤ Code.agree word c := by exact_mod_cast count
    have distance : (Code.relHammingDist word c : ℝ) ≤ (radius : ℝ) := by
      rw [Code.relHammingDist_coe, div_le_iff₀ (by exact_mod_cast Fintype.card_pos (α := Index))]
      nlinarith
    exact_mod_cast distance
  · intro close
    obtain ⟨c, member, distance⟩ :=
      (Code.relCloseToCode_iff_relCloseToCodeword_of_minDist word radius).mp close
    let T := Finset.univ.filter fun i => word i = c i
    have total : (T.card : ℝ) + hammingDist word c = Fintype.card Index := by
      exact_mod_cast (Code.agree_add_hammingDist (u := word) (v := c))
    have distanceReal : (Code.relHammingDist word c : ℝ) ≤ (radius : ℝ) := by
      exact_mod_cast distance
    rw [Code.relHammingDist_coe,
      div_le_iff₀ (by exact_mod_cast Fintype.card_pos (α := Index))] at distanceReal
    refine ⟨T, by nlinarith, (mem_projectedCodeSubmod_iff code T _).mpr ⟨c, member, ?_⟩⟩
    funext i
    exact (Finset.mem_filter.mp i.property).2

/-- A close power combination with even one far input is an MCA error.
Neither the fixed input family nor the common target code depends on gamma. -/
theorem powerBatch_bad_implies_isMCA (code : LinearCode Index F) (k : ℕ)
    (words : Fin (k + 1) → Index → F) (radius : ℝ≥0) (gamma : F)
    (close : Code.relDistFromCode (fun i => ∑ j : Fin (k + 1), gamma ^ (j : ℕ) * words j i) code ≤ radius)
    (far : ∃ j, (radius : ℝ≥0∞) < Code.relDistFromCode (words j) code) :
    IsMCA (univariatePowersGenerator F k) code gamma words (radius : ℝ) := by
  obtain ⟨T, size, projected⟩ := (projected_close_iff code _ radius).mpr close
  obtain ⟨j, far⟩ := far
  refine ⟨T, size, projected, j, ?_⟩
  intro extension
  exact (not_le_of_gt far) ((projected_close_iff code (words j) radius).mp ⟨T, size, extension⟩)

/-- Outside the MCA exception, one far input forces the actual batch to be far. -/
theorem powerBatch_distance_gt_of_not_isMCA (code : LinearCode Index F) (k : ℕ)
    (words : Fin (k + 1) → Index → F) (radius : ℝ≥0) (gamma : F)
    (outside : ¬ IsMCA (univariatePowersGenerator F k) code gamma words (radius : ℝ))
    (far : ∃ j, (radius : ℝ≥0∞) < Code.relDistFromCode (words j) code) :
    (radius : ℝ≥0∞) <
      Code.relDistFromCode (fun i => ∑ j : Fin (k + 1), gamma ^ (j : ℕ) * words j i) code :=
  lt_of_not_ge fun close => outside (powerBatch_bad_implies_isMCA code k words radius gamma close far)

/-- Exact ENNReal expression in ArkLib's proved power-generator capacity bound.
Here `k + 1` is the number of words, not the common code's degree. -/
noncomputable def powerBatchError (length fieldSize k : ℕ) (minDistance slack : ℝ≥0) : ℝ≥0∞ :=
  ENNReal.ofReal
    ((((length : ℝ) *
          (1 - (1 - (minDistance : ℝ) + (slack : ℝ)) ^ ((1 : ℝ) / (k + 1)))) / slack)
        * ((k : ℝ) / fieldSize)
      + max
          (2 * (k : ℝ) /
            ((slack : ℝ) *
              ((1 - (minDistance : ℝ) + (slack : ℝ)) ^ ((1 : ℝ) / (k + 2)) -
                (1 - (minDistance : ℝ) + (slack : ℝ)) ^ ((1 : ℝ) / (k + 1))) * fieldSize))
          (((k : ℝ) + 1) * ((k : ℝ) + 2) / ((slack : ℝ) * fieldSize)))

/-- Uniform gamma and its powers preserve proximity for many fixed words,
except with this explicit error. All upstream admission premises are retained. -/
theorem powerBatch_distance_uniform_le [SampleableType F]
    (code : LinearCode Index F) (k : ℕ) (words : Fin (k + 1) → Index → F)
    (minDistance slack radius : ℝ≥0) (many : 1 ≤ k) (cardinality : k + 1 ≤ Fintype.card F)
    (minimum : (minDistance : ℝ) =
      (Code.minDist (code : Set (Index → F)) : ℝ) / Fintype.card Index)
    (positive : 0 < slack) (below : slack < minDistance)
    (admitted : (radius : ℝ) ≤
      1 - (1 - (minDistance : ℝ) + (slack : ℝ)) ^ ((1 : ℝ) / (k + 2))) :
    Pr{let gamma ← $ᵗ F}[
      Code.relDistFromCode (fun i => ∑ j : Fin (k + 1), gamma ^ (j : ℕ) * words j i) code ≤ radius ∧
        ∃ j, (radius : ℝ≥0∞) < Code.relDistFromCode (words j) code] ≤
      powerBatchError (Fintype.card Index) (Fintype.card F) k minDistance slack := by
  calc
    _ ≤ Pr{let gamma ← $ᵗ F}[
        IsMCA (univariatePowersGenerator F k) code gamma words (radius : ℝ)] :=
      prEvent_mono _ _ _ fun gamma bad =>
        powerBatch_bad_implies_isMCA code k words radius gamma bad.1 bad.2
    _ ≤ mcaError (univariatePowersGenerator F k) code (radius : ℝ) :=
      le_iSup (fun U : Fin (k + 1) → Index → F =>
        Pr{let gamma ← $ᵗ F}[IsMCA (univariatePowersGenerator F k) code gamma U (radius : ℝ)]) words
    _ ≤ _ := CodingTheory.linear_mcaError_powers_le code k minDistance slack radius
      many cardinality minimum positive below admitted

/-- A client with a fixed far input can directly bound the close-batch event. -/
theorem powerBatch_close_uniform_le [SampleableType F]
    (code : LinearCode Index F) (k : ℕ) (words : Fin (k + 1) → Index → F)
    (minDistance slack radius : ℝ≥0) (many : 1 ≤ k) (cardinality : k + 1 ≤ Fintype.card F)
    (minimum : (minDistance : ℝ) =
      (Code.minDist (code : Set (Index → F)) : ℝ) / Fintype.card Index)
    (positive : 0 < slack) (below : slack < minDistance)
    (admitted : (radius : ℝ) ≤
      1 - (1 - (minDistance : ℝ) + (slack : ℝ)) ^ ((1 : ℝ) / (k + 2)))
    (far : ∃ j, (radius : ℝ≥0∞) < Code.relDistFromCode (words j) code) :
    Pr{let gamma ← $ᵗ F}[
      Code.relDistFromCode (fun i => ∑ j : Fin (k + 1), gamma ^ (j : ℕ) * words j i) code ≤ radius] ≤
      powerBatchError (Fintype.card Index) (Fintype.card F) k minDistance slack := by
  exact (prEvent_mono _ _ _ fun _ close => ⟨close, far⟩).trans
    (powerBatch_distance_uniform_le code k words minDistance slack radius
      many cardinality minimum positive below admitted)

/-- Quotient words may use different answer sets, but all remove the same
number of distinct points from the same degree budget. A separated original
word supplies the far quotient via `quotient_distance_gt`. This is common-degree
power batching, without STIR degree correction or native correspondence. -/
theorem quotient_powerBatch_close_uniform_le [SampleableType F] [DecidableEq Index]
    (domain : Index ↪ F) (k degree removed : ℕ)
    (points : Fin (k + 1) → Finset F) (answers : ∀ j, points j → F)
    (words : Fin (k + 1) → Index → F)
    (sizes : ∀ j, (points j).card = removed) (size : removed < degree)
    (rate : degree ≤ Fintype.card Index) (outside : ∀ j i, domain i ∉ points j)
    (minDistance slack radius : ℝ≥0) (many : 1 ≤ k) (cardinality : k + 1 ≤ Fintype.card F)
    (minimum : (minDistance : ℝ) =
      (Code.minDist (ReedSolomon.code domain (degree - removed) : Set (Index → F)) : ℝ) /
        Fintype.card Index)
    (positive : 0 < slack) (below : slack < minDistance)
    (admitted : (radius : ℝ) ≤
      1 - (1 - (minDistance : ℝ) + (slack : ℝ)) ^ ((1 : ℝ) / (k + 2)))
    (disagrees : ∃ j, ∀ u : ReedSolomon.code domain degree,
      u.val ∈ Code.closeCodewordsRel (ReedSolomon.code domain degree) (words j) radius →
        ∃ x : points j, (ReedSolomon.toPolynomialLT u : Polynomial F).eval (x : F) ≠ answers j x) :
    Pr{let gamma ← $ᵗ F}[
      Code.relDistFromCode
        (fun i => ∑ j : Fin (k + 1), gamma ^ (j : ℕ) *
          ((words j i - (ZkcSecurity.Families.Stark.interpolate (points j) (answers j)).eval (domain i)) /
            (ZkcSecurity.Families.Stark.vanishing (points j)).eval (domain i)))
        (ReedSolomon.code domain (degree - removed)) ≤ radius] ≤
      powerBatchError (Fintype.card Index) (Fintype.card F) k minDistance slack := by
  apply powerBatch_close_uniform_le _ k _ minDistance slack radius
    many cardinality minimum positive below admitted
  obtain ⟨j, disagrees⟩ := disagrees
  refine ⟨j, ?_⟩
  have far := quotient_distance_gt domain (points j) (words j) (answers j)
    (by simpa only [sizes j] using size) rate (outside j) radius disagrees
  simpa only [sizes j] using far

end ZkcArkLib.Stark
