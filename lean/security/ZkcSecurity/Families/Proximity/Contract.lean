module

public import Zkc.Obligations.ClaimRelation
public import ZkcSecurity.Families.Proximity.Permutation

public section

/-! Proximity boundaries retain the request's gap. Mathematical permutation
links are separate from the executable positional read and its authentication
and cache laws in `Realizations.Oracle.Permutation`. -/

set_option autoImplicit false
namespace ZkcSecurity.Families.Proximity
open Zkc.Obligations

variable {Index Value : Type} [Fintype Index] [DecidableEq Value]

/-- Exact membership is Yes; distance at least the positive threshold is No.
Words between them remain in the gap and supply neither premise. -/
@[expose] def relation (code : Set (Index → Value)) (threshold : ℚ≥0)
    (positive : 0 < threshold) : ClaimRelation (Index → Value) Unit where
  Holds word _ := word ∈ code
  No := Far code threshold
  no_excludes word _ far member := far_excludes_member code threshold positive word far member

theorem relation_yes (code : Set (Index → Value)) (threshold : ℚ≥0)
    (positive : 0 < threshold) (word : Index → Value) :
    (relation code threshold positive).token.Yes word ↔ word ∈ code := by
  simp [relation, ClaimRelation.token]

/-- Sound transport preserves the specified distance, not only code membership. -/
theorem permutation_sound (permutation : Equiv.Perm Index) (code : Set (Index → Value))
    (threshold : ℚ≥0) (positive : 0 < threshold) :
    (relation code threshold positive).SoundLink
      (relation (permutedCode permutation code) threshold positive) (reindex permutation) :=
  fun word far => (far_reindex_iff permutation code threshold word).mpr far

theorem permutation_honest (permutation : Equiv.Perm Index) (code : Set (Index → Value))
    (threshold : ℚ≥0) (positive : 0 < threshold) :
    (relation code threshold positive).HonestLink
      (relation (permutedCode permutation code) threshold positive) (reindex permutation) := by
  intro word yes
  rw [relation_yes] at yes ⊢
  exact (mem_permutedCode_iff permutation code word).mpr yes

end ZkcSecurity.Families.Proximity
