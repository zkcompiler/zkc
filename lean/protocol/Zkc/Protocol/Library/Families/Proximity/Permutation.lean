module

public import Mathlib.InformationTheory.Hamming
public import Mathlib.Data.NNRat.Lemmas

@[expose] public section

/-! Coordinate permutations of arbitrary finite codes. The normalization is the
same count/cardinality in `Code.relHammingDist` used by the optional ArkLib FRI
integration. No ArkLib protocol or proximity theorem is imported here.

The coordinate-count proof follows ArkLib's
`ArkLib/ToMathlib/InformationTheory/Hamming.lean`, `hammingDist_comp_equiv`
(Apache-2.0, Alexander Hicks). It is kept here to avoid making the security
package depend on the optional integration package. -/

set_option autoImplicit false
namespace ZkcSecurity.Families.Proximity

variable {Index Value : Type} [Fintype Index] [DecidableEq Value]

/-- Reindex both the input word and every codeword in the same direction. -/
def reindex (permutation : Equiv.Perm Index) (word : Index → Value) : Index → Value :=
  word ∘ permutation

def permutedCode (permutation : Equiv.Perm Index) (code : Set (Index → Value)) :
    Set (Index → Value) := reindex permutation '' code

/-- Normalized Hamming distance, with the same rational normalization as ArkLib.
Clients selecting a nonempty positional domain exclude the empty-domain case. -/
def relativeDistance (left right : Index → Value) : ℚ≥0 :=
  hammingDist left right / Fintype.card Index

/-- Farness is a gap predicate, with the threshold fixed by the caller. -/
def Far (code : Set (Index → Value)) (threshold : ℚ≥0) (word : Index → Value) : Prop :=
  ∀ codeword ∈ code, threshold ≤ relativeDistance word codeword

omit [Fintype Index] [DecidableEq Value] in
theorem reindex_injective (permutation : Equiv.Perm Index) :
    Function.Injective (reindex (Value := Value) permutation) := by
  intro left right equal
  funext index
  simpa only [reindex, Function.comp_apply, Equiv.apply_symm_apply] using
    congrFun equal (permutation.symm index)

theorem hammingDistance_reindex (permutation : Equiv.Perm Index) (left right : Index → Value) :
    hammingDist (reindex permutation left) (reindex permutation right) = hammingDist left right := by
  unfold hammingDist reindex
  apply Finset.card_nbij' (fun i => permutation i) (fun i => permutation.symm i)
  · intro i member; simpa using member
  · intro i member; simpa using member
  · intro i _; simp
  · intro i _; simp

theorem relativeDistance_reindex (permutation : Equiv.Perm Index) (left right : Index → Value) :
    relativeDistance (reindex permutation left) (reindex permutation right) =
      relativeDistance left right := by
  simp only [relativeDistance, hammingDistance_reindex]

omit [Fintype Index] [DecidableEq Value] in
theorem mem_permutedCode_iff (permutation : Equiv.Perm Index) (code : Set (Index → Value))
    (word : Index → Value) :
    reindex permutation word ∈ permutedCode permutation code ↔ word ∈ code := by
  constructor
  · rintro ⟨original, member, equal⟩
    exact reindex_injective permutation equal ▸ member
  · exact fun member => ⟨word, member, rfl⟩

theorem far_reindex_iff (permutation : Equiv.Perm Index) (code : Set (Index → Value))
    (threshold : ℚ≥0) (word : Index → Value) :
    Far (permutedCode permutation code) threshold (reindex permutation word) ↔
      Far code threshold word := by
  constructor
  · intro far codeword member
    simpa only [relativeDistance_reindex] using far _ ⟨codeword, member, rfl⟩
  · rintro far _ ⟨codeword, member, rfl⟩
    simpa only [relativeDistance_reindex] using far codeword member

/-- Positive thresholds make farness disjoint from exact validity; invalidity
alone does not imply farness. -/
theorem far_excludes_member (code : Set (Index → Value)) (threshold : ℚ≥0)
    (positive : 0 < threshold) (word : Index → Value) (far : Far code threshold word) :
    word ∉ code := by
  intro member
  have bound := far word member
  simp only [relativeDistance, hammingDist_self, Nat.cast_zero, zero_div] at bound
  exact (not_le_of_gt positive) bound

end ZkcSecurity.Families.Proximity
