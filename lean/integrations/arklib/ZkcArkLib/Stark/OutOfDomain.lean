module

public import ZkcSecurity.Families.Stark.OutOfDomain
public import ArkLib.ProofSystem.Stir.OutOfDomSmpl

@[expose] public section

/-! Exact adapters to ArkLib STIR Lemma 4.5 at the manifest-pinned revision.
The samples are independent uniform draws from the typed domain complement.
List decodability is a hypothesis, not a parameter certification. -/

namespace ZkcArkLib.Stark
open ZkcSecurity.Families.Stark
open scoped NNReal ENNReal ProbabilityTheory

variable {F Index : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype Index] [DecidableEq Index]

omit [Field F] [DecidableEq Index] in
theorem domainComplement_eq (domain : Index ↪ F) :
    OutOfDomSmpl.domainComplement domain = outsidePoints domain := rfl

/-- The sharper unordered-pair bound, for the actual upstream collision event.
Both the list radius and the list size are supplied by the selected code. -/
theorem list_collision_le (domain : Index ↪ F) (word : Index → F)
    (degree samples : ℕ) (radius listSize : ℝ≥0)
    (decodable : Code.IsListDecodable
      (ReedSolomon.code domain degree : Set (Index → F)) radius listSize)
    (nonempty : Nonempty ↥(outsidePoints domain)) :
    OutOfDomSmpl.listDecodingCollisionProbability domain word radius samples degree nonempty ≤
      (listSize * (listSize - 1) / 2) *
        (((degree : ℝ≥0∞) - 1) /
          ((Fintype.card F : ℝ≥0∞) - Fintype.card Index)) ^ samples :=
  OutOfDomSmpl.out_of_dom_smpl_1 _ rfl decodable nonempty

end ZkcArkLib.Stark
