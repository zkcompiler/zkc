module

public import ZkcSecurity.Families.Stark.DeepBatching
public import ArkLib.ProofSystem.Stir.Quotienting

@[expose] public section

/-! Representation equalities and the proved STIR quotienting separation law.
The OOD specialization has no in-domain fill loss. Degree and rate premises
remain explicit: `|S| < degree ≤ |Index|`. -/

namespace ZkcArkLib.Stark
open ZkcSecurity.Families.Stark
open scoped NNReal

variable {F Index : Type} [Field F] [DecidableEq F]

omit [DecidableEq F] in
theorem vanishing_eq (points : Finset F) :
    vanishing points = Quotienting.vanishingPoly points := rfl

theorem interpolate_eq (points : Finset F) (answers : points → F) :
    interpolate points answers = Quotienting.ansPoly points answers := rfl

theorem deepQuotient_eq (points : Finset F) (p : Polynomial F) :
    deepQuotient points p = Quotienting.polyQuotient points p :=
  Polynomial.divByMonic_eq_div _ (vanishing_monic points)

/-- If every nearby codeword disagrees with at least one claimed OOD answer,
the quotient word lies beyond the same radius of the reduced-degree code. -/
theorem quotient_distance_gt [Fintype Index] [Nonempty Index] [DecidableEq Index]
    (domain : Index ↪ F) (points : Finset F) (word : Index → F) (answers : points → F)
    {degree : ℕ} (size : points.card < degree) (rate : degree ≤ Fintype.card Index)
    (outside : ∀ i, domain i ∉ points) (radius : ℝ≥0)
    (disagrees : ∀ u : ReedSolomon.code domain degree,
      u.val ∈ Code.closeCodewordsRel (ReedSolomon.code domain degree) word radius →
        ∃ x : points, (ReedSolomon.toPolynomialLT u : Polynomial F).eval (x : F) ≠ answers x) :
    Code.relDistFromCode
      (fun i => (word i - (interpolate points answers).eval (domain i)) /
        (vanishing points).eval (domain i))
      (ReedSolomon.code domain (degree - points.card)) > radius := by
  have law := Quotienting.quotienting points size rate word answers (fun _ => 0) radius disagrees
  have empty : Quotienting.disagreementSet domain word points answers = ∅ := by
    ext i
    simp [Quotienting.disagreementSet, outside i]
  simp only [empty, Finset.card_empty, Nat.cast_zero, ENNReal.zero_div, add_zero] at law
  have same : Quotienting.funcQuotient domain word points answers (fun _ => 0) =
      fun i => (word i - (interpolate points answers).eval (domain i)) /
        (vanishing points).eval (domain i) := by
    funext i
    rw [Quotienting.funcQuotient_of_not_mem (outside i)]
    rfl
  rw [same] at law
  exact law

end ZkcArkLib.Stark
