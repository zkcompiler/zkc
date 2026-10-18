module

public import ZkcExamples.Structured.OkamotoNormalForms
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Tactic.Abel

@[expose] public section

/-! Okamoto's proof of knowledge of a representation, over the actual
original-stage `okamoto::Interactive` Entry.

The participant processes, their runs, the `knowledge` clause's binding and the
verifier's observed decision are the generated declarations of
`OkamotoNormalForms`. This module states the protocol's mathematics over them:
two accepting runs with one commitment and distinct challenges give a
representation of the point at both bases, and the actual verifier accepts what
the actual prover sends whenever the prover's witnesses represent the point. -/
namespace ZkcExamples.Structured.Okamoto
open Zkc.Source Zkc.Source.Structured OkamotoViews

set_option smartUnfolding false

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

omit [DecidableEq F] [DecidableEq G] in
/-- Two verifier equations at one commitment and distinct challenges determine
a representation of the point: each response difference divided by the
challenge difference. -/
theorem extract_representation (firstBase secondBase point commitment : G)
    (challenge₁ challenge₂ firstResponse₁ secondResponse₁ firstResponse₂ secondResponse₂ : F)
    (distinct : challenge₁ ≠ challenge₂)
    (accept₁ : firstResponse₁ • firstBase + secondResponse₁ • secondBase =
      commitment + challenge₁ • point)
    (accept₂ : firstResponse₂ • firstBase + secondResponse₂ • secondBase =
      commitment + challenge₂ • point) :
    point = ((firstResponse₁ - firstResponse₂) / (challenge₁ - challenge₂)) • firstBase +
      ((secondResponse₁ - secondResponse₂) / (challenge₁ - challenge₂)) • secondBase := by
  have difference : (firstResponse₁ - firstResponse₂) • firstBase +
      (secondResponse₁ - secondResponse₂) • secondBase = (challenge₁ - challenge₂) • point := by
    calc (firstResponse₁ - firstResponse₂) • firstBase +
          (secondResponse₁ - secondResponse₂) • secondBase
        = (firstResponse₁ • firstBase + secondResponse₁ • secondBase) -
            (firstResponse₂ • firstBase + secondResponse₂ • secondBase) := by
          rw [sub_smul, sub_smul]
          abel
      _ = (challenge₁ - challenge₂) • point := by
          rw [accept₁, accept₂, sub_smul]
          abel
  rw [div_eq_inv_mul, div_eq_inv_mul, ← smul_smul, ← smul_smul, ← smul_add, difference,
    smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr distinct), one_smul]

/-- Two runs of the actual verifier with one commitment and distinct challenges,
both accepted, give a witness pair for which the `knowledge` target holds at the
first run's observed boundary: each response difference divided by the
challenge difference. -/
theorem extracted_target (firstBase secondBase point : G) (challenges : Nat) (commitment : G)
    (challenge₁ challenge₂ firstResponse₁ secondResponse₁ firstResponse₂ secondResponse₂ : F)
    (distinct : challenge₁ ≠ challenge₂)
    (accept₁ : OkamotoNormalForms.decisionSelector.read {}
      (OkamotoNormalForms.observedBoundary firstBase secondBase point challenges commitment
        challenge₁ firstResponse₁ secondResponse₁) = some true)
    (accept₂ : OkamotoNormalForms.decisionSelector.read {}
      (OkamotoNormalForms.observedBoundary firstBase secondBase point challenges commitment
        challenge₂ firstResponse₂ secondResponse₂) = some true) :
    (OkamotoNormalForms.target (F := F) (G := G)).Holds {}
      (OkamotoNormalForms.observedBoundary firstBase secondBase point challenges commitment
        challenge₁ firstResponse₁ secondResponse₁)
      (OkamotoNormalForms.assignments firstBase secondBase
        ((firstResponse₁ - firstResponse₂) / (challenge₁ - challenge₂))
        ((secondResponse₁ - secondResponse₂) / (challenge₁ - challenge₂))) := by
  rw [OkamotoNormalForms.observed_accepts_iff] at accept₁ accept₂
  apply (OkamotoNormalForms.observed_target_iff ..).mpr
  apply (OkamotoNormalForms.relation_iff ..).mpr
  exact extract_representation firstBase secondBase point commitment challenge₁ challenge₂
    firstResponse₁ secondResponse₁ firstResponse₂ secondResponse₂ distinct accept₁ accept₂

/-- The commitment and responses the admitted prover computes for two nonces
and a challenge are accepted by the actual verifier with that challenge when
the witnesses represent the point at the verifier's bases. -/
theorem honest_values_accepted (firstBase secondBase point : G) (firstScalar secondScalar : F)
    (challenges : Nat) (firstNonce secondNonce challenge : F)
    (valid : OkamotoNormalForms.Relation firstBase secondBase point firstScalar secondScalar) :
    OkamotoNormalForms.decisionSelector.read {}
      (OkamotoNormalForms.observedBoundary firstBase secondBase point challenges
        ((firstNonce • firstBase) + (secondNonce • secondBase)) challenge
        (firstNonce + (challenge * firstScalar)) (secondNonce + (challenge * secondScalar))) =
      some true := by
  apply (OkamotoNormalForms.observed_accepts_iff ..).mpr
  have representation := (OkamotoNormalForms.relation_iff ..).mp valid
  subst representation
  simp only [add_smul, smul_add, smul_smul]
  abel

/-- Honest acceptance over the actual prover's run: for every pair of nonces it
draws and every challenge it receives, the prover returns, and the actual
verifier, drawing that challenge, accepts the commitment and the two responses
the prover sends, whenever the prover's witnesses represent the point. -/
theorem honest_accepts (firstBase secondBase point : G) (firstScalar secondScalar : F)
    (nonces challenges : Nat) (firstNonce secondNonce challenge : F)
    (valid : OkamotoNormalForms.Relation firstBase secondBase point firstScalar secondScalar) :
    ∃ (commitment : G) (firstResponse secondResponse : F),
      (OkamotoNormalForms.proverReplies firstNonce secondNonce challenge).run
          (program.participant F G 0 (OkamotoNormalForms.proverInputs firstBase secondBase point
            firstScalar secondScalar nonces)) =
        ⟨.returned (.cons none .nil), (),
          [.query OkamotoNormalForms.firstNonceSite scalarDomain (.cons nonces .nil),
           .query OkamotoNormalForms.secondNonceSite scalarDomain (.cons nonces .nil),
           .send (ty := .group groupDomain) OkamotoNormalForms.commitmentSite 1 commitment,
           .receive (.field scalarDomain) OkamotoNormalForms.deliverySite 1,
           .send (ty := .field scalarDomain) OkamotoNormalForms.firstResponseSite 1 firstResponse,
           .send (ty := .field scalarDomain) OkamotoNormalForms.secondResponseSite 1
             secondResponse]⟩ ∧
      OkamotoNormalForms.decisionSelector.read {}
        (OkamotoNormalForms.observedBoundary firstBase secondBase point challenges commitment
          challenge firstResponse secondResponse) = some true :=
  ⟨_, _, _,
    OkamotoNormalForms.prover_run firstBase secondBase point firstScalar secondScalar nonces
      firstNonce secondNonce challenge,
    honest_values_accepted firstBase secondBase point firstScalar secondScalar challenges
      firstNonce secondNonce challenge valid⟩

end ZkcExamples.Structured.Okamoto
