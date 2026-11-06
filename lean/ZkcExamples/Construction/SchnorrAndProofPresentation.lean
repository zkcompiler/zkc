module

public import ZkcExamples.Construction.SchnorrAndArtifact
public import ZkcExamples.Structured.Generated.Scalar.SchnorrAnd

@[expose] public section

/-! Mathematical presentation of the exact admitted conjunction verifier.
The generated participant view owns protocol plumbing. The actual helper-body
association then connects lazy selected computation with Boolean conjunction.
The complete process, all inputs, all replies and every result remain fixed.
-/
set_option autoImplicit false
set_option smartUnfolding true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace ZkcExamples.Construction.SchnorrAndProof
open Zkc.Source Zkc.Source.Structured Zkc.Construction
attribute [local implicit_reducible] Op.results Op.arguments Op.regions

open ZkcExamples.Construction.SchnorrAndProofBodies in
private theorem verificationBody_equation {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G]
    {I : PIR.Signature} (observations : SiteObservations I) (tables : Evaluation.ComponentTables F G I)
    (firstBase firstKey secondBase secondKey firstCommitment secondCommitment : G)
    (challenge firstResponse secondResponse : F) :
    helper1Body.component
      (Evaluation.meaning (F := F) (G := G) observations tables.closed)
      (Evaluation.componentOperation observations tables)
      (show Values (Component (assignment F G)) helper1Helper.inputs from (.cons (some firstBase) (.cons (some firstResponse) (.cons (some firstCommitment) (.cons (some firstKey) (.cons (some challenge) (.cons (some secondBase) (.cons (some secondResponse) (.cons (some secondCommitment) (.cons (some secondKey) .nil)))))))))).get =
      .done (.cons (some (decide (firstResponse • firstBase = firstCommitment + challenge • firstKey) &&
        decide (secondResponse • secondBase = secondCommitment + challenge • secondKey))) .nil) := by
  conv_lhs => whnf
  erw [Evaluation.componentOperation_branch observations tables
    [.group "bls12-381.g1", .group "bls12-381.g1", .group "bls12-381.g1",
     .field "bls12-381.fr", .field "bls12-381.fr"] [.boolean]
    (decide (firstResponse • firstBase = firstCommitment + challenge • firstKey))
    (.cons secondBase (.cons secondKey (.cons secondCommitment (.cons challenge (.cons secondResponse .nil)))))]
  simp only [PIR.Process.bind_ite]
  split <;> simp_all only [Bool.true_and, Bool.false_and]
  all_goals rfl

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Full source process equality, including every optional reply. -/
theorem participant_equation (firstBase firstPoint secondBase secondPoint : G) (handle : Nat) :
    ZkcExamples.Structured.Generated.Scalar.SchnorrAnd.program.participant F G 1 (verifierInputs firstBase firstPoint secondBase secondPoint handle) =
      ((Zkc.Protocols.Schnorr.Variants.conjunction wiring firstBase firstPoint secondBase secondPoint handle).interpret CommonAdapter.embed).bind (fun value => .done (.cons value .nil)) := by
  rw [ZkcExamples.Structured.Generated.Scalar.SchnorrAnd.Root.verifier_participant]
  simp only [ZkcExamples.Structured.Generated.Scalar.SchnorrAnd.Root.verifierView,
    ZkcExamples.Structured.Generated.Scalar.SchnorrAnd.Root.verifierProcess,
    PIR.Process.bind, Values.get, verifierInputs]
  repeat' (apply PIR.Process.call_congr; intro)
  have association : BodyIn ZkcExamples.Structured.Generated.Scalar.SchnorrAnd.payload.definitions
      SchnorrAndProofBodies.helper1Helper SchnorrAndProofBodies.helper1Body := by
    refine ⟨helper1Definition, ?_, rfl, rfl⟩
    exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  erw [component_body_plain _ _ _ association]
  rw [verificationBody_equation]
  rfl

/-- Full source process equality, including every optional reply. -/
theorem process_equation (firstBase firstPoint secondBase secondPoint : G) (handle : Nat) :
    process (F := F) (G := G) firstBase firstPoint secondBase secondPoint handle = (Zkc.Protocols.Schnorr.Variants.conjunction wiring firstBase firstPoint secondBase secondPoint handle).interpret CommonAdapter.embed := by
  change ((ZkcExamples.Structured.Generated.Scalar.SchnorrAnd.program.participant F G 1
    (verifierInputs firstBase firstPoint secondBase secondPoint handle)).bind fun outputs =>
      .done (outputs.get .here)) = _
  rw [participant_equation (F := F) firstBase firstPoint secondBase secondPoint handle, PIR.Process.bind_assoc]
  simpa only [PIR.Process.bind, Values.get] using PIR.Process.bind_done _


theorem verifier_correspondence (firstBase firstPoint secondBase secondPoint : G) (handle : Nat) :
    verifier (F := F) (G := G) firstBase firstPoint secondBase secondPoint handle = Zkc.Protocols.Schnorr.Variants.conjunction wiring firstBase firstPoint secondBase secondPoint handle := by
  rw [verifier, process_equation, CommonAdapter.project_embed]


end ZkcExamples.Construction.SchnorrAndProof
