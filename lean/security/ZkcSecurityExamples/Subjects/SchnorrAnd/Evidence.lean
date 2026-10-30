module

public import ZkcSecurityExamples.Subjects.SchnorrAnd.Artifacts
public import ZkcSecurityExamples.Subjects.SchnorrAnd.Contract
public import ZkcSecurity.Bindings.Sigma.SchnorrVariants

@[expose] public section

/-! Knowledge evidence of the subject `schnorr-and`.

The family package of two Schnorr proofs under one challenge, at the checked
context and the example's wiring, for the bases and the points of a policy
statement (`parts`). The model equation is the generated
`SchnorrAndProof.verifier_correspondence`: the admitted original validator is
the common conjunction verifier, by computation. The contract's witness
relation is the family's relation (`relation`), by the formula's process. -/

namespace ZkcSecurity.Examples.Subjects.SchnorrAnd
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcSecurity.Endpoint
open ZkcExamples.Construction

set_option smartUnfolding false

/-- The bases and the points of a policy statement. -/
def parts {F G : Type} : artifacts.Statement F G → G × G × G × G
  | .cons firstBase (.cons firstPoint (.cons secondBase (.cons secondPoint .nil))) =>
      (firstBase, firstPoint, secondBase, secondPoint)

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
  [SampleableType F] [SampleableType G]

/-- The conjunction family at the checked context and the example's wiring. -/
def family :
    SigmaFamily (F := F) (G := G) compiled.context (artifacts.Statement F G) (G × G) (F × F) (G × G) (F × F) (F × F) :=
  ZkcSecurity.Families.SchnorrVariants.conjunctionFamily compiled.context SchnorrAndProof.wiring 0 parts

omit [SampleableType F] [SampleableType G] in
theorem original_eq (firstBase firstPoint secondBase secondPoint : G) :
    compiled.original (F := F) (.cons firstBase (.cons firstPoint (.cons secondBase (.cons secondPoint .nil)))) 0 =
      SchnorrAndProof.verifier firstBase firstPoint secondBase secondPoint 0 :=
  rfl

theorem model (statement : artifacts.Statement F G) :
    compiled.original statement 0 = family.validator statement := by
  match statement with
  | .cons firstBase (.cons firstPoint (.cons secondBase (.cons secondPoint .nil))) =>
      rw [original_eq]
      exact SchnorrAndProof.verifier_correspondence firstBase firstPoint secondBase secondPoint 0

theorem relation (statement : artifacts.Statement F G) (witnesses : F × F) :
    Contract.holds statement witnesses ↔ family.rel statement (family.key statement) witnesses = true := by
  match statement with
  | .cons firstBase (.cons firstPoint (.cons secondBase (.cons secondPoint .nil))) =>
      rw [Contract.holds_iff]
      simp only [family, ZkcSecurity.Families.SchnorrVariants.conjunctionFamily, parts,
        ZkcSecurity.VCVio.SigmaAnd.andRelation, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨fun ⟨first, second⟩ => ⟨first.symm, second.symm⟩, fun ⟨first, second⟩ => ⟨first.symm, second.symm⟩⟩

/-- Knowledge evidence of the compiled Schnorr AND proof Entry at a covered
endpoint. -/
def knowledge (endpoint : Semantics) (lowering : LoweringRequirement artifacts compiled F G endpoint) :
    KnowledgeEvidence (F := F) (G := G) artifacts endpoint (G × G) (F × F) (G × G) (F × F) (F × F)
      Contract.holds where
  compiled := compiled
  connection := sourceConnection
  target := Contract.retained
  formula := ZkcSecurity.Examples.Subjects.SchnorrAnd.Contract.formulaBinding
  witness := Contract.embed
  relationPinned := Contract.holds_pinned
  handle := 0
  family := family
  model := model
  relation := relation
  lowering := lowering
  hypotheses := []

end ZkcSecurity.Examples.Subjects.SchnorrAnd
