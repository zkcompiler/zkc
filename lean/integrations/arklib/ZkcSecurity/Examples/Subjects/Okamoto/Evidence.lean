module

public import ZkcSecurity.Examples.Subjects.Okamoto.Artifacts
public import ZkcSecurity.Examples.Subjects.Okamoto.Contract
public import ZkcSecurity.Families.SchnorrVariants

@[expose] public section

/-! Knowledge evidence of the subject `okamoto-proof`.

The Okamoto family package at the checked context and the example's wiring, for
the bases and the point of a policy statement (`parts`). The model equation is
the generated `OkamotoProof.verifier_correspondence`: the admitted original
validator is the common representation verifier, by computation. The
contract's witness relation is the family's relation (`relation`), by the
formula's process. -/

namespace ZkcSecurity.Examples.Subjects.Okamoto
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcSecurity.Endpoint
open ZkcExamples.Construction

set_option smartUnfolding false

/-- The bases and the point of a policy statement. -/
def parts {F G : Type} : artifacts.Statement F G → G × G × G
  | .cons firstBase (.cons secondBase (.cons point .nil)) => (firstBase, secondBase, point)

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
  [SampleableType F] [SampleableType G]

/-- The Okamoto family at the checked context and the example's wiring. -/
def family : SigmaFamily (F := F) (G := G) compiled.context (artifacts.Statement F G) G (F × F) G (F × F) (F × F) :=
  ZkcSecurity.Families.SchnorrVariants.representationFamily compiled.context OkamotoProof.wiring 0 parts

omit [SampleableType F] [SampleableType G] in
theorem original_eq (firstBase secondBase point : G) :
    compiled.original (F := F) (.cons firstBase (.cons secondBase (.cons point .nil))) 0 =
      OkamotoProof.verifier firstBase secondBase point 0 :=
  rfl

theorem model (statement : artifacts.Statement F G) :
    compiled.original statement 0 = family.validator statement := by
  match statement with
  | .cons firstBase (.cons secondBase (.cons point .nil)) =>
      rw [original_eq]
      exact OkamotoProof.verifier_correspondence firstBase secondBase point 0

theorem relation (statement : artifacts.Statement F G) (witnesses : F × F) :
    Contract.holds statement witnesses ↔ family.rel statement (family.key statement) witnesses = true := by
  match statement with
  | .cons firstBase (.cons secondBase (.cons point .nil)) =>
      rw [Contract.holds_iff]
      simp only [family, ZkcSecurity.Families.SchnorrVariants.representationFamily, parts, decide_eq_true_eq]
      exact eq_comm

/-- Knowledge evidence of the compiled Okamoto proof Entry at a covered
endpoint. -/
def knowledge (endpoint : Semantics) (lowering : LoweringRequirement artifacts compiled F G endpoint) :
    KnowledgeEvidence (F := F) (G := G) artifacts endpoint G (F × F) G (F × F) (F × F) Contract.holds where
  compiled := compiled
  handle := 0
  family := family
  model := model
  relation := relation
  lowering := lowering
  hypotheses := []

end ZkcSecurity.Examples.Subjects.Okamoto
