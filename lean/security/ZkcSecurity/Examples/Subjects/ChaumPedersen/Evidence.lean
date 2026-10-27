module

public import ZkcSecurity.Examples.Subjects.ChaumPedersen.Artifacts
public import ZkcSecurity.Examples.Subjects.ChaumPedersen.Contract
public import ZkcSecurity.Families.SchnorrVariants

@[expose] public section

/-! Knowledge evidence of the subject `chaum-pedersen`.

The Chaum–Pedersen family package at the checked context and the example's
wiring, for the bases and the points of a policy statement (`parts`). The model
equation is the generated `ChaumPedersenProof.verifier_correspondence`: the
admitted original validator is the common Chaum–Pedersen verifier, by
computation. The contract's witness relation is the family's relation
(`relation`), by the formula's process. -/

namespace ZkcSecurity.Examples.Subjects.ChaumPedersen
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcSecurity.Endpoint
open ZkcExamples.Construction

set_option smartUnfolding false

/-- The bases and the points of a policy statement. -/
def parts {F G : Type} : artifacts.Statement F G → G × G × G × G
  | .cons firstBase (.cons firstPoint (.cons secondBase (.cons secondPoint .nil))) =>
      (firstBase, firstPoint, secondBase, secondPoint)

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
  [SampleableType F] [SampleableType G]

/-- The Chaum–Pedersen family at the checked context and the example's wiring. -/
def family : SigmaFamily (F := F) (G := G) compiled.context (artifacts.Statement F G) (G × G) F (G × G) F F :=
  ZkcSecurity.Families.SchnorrVariants.equalityFamily compiled.context ChaumPedersenProof.wiring 0 parts

omit [SampleableType F] [SampleableType G] in
theorem original_eq (firstBase firstPoint secondBase secondPoint : G) :
    compiled.original (F := F) (.cons firstBase (.cons firstPoint (.cons secondBase (.cons secondPoint .nil)))) 0 =
      ChaumPedersenProof.verifier firstBase firstPoint secondBase secondPoint 0 :=
  rfl

theorem model (statement : artifacts.Statement F G) :
    compiled.original statement 0 = family.validator statement := by
  match statement with
  | .cons firstBase (.cons firstPoint (.cons secondBase (.cons secondPoint .nil))) =>
      rw [original_eq]
      exact ChaumPedersenProof.verifier_correspondence firstBase firstPoint secondBase secondPoint 0

theorem relation (statement : artifacts.Statement F G) (witness : F) :
    Contract.holds statement witness ↔ family.rel statement (family.key statement) witness = true := by
  match statement with
  | .cons firstBase (.cons firstPoint (.cons secondBase (.cons secondPoint .nil))) =>
      rw [Contract.holds_iff]
      simp only [family, ZkcSecurity.Families.SchnorrVariants.equalityFamily, parts, Prod.smul_mk,
        decide_eq_true_eq, Prod.mk.injEq]
      exact ⟨fun ⟨first, second⟩ => ⟨first.symm, second.symm⟩, fun ⟨first, second⟩ => ⟨first.symm, second.symm⟩⟩

/-- Knowledge evidence of the compiled Chaum–Pedersen proof Entry at a covered
endpoint. -/
def knowledge (endpoint : Semantics) (lowering : LoweringRequirement artifacts compiled F G endpoint) :
    KnowledgeEvidence (F := F) (G := G) artifacts endpoint (G × G) F (G × G) F F Contract.holds where
  compiled := compiled
  connection := sourceConnection
  target := Contract.retained
  formula := ZkcSecurity.Examples.Subjects.ChaumPedersen.Contract.formulaBinding
  witness := Contract.embed
  relationPinned := Contract.holds_pinned
  handle := 0
  family := family
  model := model
  relation := relation
  lowering := lowering
  hypotheses := []

end ZkcSecurity.Examples.Subjects.ChaumPedersen
