module

public import ZkcSecurity.Examples.Subjects.Schnorr.Artifacts
public import ZkcSecurity.Examples.Subjects.Schnorr.Contract
public import ZkcSecurity.Families.Schnorr

@[expose] public section

/-! Knowledge evidence of the subject `schnorr`.

The Schnorr family package at the checked context and the example's wiring,
for the base and the key of a policy statement (`parts`). The model equation is
the generated `SchnorrProof.verifier_correspondence`: the admitted original
validator is the common Schnorr verifier, by computation. The contract's witness
relation is the family's relation (`relation`), by the formula's process. -/

namespace ZkcSecurity.Examples.Subjects.Schnorr
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcSecurity.Endpoint
open ZkcExamples.Construction

set_option smartUnfolding false

/-- The base and the key of a policy statement. -/
def parts {F G : Type} : artifacts.Statement F G → G × G
  | .cons base (.cons key .nil) => (base, key)

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
  [SampleableType F] [SampleableType G]

/-- The Schnorr family at the checked context and the example's wiring. -/
def family : SigmaFamily (F := F) (G := G) compiled.context (artifacts.Statement F G) G F G F F :=
  ZkcSecurity.Families.Schnorr.family compiled.context SchnorrProof.wiring 0 parts

omit [SampleableType F] [SampleableType G] in
theorem original_eq (base key : G) :
    compiled.original (F := F) (.cons base (.cons key .nil)) 0 = SchnorrProof.verifier base key 0 :=
  rfl

theorem model (statement : artifacts.Statement F G) :
    compiled.original statement 0 = family.validator statement := by
  match statement with
  | .cons base (.cons key .nil) =>
      rw [original_eq]
      exact SchnorrProof.verifier_correspondence base key 0

theorem relation (statement : artifacts.Statement F G) (witness : F) :
    Contract.holds statement witness ↔ family.rel statement (family.key statement) witness = true := by
  match statement with
  | .cons base (.cons key .nil) => exact SchnorrProofBinding.relation_eq base key witness

/-- Knowledge evidence of the compiled Schnorr proof Entry at a covered endpoint. -/
def knowledge (endpoint : Semantics) (lowering : LoweringRequirement artifacts compiled F G endpoint) :
    KnowledgeEvidence (F := F) (G := G) artifacts endpoint G F G F F Contract.holds where
  compiled := compiled
  target := Contract.retained
  witness := Contract.embed
  relationPinned := Contract.holds_pinned
  handle := 0
  family := family
  model := model
  relation := relation
  lowering := lowering
  hypotheses := []

end ZkcSecurity.Examples.Subjects.Schnorr
