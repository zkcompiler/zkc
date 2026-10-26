module

public import ZkcArkLib.Examples.Subjects.Guess.Artifacts
public import ZkcArkLib.Examples.Subjects.Guess.Contract

@[expose] public section

/-! Ordinary soundness evidence of the subject `guess`.

The family is the imported ArkLib certificate of `CompiledGuessFiatShamir`,
each challenge charged `1 / |F|`. A statement denotes its offset, every offset is
false in the model, and the generated model equation (`GuessProof.verifier`, the
original validator by computation) makes the original validator the family's. -/

namespace ZkcSecurity.Examples.Subjects.Guess
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcSecurity.Endpoint ZkcSecurity.FiatShamir
open ZkcExamples.Construction
open scoped ENNReal NNReal

set_option smartUnfolding false

/-- A statement denotes its offset; every offset is false. -/
abbrev relation {F G : Type} : ModelRelation F G artifacts.publics where
  Model := F
  models statement value := Contract.offset statement = value
  functional _ _ _ first second := first.symm.trans second
  falseModel _ := True

variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

open ZkcSecurity.Examples.CompiledGuessFiatShamir in
/-- The imported ArkLib certificate, each challenge charged `1 / |F|`. -/
noncomputable def family :
    CertificateFamily (G := G) compiled.context (Regime.exact F) (relation (F := F) (G := G)) where
  validator offset := GuessProof.verifier offset 0
  charge _ event := participantError event
  certificate := (certificate (F := F) (G := G)).charged
  doomed offset _ _ := verifier_doomed offset 0

/-- The charge of one challenge. -/
noncomputable def error : ENNReal := ((Fintype.card F : ℝ≥0)⁻¹ : ℝ≥0)

omit [Fintype F] [SampleableType F] in
theorem original_eq (offset : F) :
    compiled.original (G := G) (.cons offset .nil) 0 = GuessProof.verifier offset 0 :=
  rfl

theorem costBound (statement : artifacts.Statement F G) (initial : History F G) :
    Typed.ChargedCostBound (interface (G := G) compiled.context (Regime.exact F).decode)
      (family (F := F) (G := G)).charge (compiled.original statement 0) initial (error (F := F)) := by
  match statement with
  | .cons offset .nil =>
      rw [original_eq]
      have bounded := Typed.QueryBound.chargedCostBound (interface (G := G) compiled.context (Regime.exact F).decode)
        (charge := (family (F := F) (G := G)).charge) (bound := error (F := F)) (fun _ _ => le_rfl) _ 1
        (QueryBound.typed _ _ _ 1 (ZkcSecurity.Examples.CompiledGuessFiatShamir.verifier_queryBound offset 0))
        initial
      rwa [Nat.cast_one, one_mul] at bounded

/-- Ordinary soundness evidence of the guessing Entry at a covered endpoint and a
statement form. -/
noncomputable def soundness (endpoint : Semantics) (form : Form) (binding : BindingRequirement form)
    (lowering : LoweringRequirement artifacts compiled F G endpoint) :
    SoundnessEvidence (F := F) (G := G) artifacts endpoint form Contract.falseStatement (Regime.exact F) where
  compiled := compiled
  connection := sourceConnection
  target := .importedLanguage Contract.importedLanguage
  claimPinned := Contract.falseStatement_pinned
  handle := 0
  relation := relation
  family := family
  model statement offset denotes := by
    match statement, denotes with
    | .cons _ .nil, rfl => rfl
  covers statement _ := .inl ⟨Contract.offset statement, rfl, trivial⟩
  unmapped statement unmapped := absurd rfl (unmapped (Contract.offset statement))
  cost _ := error
  costBound := costBound
  binding := binding
  lowering := lowering
  hypotheses := []

end ZkcSecurity.Examples.Subjects.Guess
