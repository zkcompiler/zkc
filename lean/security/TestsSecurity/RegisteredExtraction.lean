import ZkcSecurityExamples.Subjects.Schnorr.Registration
import ZkcSecurityExamples.Subjects.ChaumPedersen.Registration
import ZkcSecurityExamples.Subjects.Okamoto.Registration
import ZkcSecurityExamples.Subjects.SchnorrAnd.Registration
import ZkcSecurity.Claims.FiniteRecovery
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-! Controls for request-owned extraction semantics. These check the actual
registered profile, not a ban on classical reasoning inside proofs. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace TestsSecurity.RegisteredExtraction
open OracleComp OracleSpec ZkcSecurity.Endpoint ZkcSecurity.Claims
open ZkcSecurity.Examples.Subjects

instance : Fact (Nat.Prime 7) := ⟨by decide⟩
abbrev F := ZMod 7

abbrev scalar : Extraction.Layout := .scalar 2
abbrev pair : Extraction.Layout := .pair (.scalar 3) (.scalar 4)

example : scalar.recover (F := F) 1 6 3 3 = 2 := by decide +kernel
example : pair.recover (F := F) 1 (6, 4) 3 (3, 0) = (2, 5) := by decide +kernel

/-- A witness-search function that always finds the witness for the total
relation `w = publicValue` cannot pass response-difference correspondence. -/
theorem witnessSearch_not_responseDifference :
    ¬ ∀ first (response₁ : F) second response₂,
      (pure (1 : F) : ProbComp F) = pure (scalar.recover first response₁ second response₂) := by
  intro search
  have impossible := search 0 0 1 0
  simp [scalar, Extraction.Layout.recover_scalar] at impossible

/-- Admission rejects aliased components, missing private inputs, public inputs,
and a scalar field different from the challenge's declared domain. -/
example : (Extraction.Layout.pair (.scalar 3) (.scalar 3)).admitted Okamoto.Contract.retained
    "bls12-381.fr" = false := by decide +kernel
example : (Extraction.Layout.scalar 3).admitted Okamoto.Contract.retained
    "bls12-381.fr" = false := by decide +kernel
example : (Extraction.Layout.scalar 0).admitted Schnorr.Contract.retained
    "bls12-381.fr" = false := by decide +kernel
example : scalar.admitted Schnorr.Contract.retained "other.field" = false := by decide +kernel

/-- A failed fork uses the fixed full carrier, not a subtype of valid witnesses. -/
example : Extraction.recoverFork (M := Unit) (Commit := Unit)
    (fun c₁ (z₁ : F) c₂ z₂ => pure (scalar.recover c₁ z₁ c₂ z₂)) none =
      liftComp ($ᵗ F) (_root_.FiatShamir.Fork.wrappedSpec F) := rfl

/-- Every request resolved against this subject has the same response reader,
site, recovery layout, and witness embedding, irrespective of proof method. -/
example (request : KnowledgeRequest (Schnorr.Registration.subject (F := F) (G := F) .idealMeaning)) :
    request.profile = Schnorr.Registration.extractionProfile := request.profile_eq _ rfl rfl

/-- Evidence cannot make an unregistered profile available. -/
def unregistered : Subject F F Schnorr.artifacts .idealMeaning :=
  { Schnorr.Registration.subject .idealMeaning with extractors := ⟨[]⟩ }

example : ¬ Nonempty (KnowledgeRequest unregistered) := by
  rintro ⟨request⟩
  have impossible := request.registered
  contradiction

/-- Duplicate entries cannot silently select a second meaning. -/
def duplicate : Subject F F Schnorr.artifacts .idealMeaning :=
  let subject := Schnorr.Registration.subject (F := F) (G := F) .idealMeaning
  { subject with extractors := ⟨subject.extractors.exports ++ subject.extractors.exports⟩ }

example : ¬ Nonempty (KnowledgeRequest duplicate) := by
  rintro ⟨request⟩
  have impossible := request.registered
  contradiction

open Zkc.Claims

def wire (extractor : Wire.Expr) : Wire.Request :=
  let subject := Schnorr.Registration.subject (F := F) (G := F) .idealMeaning
  { subject := subject.reference
    property := ⟨"knowledge", 0⟩
    model := ⟨exactUniform, [
      (some "level", .reference "levels.ideal"), (some "statement", .reference "statements.fixed"),
      (some "oracle", .application "oracles.random" (some 0) [(none, .reference "construction.provider")]),
      (some "queries", .reference "Q"), (some "budget_symbol", .reference "Q")]⟩
    target := subject.targetReference
    accept := subject.acceptance
    quantity := .guarantee ⟨forking, [(some "extractor", extractor)]⟩ }

-- The closed guarantee schema refuses request-selected extraction methods.
set_option maxRecDepth 8192 in
example : knowledgeArguments (models .empty .idealMeaning)
    (wire (.application "extractors.witness_search" (some 0) []))
    (Schnorr.Registration.subject (F := F) (G := F) .idealMeaning) =
      .error (.schema "unknown argument: extractor") := rfl

set_option maxRecDepth 8192 in
example : knowledgeArguments (models .empty .idealMeaning)
    (wire (.application "extractors.response_difference" (some 1) []))
    (Schnorr.Registration.subject (F := F) (G := F) .idealMeaning) =
      .error (.schema "unknown argument: extractor") := rfl

example : ("wrong.challenge", "label_64656c6976657279_0") ∉ Schnorr.compiled.context.draws := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Straight-line recovery cannot be read as the existing forking guarantee. -/
example : knowledgeArguments (models .empty .idealMeaning)
    { wire (.natural 0) with quantity := .guarantee ⟨FiniteRecovery.identifier, []⟩ }
    (Schnorr.Registration.subject (F := F) (G := F) .idealMeaning) =
      .error (.unknownIdentifier FiniteRecovery.identifier) := rfl

example : FiniteRecovery.evaluate FiniteRecovery.registry responseDifference
    (⟨3⟩ : ZkcSecurity.Commitment.FiniteRecovery.Request Nat) 2 =
      .error (.unknownIdentifier responseDifference) := rfl

/-- A caller cannot alias the closed finite token to the forking extractor's
name, even by explicitly assembling a registry under that key. -/
example : FiniteRecovery.evaluate
    ⟨[{ FiniteRecovery.profileEntry with identifier := responseDifference }]⟩ responseDifference
    (⟨3⟩ : ZkcSecurity.Commitment.FiniteRecovery.Request Nat) 2 =
      .error (.schema "finite recovery profile identifier mismatch") := rfl

#check_failure (show ExtractionProfile Schnorr.compiled F F from
  FiniteRecovery.Profile.orderedTwoCellSum)

end TestsSecurity.RegisteredExtraction
