import ZkcSecurity.Examples.Subjects.Schnorr.Claims
import ZkcSecurity.Examples.Subjects.Guess.Claims
import ZkcSecurity.Examples.CompiledSchnorrFiatShamir
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-! Controls for the endpoints and the subjects' evidence.

- **Schnorr.** The subject's evidence runs the compiled verifier of
  `CompiledSchnorrFiatShamir` (`schnorr_verify_eq`), so the registered claim is
  about that compiled verifier.
- **Guessing Entry.** The subject's evidence at the fixed form gives back
  `CompiledGuessFiatShamir.soundness` for that theorem's verifier
  (`guess_verify_eq`, `guess_fixed_soundness`), a bound attained at zero queries
  (`CompiledGuessFiatShamir.guess_accepted`). Statement determination of the
  adaptive claim's binding is a named hypothesis of the binding category,
  discharged by the codec's proof (`determination_discharged`).
- **Requirements.** Lowering evidence is required exactly for program bytes and
  binding evidence exactly for adaptive statements, by the evidence's indices.
- **Artifacts.** The composed check refuses the Schnorr original with the
  guessing export (`mismatched_artifacts`), so no `Compiled` value exists for that
  pair.
-/

namespace TestsSecurity.Endpoints
open OracleComp OracleSpec
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Endpoint ZkcSecurity.FiatShamir
open ZkcExamples.Construction
open scoped ENNReal NNReal

set_option smartUnfolding false

section Schnorr
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
  [SampleableType F] [SampleableType G]

/-- The subject's evidence runs the compiled verifier of `CompiledSchnorrFiatShamir`. -/
theorem schnorr_verify_eq (application : String) (base key : G) (proof : G × F) :
    (ZkcSecurity.Examples.Subjects.Schnorr.knowledge .idealMeaning PUnit.unit).verify
        (.cons base (.cons key .nil))
        (ZkcSecurity.Examples.CompiledSchnorrFiatShamir.initial application base key) proof =
      ZkcSecurity.Examples.CompiledSchnorrFiatShamir.verify application base key proof := by
  unfold KnowledgeEvidence.verify ZkcSecurity.Examples.CompiledSchnorrFiatShamir.verify Compiled.verifier
  rw [Functor.map_map]
  rfl

end Schnorr

section Guess
variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]
open ZkcSecurity.Examples.Subjects.Guess

omit [Fintype F] [SampleableType F] in
/-- The subject's evidence runs the compiled verifier of `CompiledGuessFiatShamir`. -/
theorem guess_verify_eq [Fintype F] [SampleableType F] (offset : F) (initial : History F G) (proof : Proof F G) :
    (soundness (F := F) (G := G) .idealMeaning .fixed PUnit.unit PUnit.unit).verify (.cons offset .nil) initial proof =
      ZkcSecurity.Examples.CompiledGuessFiatShamir.compiledVerifier historyQuery offset initial proof := by
  show compiled.verifier (decodedQuery (id : F → F)) (.cons offset .nil) initial proof = _
  rw [decodedQuery_id]
  rfl

/-- `CompiledGuessFiatShamir.soundness`, from the fixed-statement endpoint applied
to the subject's evidence. -/
theorem guess_fixed_soundness (offset : F) (initial : History F G)
    (prover : OracleComp (FieldOracle F G) (Proof F G)) (queries : ℕ)
    (proverBound : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle
        (prover >>= ZkcSecurity.Examples.CompiledGuessFiatShamir.compiledVerifier historyQuery offset initial)).run'
          ∅}[Zkc.Transcript.Accepted (· = some true) result.1] ≤
      (queries + 1) * (Fintype.card F : ℝ≥0∞)⁻¹ := by
  have bound := fixed_soundness (soundness (F := F) (G := G) .idealMeaning .fixed PUnit.unit PUnit.unit) (.cons offset .nil)
    (Contract.falseStatement_all _) initial prover (queries * error)
    (Typed.worstCaseCostBound_of_isTotalQueryBound _ (Typed.keyCharge_le fun _ _ => le_rfl) prover queries
      proverBound)
  have same : (prover >>= ZkcSecurity.Examples.CompiledGuessFiatShamir.compiledVerifier historyQuery offset initial) =
      prover >>= (soundness (F := F) (G := G) .idealMeaning .fixed PUnit.unit PUnit.unit).verify (.cons offset .nil) initial :=
    congrArg (prover >>= ·) (funext fun proof => (guess_verify_eq offset initial proof).symm)
  refine (le_of_eq (congrArg (fun computation => Pr{let result ← (simulateQ randomOracle computation).run' ∅}[
    Zkc.Transcript.Accepted (· = some true) result.1]) same)).trans (bound.trans (le_of_eq ?_))
  change (queries : ℝ≥0∞) * error (F := F) + error (F := F) = _
  rw [← add_one_mul, error, ENNReal.coe_inv (by simp [Fintype.card_ne_zero]), ENNReal.coe_natCast]

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Statement determination by the policy-derived binding, as a named hypothesis
discharged by the codec's proof. -/
def determination (application : String) : Hypothesis where
  identifier := "binding.statement-determination"
  category := .binding .statementDetermination
  claim := Zkc.Transcript.Determined (policyCodec (F := F) (G := G) artifacts.publics application).encode
  status := .proved (policyCodec artifacts.publics application).determined

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem determination_discharged (application : String) :
    (determination (F := F) (G := G) application).status.Discharged :=
  trivial

end Guess

/-! ## Controls -/

section Controls

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

abbrev Scalar := ZMod 5

/-- Program bytes require lowering evidence. -/
example (art : Artifacts) (c : Compiled art) :
    LoweringRequirement art c Scalar Scalar .executableBytes = LoweringEvidence art c Scalar Scalar := rfl

/-- The ideal meaning requires none. -/
example (art : Artifacts) (c : Compiled art) : LoweringRequirement art c Scalar Scalar .idealMeaning = PUnit :=
  rfl

/-- Adaptive statements require binding evidence. -/
example : BindingRequirement .adaptive = BindingEvidence := rfl

/-- Fixed statements require none. -/
example : BindingRequirement .fixed = PUnit := rfl

set_option smartUnfolding true in
/-- Evidence is indexed by matching artifacts: the composed check refuses the
Schnorr original with the guessing export. -/
theorem mismatched_artifacts : checkCompiled SchnorrProof.imported GuessProof.participant ≠ .ok () := by
  decide +kernel

end Controls

end TestsSecurity.Endpoints
