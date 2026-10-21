import ZkcSecurity.Examples.Subjects.Schnorr.Claims
import ZkcSecurity.Examples.Subjects.Guess.Claims
import ZkcSecurity.Examples.Subjects.Sumcheck.Claims
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-! Controls for the endpoints and the subjects' evidence.

- **Guessing Entry.** The subject's evidence at the fixed form gives back
  `CompiledGuessFiatShamir.soundness` for that theorem's verifier
  (`guess_verify_eq`, `guess_fixed_soundness`), a bound attained at zero queries
  (`CompiledGuessFiatShamir.guess_accepted`). Statement determination of the
  adaptive claim's binding is a named hypothesis of the binding category,
  discharged by the codec's proof (`determination_discharged`).
- **Sumcheck.** A malformed statement the contract counts as false (a vector
  with one entry at one round, whose claim is not its total) denotes no model
  statement, its original validator is doomed after every initial transcript
  (`malformed_doomed`), and the fixed-statement endpoint bounds acceptance on it
  (`malformed_soundness`).
- **Wrong validator.** The Schnorr original interacts before it decides, so no
  family whose validator accepts outright satisfies the model equation
  (`wrong_validator`).
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
  have bound := ZkcSecurity.Examples.Subjects.Guess.fixed_soundness (F := F) (G := G) (.cons offset .nil)
    (Contract.falseStatement_all _) initial prover (queries * error)
    (Typed.worstCaseCostBound_of_isTotalQueryBound _ (Typed.keyCharge_le fun _ _ => le_rfl) prover queries
      proverBound)
  have same : (prover >>= ZkcSecurity.Examples.CompiledGuessFiatShamir.compiledVerifier historyQuery offset initial) =
      prover >>= (fixedIdealEvidence (F := F) (G := G)).verify (.cons offset .nil) initial :=
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

section Sumcheck
variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]
open ZkcSecurity.Examples.Subjects

/-- A vector with one entry at one round: no table has that shape. -/
def malformed : Sumcheck.artifacts.Statement F G := .cons [1] (.cons 0 (.cons 1 .nil))

omit [Fintype F] [SampleableType F] in
/-- The contract counts it false: its claim is not its total. -/
theorem malformed_false : Sumcheck.Contract.falseStatement (malformed (F := F) (G := G)) := by
  change ¬ ZkcExamples.Structured.SumcheckContractBindings.PublicTruth (G := G) [(1 : F)] 0
  unfold ZkcExamples.Structured.SumcheckContractBindings.PublicTruth
  rw [ZkcExamples.Structured.SumcheckContractBindings.public_formula_equation [(1 : F)] 0
    (by rw [List.length_singleton]; decide)]
  simp only [List.sum_singleton, zero_ne_one, decide_false]
  nofun

omit [Fintype F] [SampleableType F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- It denotes no model statement. -/
theorem malformed_unmapped : (Sumcheck.relation (F := F) (G := G)).Unmapped malformed := by
  rintro ⟨raw, claim, count, table, decoded⟩ ⟨same, _⟩
  simp only [malformed, Sumcheck.parts, Prod.mk.injEq] at same
  obtain ⟨rawEq, -, countEq⟩ := same
  subst rawEq countEq
  simp [Zkc.Polynomial.Multilinear.ofList?] at decoded

/-- Its original validator is doomed after every initial transcript. -/
theorem malformed_doomed (initial : History F G) :
    (Sumcheck.family (F := F) (G := G)).certificate.doomed initial
      (Sumcheck.compiled.original (malformed (F := F) (G := G)) 0) :=
  Sumcheck.unmapped _ malformed_unmapped initial

/-- The fixed-statement endpoint bounds acceptance on it. -/
theorem malformed_soundness (initial : History F G) (prover : OracleComp (FieldOracle F G) (Proof F G))
    (proverCost : ENNReal)
    (proverBound : WorstCaseCostBound prover ⟨Typed.keyCharge (Sumcheck.family (F := F) (G := G)).charge⟩ proverCost) :
    Pr{let result ← (simulateQ randomOracle
        (prover >>= (Sumcheck.fixedIdealEvidence (F := F) (G := G)).verify malformed initial)).run' ∅}[
        Zkc.Transcript.Accepted (· = some true) result.1] ≤
      proverCost + Sumcheck.cost (F := F) :=
  Sumcheck.fixed_soundness malformed malformed_false initial prover proverCost proverBound

end Sumcheck

section WrongValidator
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
open ZkcSecurity.Examples.Subjects

/-- The Schnorr original interacts before it decides: it is not a validator that
accepts outright, so no family with such a validator meets the model equation. -/
theorem wrong_validator (base key : G) :
    Schnorr.compiled.original (F := F) (.cons base (.cons key .nil)) 0 ≠ .done (some true) := by
  rw [Schnorr.original_eq, SchnorrProof.verifier_correspondence]
  nofun

end WrongValidator

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

section RetainedContracts
open ZkcSecurity.Examples.Subjects

/-- Changing the false set to False cannot satisfy the actual pinning field:
the retained Sumcheck target has a false statement, even though no table has
this vector's shape at the supplied round count. -/
theorem false_predicate_rejected {F G : Type} [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] [DecidableEq G] :
    ¬ (∀ statement, False ↔
      (SoundnessTarget.retained Sumcheck.Contract.retained).FalseStatement
        (F := F) (G := G) statement) := by
  intro pin
  exact (pin malformed).mpr ((Sumcheck.Contract.falseStatement_pinned _).mp malformed_false)

/-- A valid retained witness also prevents replacing the knowledge relation
with False. The relation is read at the published zero base and point. -/
theorem false_knowledge_relation_rejected {F G : Type} [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] [DecidableEq G] :
    ¬ (∀ statement witness, False ↔ Schnorr.Contract.retained.Holds statement
      (Schnorr.Contract.embed (F := F) (G := G) witness)) := by
  intro pin
  apply (pin (.cons (0 : G) (.cons 0 .nil)) (0 : F)).mpr
  apply (Schnorr.Contract.holds_pinned _ _).mp
  rw [Schnorr.Contract.holds_iff, SchnorrProofBinding.relation_iff]
  simp

/-- The imported-language escape hatch is unavailable to a subject with an
actual retained clause. Empty owner records in the guessing fixture are fine. -/
theorem retained_language_alternative_rejected :
    Schnorr.artifacts.original.contracts.all (fun contract => contract.clauses.isEmpty) = false := by
  decide +kernel

set_option smartUnfolding true in
/-- The internal Sumcheck reduction's input clause is not an endpoint target. -/
theorem wrong_target_kind :
    ZkcExamples.Structured.SumcheckContractBindings.reductionClause.kind ≠ .target := by
  decide +kernel

set_option smartUnfolding true in
/-- The sole retained Schnorr target has no alternative clause index. -/
theorem wrong_target_index : ¬ 1 < Schnorr.Contract.retained.owner.contract.clauses.length := by
  decide +kernel

set_option smartUnfolding true in
/-- A published input cannot become a witness by changing its purpose. -/
theorem published_witness_rejected :
    targetSelectorsSupported Schnorr.artifacts.participant.policy ["witness", "statement", "witness"]
      SchnorrProofBinding.application.selectors = false := by
  decide +kernel

set_option smartUnfolding true in
/-- A private producer input cannot become a fixed public parameter. -/
theorem private_parameter_rejected :
    targetSelectorsSupported Schnorr.artifacts.participant.policy ["parameter", "statement", "parameter"]
      SchnorrProofBinding.application.selectors = false := by
  decide +kernel

set_option smartUnfolding true in
theorem unknown_purpose_rejected :
    targetSelectorsSupported Schnorr.artifacts.participant.policy ["parameter", "unknown", "witness"]
      SchnorrProofBinding.application.selectors = false := by
  decide +kernel

set_option smartUnfolding true in
theorem missing_purpose_rejected :
    targetSelectorsSupported Schnorr.artifacts.participant.policy ["parameter", "statement"]
      SchnorrProofBinding.application.selectors = false := by
  decide +kernel

set_option smartUnfolding true in
/-- A retained output selector has no policy input reading. -/
theorem output_argument_rejected :
    targetSelectorsSupported Sumcheck.artifacts.participant.policy ["statement"]
      (Values.cons ZkcExamples.Structured.SumcheckContractBindings.publicDecision .nil) = false := by
  decide +kernel

/-- Changing the public binding changes the ordered formula arguments. An
embedding supplies the witness only, even if it also supplies public coordinates. -/
theorem changed_public_binding {F G : Type}
    (base point : G) (different : base ≠ point) (witness : F) :
    Schnorr.Contract.retained.arguments (.cons base (.cons point .nil)) (Schnorr.Contract.embed witness) ≠
      some (Schnorr.Contract.arguments (.cons point (.cons base .nil)) witness) := by
  change some (Schnorr.Contract.arguments (.cons base (.cons point .nil)) witness) ≠ _
  intro same
  have values := Option.some.inj same
  exact different (congrArg (fun values => values.get .here) values)

/-- A witness's proposed replacement for a public parameter is ignored. -/
theorem witness_cannot_replace_parameter {F G : Type}
    (base point replacement : G) (witness : F) :
    Schnorr.Contract.retained.arguments (.cons base (.cons point .nil))
      (fun type _ => match type with
        | .group _ => some replacement
        | .field _ => some witness
        | _ => none) =
      some (Schnorr.Contract.arguments (.cons base (.cons point .nil)) witness) := rfl

end RetainedContracts

end TestsSecurity.Endpoints
