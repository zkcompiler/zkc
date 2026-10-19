import ZkcSecurity.Endpoint.Knowledge
import ZkcSecurity.Endpoint.Binding
import ZkcSecurity.Families.Schnorr
import ZkcSecurity.Examples.CompiledSchnorrFiatShamir
import ZkcSecurity.Examples.ExecutableSchnorrFiatShamir
import ZkcSecurity.Examples.CompiledGuessFiatShamir
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-! Representative applications of the endpoints to artifact-indexed evidence.

- **Schnorr, knowledge soundness.** Evidence for the compiled `example::Proof`
  Entry from its generated facts (`Compiled`), the Schnorr family package, the
  generated model equation, the retained relation and, for program bytes, the
  generated lowering facts. Its compiled verifier is the one of
  `CompiledSchnorrFiatShamir` (`schnorr_verify_eq`), so the endpoint's subject is
  the same compiled verifier; both knowledge endpoints apply.
- **Guessing Entry, ordinary soundness.** Evidence from the imported ArkLib
  certificate, at the fixed and the adaptive form. The fixed endpoint gives back
  `CompiledGuessFiatShamir.soundness` (`guess_fixed_soundness`); its verifier is
  that theorem's (`guess_verify_eq`), whose bound is attained at zero queries
  (`CompiledGuessFiatShamir.guess_accepted`). The adaptive endpoint, with the
  policy-derived binding of the offset, bounds a prover that chooses the offset
  after its queries by `(Q + 1) / |F|` (`guess_adaptive_soundness`).
- **Controls.** The requirements are selected by the indices: lowering evidence
  exactly for program bytes, binding evidence exactly for adaptive statements.
  Evidence is indexed by the artifacts: the composed check refuses the Schnorr
  original with the guessing export (`mismatched_artifacts`), so no `Compiled`
  value exists for that pair.
-/

namespace TestsSecurity.Endpoints
open OracleComp OracleSpec
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Endpoint ZkcSecurity.FiatShamir
open ZkcExamples.Construction
open scoped ENNReal NNReal

set_option smartUnfolding false

/-! ## Schnorr: fixed-statement knowledge soundness -/

/-- The artifacts of the compiled Schnorr proof Entry. -/
def schnorrArtifacts : Artifacts where
  original := SchnorrProof.snapshot
  participant := SchnorrProof.participant
  publics := [.group "bls12-381.g1", .group "bls12-381.g1"]
  program := some ZkcExamples.Executable.SchnorrProof.validator

set_option smartUnfolding true in
/-- The generated facts of the compiled Schnorr proof Entry. -/
def schnorrCompiled : Compiled schnorrArtifacts where
  imported := SchnorrProof.imported
  compiled := SchnorrProof.compiled
  selection := SchnorrProof.selection
  selected := SchnorrProof.selected
  checked := SchnorrProof.selection_checked
  publics := by decide +kernel

/-- The base and the key of a Schnorr statement. -/
def schnorrParts {F G : Type} : schnorrArtifacts.Statement F G → G × G
  | .cons base (.cons key .nil) => (base, key)

section Schnorr
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
  [SampleableType F] [SampleableType G]

/-- The Schnorr family at the checked context and the example's wiring. -/
def schnorrFamily : SigmaFamily (F := F) (G := G) schnorrCompiled.context (schnorrArtifacts.Statement F G)
    G F G F F :=
  ZkcSecurity.Families.Schnorr.family schnorrCompiled.context SchnorrProof.wiring 0 schnorrParts

omit [SampleableType F] [SampleableType G] in
/-- The generated model equation, read on the artifacts' statements. -/
theorem schnorr_original (base key : G) :
    schnorrCompiled.original (F := F) (.cons base (.cons key .nil)) 0 = SchnorrProof.verifier base key 0 :=
  rfl

theorem schnorr_model (statement : schnorrArtifacts.Statement F G) :
    schnorrCompiled.original statement 0 = schnorrFamily.validator statement := by
  match statement with
  | .cons base (.cons key .nil) =>
      rw [schnorr_original]
      exact SchnorrProof.verifier_correspondence base key 0

/-- The application's witness relation: the relation the Proof Entry's export
retains. -/
def schnorrHolds (statement : schnorrArtifacts.Statement F G) (witness : F) : Prop :=
  ZkcExamples.Construction.SchnorrProofBinding.Relation (schnorrParts statement).1 (schnorrParts statement).2
    witness

theorem schnorr_relation (statement : schnorrArtifacts.Statement F G) (witness : F) :
    schnorrHolds statement witness ↔
      schnorrFamily.rel statement (schnorrFamily.key statement) witness = true := by
  match statement with
  | .cons base (.cons key .nil) => exact ZkcExamples.Construction.SchnorrProofBinding.relation_eq base key witness

/-- The generated lowering facts of the executable Schnorr validator. -/
def schnorrLowering : LoweringEvidence schnorrArtifacts schnorrCompiled F G where
  validator := ZkcExamples.Executable.SchnorrProof.validator
  program := rfl
  lowered := ZkcExamples.Executable.SchnorrProof.lowered
  accepted := ZkcExamples.Executable.SchnorrProof.accepted
  prepared := ZkcExamples.Executable.SchnorrProof.prepared
  sorted := ZkcExamples.Executable.SchnorrProof.helpersSorted
  admits statement := by
    match statement with
    | .cons base (.cons key .nil) => exact ZkcExamples.Executable.SchnorrProof.admitted base key

/-- Knowledge evidence of the compiled Schnorr proof Entry at a covered endpoint. -/
def schnorrEvidence (endpoint : Semantics) (lowering : LoweringRequirement schnorrArtifacts schnorrCompiled F G endpoint) :
    KnowledgeEvidence (F := F) (G := G) schnorrArtifacts endpoint G F G F F schnorrHolds where
  compiled := schnorrCompiled
  handle := 0
  family := schnorrFamily
  model := schnorr_model
  relation := schnorr_relation
  lowering := lowering
  hypotheses := []

omit [SampleableType F] [SampleableType G] in
/-- The evidence's verifier is the compiled verifier of `CompiledSchnorrFiatShamir`. -/
theorem schnorr_verify_eq [SampleableType F] [SampleableType G] (application : String) (base key : G)
    (proof : G × F) :
    (schnorrEvidence .idealMeaning PUnit.unit).verify (.cons base (.cons key .nil))
        (ZkcSecurity.Examples.CompiledSchnorrFiatShamir.initial application base key) proof =
      ZkcSecurity.Examples.CompiledSchnorrFiatShamir.verify application base key proof := by
  unfold KnowledgeEvidence.verify ZkcSecurity.Examples.CompiledSchnorrFiatShamir.verify Compiled.verifier
  rw [Functor.map_map]
  rfl

/-- Knowledge soundness of the compiled Schnorr verifier through the endpoint. -/
theorem schnorr_knowledge [Fintype F] [Inhabited F] (statement : schnorrArtifacts.Statement F G)
    (initial : History F G) (prover : Sigma.Prover F G G G F) (budget : Nat)
    (bounded : IsQueryBoundP (prover (schnorrParts statement).2 initial) (· matches .inr _) budget) :
    let accepting := (schnorrEvidence .idealMeaning PUnit.unit).acceptance prover statement initial
    accepting * (accepting / (budget + 1 : ENNReal) - _root_.FiatShamir.challengeSpaceInv F) ≤
      Pr{let witness ← _root_.FiatShamir.knowledgeExtractor (_root_.Schnorr.sigma F G (schnorrParts statement).1)
          (ZkcSecurity.Families.Schnorr.generable (schnorrParts statement).1) (History F G ⊕ History F G)
          ((ZkcSecurity.Families.Schnorr.shape schnorrCompiled.context SchnorrProof.wiring).reduce prover)
          (.inl initial) budget (schnorrParts statement).2}[schnorrHolds statement witness] :=
  knowledge_soundness (schnorrEvidence .idealMeaning PUnit.unit) statement initial prover budget bounded

/-- Knowledge soundness of the executable Schnorr verifier through the endpoint. -/
theorem schnorr_knowledge_bytes [Fintype F] [Inhabited F]
    (codec : Zkc.Executable.PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat)
    (binding : List UInt8) (statement : schnorrArtifacts.Statement F G) (initial : History F G)
    (prover : BytesProver F G G) (queries : Nat)
    (bounded : IsQueryBoundP (prover (schnorrParts statement).2 initial) (· matches .inr _) queries) :
    let evidence := schnorrEvidence .executableBytes schnorrLowering
    let accepting := evidence.bytesAcceptance codec budget binding prover statement initial
    accepting * (accepting / (queries + 1 : ENNReal) - _root_.FiatShamir.challengeSpaceInv F) ≤
      Pr{let witness ← _root_.FiatShamir.knowledgeExtractor (_root_.Schnorr.sigma F G (schnorrParts statement).1)
          (ZkcSecurity.Families.Schnorr.generable (schnorrParts statement).1) (History F G ⊕ History F G)
          ((ZkcSecurity.Families.Schnorr.shape schnorrCompiled.context SchnorrProof.wiring).reduce
            (evidence.decodedProver codec statement prover))
          (.inl initial) queries (schnorrParts statement).2}[schnorrHolds statement witness] :=
  knowledge_soundness_bytes (schnorrEvidence .executableBytes schnorrLowering) codec budget binding statement initial
    prover queries bounded

end Schnorr

/-! ## The guessing Entry: ordinary soundness -/

/-- The artifacts of the compiled guessing Entry. -/
def guessArtifacts : Artifacts where
  original := GuessProof.snapshot
  participant := GuessProof.participant
  publics := [.field "bls12-381.fr"]
  program := none

set_option smartUnfolding true in
/-- The generated facts of the compiled guessing Entry. -/
def guessCompiled : Compiled guessArtifacts where
  imported := GuessProof.imported
  compiled := GuessProof.compiled
  selection := GuessProof.selection
  selected := GuessProof.selected
  checked := GuessProof.selection_checked
  publics := by decide +kernel

/-- The offset of a guessing statement. -/
def guessOffset {F G : Type} : guessArtifacts.Statement F G → F
  | .cons offset .nil => offset

theorem guessOffset_injective {F G : Type} : Function.Injective (guessOffset (F := F) (G := G)) := by
  intro first second same
  match first, second with
  | .cons _ .nil, .cons _ .nil => cases same; rfl

/-- Every offset is a false statement: a prover cannot predict the challenge. -/
abbrev guessRelation {F G : Type} : StatementRelation F G guessArtifacts.publics where
  Model := F
  models statement offset := guessOffset statement = offset
  functional _ _ _ first second := first.symm.trans second
  falseModel _ := True
  applicationFalse _ := True

section Guess
variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

open ZkcSecurity.Examples.CompiledGuessFiatShamir in
/-- The guessing family: the imported ArkLib certificate, each challenge charged
`1 / |F|`. -/
noncomputable def guessFamily :
    CertificateFamily (G := G) guessCompiled.context (Regime.exact F) (guessRelation (F := F) (G := G)) where
  validator offset := GuessProof.verifier offset 0
  charge _ event := participantError event
  certificate := (certificate (F := F) (G := G)).charged
  doomed offset _ _ := verifier_doomed offset 0

/-- The charge of one challenge. -/
noncomputable def guessError : ENNReal := ((Fintype.card F : ℝ≥0)⁻¹ : ℝ≥0)

omit [Fintype F] [SampleableType F] in
theorem guess_original (offset : F) :
    guessCompiled.original (G := G) (.cons offset .nil) 0 = GuessProof.verifier offset 0 :=
  rfl

theorem guess_costBound (statement : guessArtifacts.Statement F G) (initial : History F G) :
    Typed.ChargedCostBound (interface (G := G) guessCompiled.context (Regime.exact F).decode)
      (guessFamily (F := F) (G := G)).charge (guessCompiled.original statement 0) initial (guessError (F := F)) := by
  match statement with
  | .cons offset .nil =>
      rw [guess_original]
      have bounded := Typed.QueryBound.chargedCostBound (interface (G := G) guessCompiled.context (Regime.exact F).decode)
        (charge := (guessFamily (F := F) (G := G)).charge) (bound := guessError (F := F)) (fun _ _ => le_rfl) _ 1
        (QueryBound.typed _ _ _ 1 (ZkcSecurity.Examples.CompiledGuessFiatShamir.verifier_queryBound offset 0))
        initial
      rwa [Nat.cast_one, one_mul] at bounded

/-- Ordinary soundness evidence of the guessing Entry's ideal meaning at a form. -/
noncomputable def guessEvidence (form : Form)
    (binding : BindingRequirement (guessRelation (F := F) (G := G)) (fun initial statement =>
      (guessFamily (F := F) (G := G)).certificate.doomed initial (guessCompiled.original statement 0)) form) :
    SoundnessEvidence (F := F) (G := G) guessArtifacts .idealMeaning form guessRelation (Regime.exact F) where
  compiled := guessCompiled
  handle := 0
  family := guessFamily
  model statement offset denotes := by
    match statement, denotes with
    | .cons _ .nil, rfl => rfl
  cost _ := guessError
  costBound := guess_costBound
  binding := binding
  lowering := PUnit.unit
  hypotheses := []

omit [Fintype F] [SampleableType F] in
/-- The evidence's verifier is the compiled verifier of `CompiledGuessFiatShamir`. -/
theorem guess_verify_eq [Fintype F] [SampleableType F] (offset : F) (initial : History F G) (proof : Proof F G) :
    (guessEvidence .fixed PUnit.unit).verify (.cons offset .nil) initial proof =
      ZkcSecurity.Examples.CompiledGuessFiatShamir.compiledVerifier historyQuery offset initial proof := by
  show guessCompiled.verifier (decodedQuery (id : F → F)) (.cons offset .nil) initial proof = _
  rw [decodedQuery_id]
  rfl

/-- `CompiledGuessFiatShamir.soundness`, from the fixed-statement endpoint. -/
theorem guess_fixed_soundness (offset : F) (initial : History F G)
    (prover : OracleComp (FieldOracle F G) (Proof F G)) (queries : ℕ)
    (proverBound : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle
        (prover >>= ZkcSecurity.Examples.CompiledGuessFiatShamir.compiledVerifier historyQuery offset initial)).run'
          ∅}[Zkc.Transcript.Accepted (· = some true) result.1] ≤
      (queries + 1) * (Fintype.card F : ℝ≥0∞)⁻¹ := by
  have bound := fixed_soundness (guessEvidence (G := G) .fixed PUnit.unit) (.cons offset .nil)
    ⟨offset, rfl, trivial⟩ initial prover (queries * guessError)
    (Typed.worstCaseCostBound_of_isTotalQueryBound _ (Typed.keyCharge_le fun _ _ => le_rfl) prover queries
      proverBound)
  have same : (prover >>= ZkcSecurity.Examples.CompiledGuessFiatShamir.compiledVerifier historyQuery offset initial) =
      prover >>= (guessEvidence (G := G) .fixed PUnit.unit).verify (.cons offset .nil) initial :=
    congrArg (prover >>= ·) (funext fun proof => (guess_verify_eq offset initial proof).symm)
  refine (le_of_eq (congrArg (fun computation => Pr{let result ← (simulateQ randomOracle computation).run' ∅}[
    Zkc.Transcript.Accepted (· = some true) result.1]) same)).trans (bound.trans (le_of_eq ?_))
  change (queries : ℝ≥0∞) * guessError (F := F) + guessError (F := F) = _
  rw [← add_one_mul, guessError, ENNReal.coe_inv (by simp [Fintype.card_ne_zero]), ENNReal.coe_natCast]

/-- The policy-derived binding of the offset, with every offset false and
denoting itself. -/
def guessBinding (application : String) :
    BindingEvidence (guessRelation (F := F) (G := G)) (fun initial statement =>
      (guessFamily (F := F) (G := G)).certificate.doomed initial (guessCompiled.original statement 0)) where
  codec := policyCodec guessArtifacts.publics application
  coverage := .rejects (fun statement _ => .inl ⟨guessOffset statement, rfl, trivial⟩)
    fun statement unmapped => absurd rfl (unmapped (guessOffset statement))

/-- **Adaptive ordinary soundness of the compiled guessing Entry.** A prover that
chooses the offset after at most `queries` oracle queries, the verifier starting
from the policy-derived binding of the chosen offset, is accepted with
probability at most `(queries + 1) / |F|`. -/
theorem guess_adaptive_soundness (application : String)
    (prover : OracleComp (FieldOracle F G) (guessArtifacts.Statement F G × Proof F G)) (queries : ℕ)
    (proverBound : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle (prover >>= fun claimed =>
        (fun result => (claimed.1, result)) <$>
          (guessEvidence .adaptive (guessBinding application)).verify claimed.1
            ((policyCodec guessArtifacts.publics application).encode claimed.1) claimed.2)).run' ∅}[
      Zkc.Transcript.Accepted (· = some true) result.2.1] ≤ (queries + 1) * (Fintype.card F : ℝ≥0∞)⁻¹ := by
  have bound := adaptive_soundness (guessEvidence (G := G) .adaptive (guessBinding application)) prover
    (queries * guessError)
    (Typed.worstCaseCostBound_of_isTotalQueryBound _ (Typed.keyCharge_le fun _ _ => le_rfl) prover queries
      proverBound)
  refine (prEvent_mono _ _ _ fun result accepted => ⟨trivial, accepted⟩).trans (bound.trans (le_of_eq ?_))
  change (queries : ℝ≥0∞) * guessError (F := F) + ⨆ _ : guessArtifacts.Statement F G, guessError (F := F) = _
  have : Nonempty (guessArtifacts.Statement F G) := ⟨.cons 0 .nil⟩
  rw [ciSup_const, ← add_one_mul, guessError, ENNReal.coe_inv (by simp [Fintype.card_ne_zero]),
    ENNReal.coe_natCast]

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
example {publics : List Ty} (relation : StatementRelation Scalar Scalar publics)
    (doomed : History Scalar Scalar → Values (assignment Scalar Scalar) publics → Prop) :
    BindingRequirement relation doomed .adaptive = BindingEvidence relation doomed := rfl

/-- Fixed statements require none. -/
example {publics : List Ty} (relation : StatementRelation Scalar Scalar publics)
    (doomed : History Scalar Scalar → Values (assignment Scalar Scalar) publics → Prop) :
    BindingRequirement relation doomed .fixed = PUnit := rfl

set_option smartUnfolding true in
/-- Evidence is indexed by matching artifacts: the composed check refuses the
Schnorr original with the guessing export. -/
theorem mismatched_artifacts : checkCompiled SchnorrProof.imported GuessProof.participant ≠ .ok () := by
  decide +kernel

end Controls

end TestsSecurity.Endpoints
