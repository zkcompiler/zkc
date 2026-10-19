module

public import ZkcSecurity.Endpoint.Evidence
public import ZkcSecurity.Stage.FiatShamir

@[expose] public section

/-! # Ordinary soundness endpoints

Four endpoint theorems state ordinary soundness of a compiled Proof Entry from
its evidence (`SoundnessEvidence`): for a fixed or an adaptively chosen
statement, of the compiled verifier's ideal meaning or of host validation of
program bytes. Each is a chain of quantitative stage relations
(`ZkcSecurity.Stage.Relation`) from the trivial game, composed with
`Relation.comp`, whose loss is the endpoint's bound:

1. **Fiat–Shamir.** The family's charged certificate bounds the typed
   experiment of the admitted original validator through the keyed endpoint
   (`Typed.soundness_charged`, `Stage.weightedRelation`; both are applications
   of `ZkcSecurity.FiatShamir.KeyedCertificate.soundness`), at the prover's
   pathwise weighted budget plus the original validator's charge.
2. **Construction.** The compiled verifier is the transform of the admitted
   original validator (`Compiled.transform_eq`), so the compiled experiment is
   the typed one, a zero-loss stage (`Relation.ofImage`).
3. **Executable bytes.** A prover of proof bytes is translated into the prover
   of the typed proofs its bytes decode to at the validator's receive types
   (`Relation.ofLe`), with the same weighted budget; host validation prunes the
   ideal acceptance of the decoded proof by rejections at every instruction
   budget and with every framing header (`validate_prunes_export`), a zero-loss
   stage (`Relation.ofPrunesImage`).

Fixed-statement endpoints bound the acceptance of a policy statement that
denotes a false model statement. Adaptive endpoints let the prover choose any
policy statement, malformed ones included, after its queries; the verifier
starts from the binding codec's initial transcript of that statement, which
determines it, and the bound covers every statement the application counts as
false, through the evidence's coverage. The validator charge of an adaptive
endpoint is the supremum of the per-statement charges.

The prover's budget is its pathwise weighted cost (`WorstCaseCostBound`), every
oracle key charged the family's charge of its last event after the history
before it. A total query bound with every charge at most `bound` gives the
budget `queries * bound` (`Typed.worstCaseCostBound_of_isTotalQueryBound`).
-/

set_option autoImplicit false

namespace ZkcSecurity.Endpoint
open OracleComp OracleSpec
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.FiatShamir ZkcSecurity.Stage

/-- The challenge function of a regime: the oracle's answer at the absorbed
history, decoded. -/
abbrev Regime.challenge {F G : Type} (regime : Regime F) : History F G → OracleComp (Oracle F G regime.Answer) F :=
  decodedQuery regime.decode

section Bounds
variable {I : PIR.Signature} {E P A : Type} {Raw : E → Type} (absorb : Typed.Interface I E P Raw)

/-- A larger cost bounds the charged queries too. -/
theorem chargedCostBound_mono (charge : List E → E → ENNReal) :
    ∀ (process : PIR.Proc I A) (history : List E) {cost larger : ENNReal},
      Typed.ChargedCostBound absorb charge process history cost → cost ≤ larger →
        Typed.ChargedCostBound absorb charge process history larger
  | .done _, _, _, _, _, _ => trivial
  | .halt _, _, _, _, _, _ => trivial
  | .call operation next, history, _, _, bounded, le => by
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      · simp only [Typed.ChargedCostBound, absorbed] at bounded ⊢
        exact fun message value recovered =>
          chargedCostBound_mono charge (next value) _ (bounded message value recovered) le
      · simp only [Typed.ChargedCostBound, absorbed] at bounded ⊢
        exact chargedCostBound_mono charge (next value) _ bounded le
      · simp only [Typed.ChargedCostBound, absorbed] at bounded ⊢
        obtain ⟨remaining, charged, rest⟩ := bounded
        exact ⟨remaining, charged.trans le, rest⟩
      · simp only [Typed.ChargedCostBound, absorbed]

end Bounds

section Endpoints
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
  {art : Artifacts} {endpoint : Semantics} {form : Form} {relation : StatementRelation F G art.publics}
  {regime : Regime F}

namespace SoundnessEvidence
variable (evidence : SoundnessEvidence art endpoint form relation regime)

/-- The transcript interface of the checked context with the regime's decoding. -/
abbrev absorb : Typed.Interface (Actions F G) (Event F G) (Payload F G) fun _ => regime.Answer :=
  interface (G := G) evidence.compiled.context regime.decode

/-- The compiled verifier on a statement, with the regime's challenges. -/
abbrev verify (statement : art.Statement F G) (initial : History F G) (proof : Proof F G) :
    OracleComp (Oracle F G regime.Answer) (PIR.Outcome (Option Bool) × Proof F G) :=
  evidence.compiled.verifier regime.challenge statement initial proof

/-- The compiled verifier is the typed transform of the admitted original
validator over the checked context's interface. -/
theorem verify_eq (statement : art.Statement F G) (initial : History F G) (proof : Proof F G) :
    evidence.verify statement initial proof =
      Typed.transform evidence.absorb Typed.ask (evidence.compiled.original statement evidence.handle)
        initial proof := by
  rw [verify, Compiled.transform_eq _ _ statement evidence.handle, transform_eq]

/-- The original validator of a statement that denotes a false model statement
is doomed after every initial transcript. -/
theorem original_doomed {statement : art.Statement F G} (falseStatement : relation.FalseStatement statement)
    (initial : History F G) :
    evidence.family.certificate.doomed initial (evidence.compiled.original statement evidence.handle) := by
  obtain ⟨model, denotes, falseModel⟩ := falseStatement
  rw [evidence.model statement model denotes]
  exact evidence.family.doomed model initial falseModel

/-- The original validator's charge is at most the supremum of the
per-statement charges. -/
theorem costBound_iSup (statement : art.Statement F G) (initial : History F G) :
    Typed.ChargedCostBound evidence.absorb evidence.family.charge
      (evidence.compiled.original statement evidence.handle) initial (⨆ other, evidence.cost other) :=
  chargedCostBound_mono _ _ _ _ (evidence.costBound statement initial) (le_iSup evidence.cost statement)

end SoundnessEvidence

section Fixed
variable (evidence : SoundnessEvidence art endpoint form relation regime)

/-- The fixed-statement game of a verifier on proofs: provers are oracle
computations with a pathwise weighted budget, the bad event is acceptance. -/
noncomputable def fixedGame (verifier : Proof F G →
    OracleComp (Oracle F G regime.Answer) (PIR.Outcome (Option Bool) × Proof F G)) : Game :=
  oracleGame (fun _ : History F G => regime.Answer) (OracleComp (Oracle F G regime.Answer) (Proof F G))
    ENNReal (fun cost prover => WorstCaseCostBound prover ⟨Typed.keyCharge evidence.family.charge⟩ cost)
    (fun prover => prover >>= verifier) fun result => Zkc.Transcript.Accepted (· = some true) result.1

/-- The Fiat–Shamir stage: the typed transform of the doomed original validator
is bounded at every weighted budget `c` by `c` plus the validator's charge. -/
noncomputable def fixedTyped (statement : art.Statement F G)
    (falseStatement : relation.FalseStatement statement) (initial : History F G) :
    Relation Game.trivial (fixedGame evidence fun proof => Typed.transform evidence.absorb Typed.ask
      (evidence.compiled.original statement evidence.handle) initial proof) :=
  Relation.ofBound _ (fun cost : ENNReal => cost + evidence.cost statement) fun cost prover admissible =>
    Typed.soundness_charged evidence.family.certificate _ initial
      (evidence.original_doomed falseStatement initial) _ (evidence.costBound statement initial) prover cost
      admissible

/-- The construction stage: the compiled experiment is the typed one. -/
noncomputable def fixedConstruction (statement : art.Statement F G) (initial : History F G) :
    Relation (fixedGame evidence fun proof => Typed.transform evidence.absorb Typed.ask
        (evidence.compiled.original statement evidence.handle) initial proof)
      (fixedGame evidence (evidence.verify statement initial)) :=
  Relation.ofImage _ _ _ id (fun _ accepted => accepted) fun prover => by
    rw [id_map]
    exact congrArg (prover >>= ·) (funext fun proof => evidence.verify_eq statement initial proof)

/-- The ideal-meaning stages composed. -/
noncomputable def fixedIdeal (statement : art.Statement F G)
    (falseStatement : relation.FalseStatement statement) (initial : History F G) :
    Relation Game.trivial (fixedGame evidence (evidence.verify statement initial)) :=
  (fixedTyped evidence statement falseStatement initial).comp (fixedConstruction evidence statement initial)

theorem fixedIdeal_loss (statement : art.Statement F G) (falseStatement : relation.FalseStatement statement)
    (initial : History F G) (cost : ENNReal) :
    (fixedIdeal evidence statement falseStatement initial).loss cost = cost + evidence.cost statement :=
  zero_add _

end Fixed

/-- **Ordinary soundness of the compiled verifier's ideal meaning, fixed
statement.** For a policy statement that denotes a false model statement and
every initial transcript, a prover of typed proofs whose oracle queries charge
at most `proverCost` on every path makes the compiled verifier accept with
probability at most `proverCost` plus the original validator's charge on the
statement, in one lazily sampled random oracle on all typed histories with
the regime's challenges, shared by the prover and the verifier. -/
theorem fixed_soundness (evidence : SoundnessEvidence art .idealMeaning .fixed relation regime)
    (statement : art.Statement F G) (falseStatement : relation.FalseStatement statement)
    (initial : History F G) (prover : OracleComp (Oracle F G regime.Answer) (Proof F G)) (proverCost : ENNReal)
    (proverBound : WorstCaseCostBound prover ⟨Typed.keyCharge evidence.family.charge⟩ proverCost) :
    Pr{let result ← (simulateQ randomOracle
        (prover >>= evidence.verify statement initial)).run' ∅}[
      Zkc.Transcript.Accepted (· = some true) result.1] ≤ proverCost + evidence.cost statement := by
  have bounded := (fixedIdeal evidence statement falseStatement initial).bounded proverCost prover proverBound
  rwa [fixedIdeal_loss] at bounded

section Adaptive
variable (evidence : SoundnessEvidence art endpoint .adaptive relation regime)

namespace SoundnessEvidence

/-- The binding evidence of an adaptive claim. -/
def bound : BindingEvidence relation (fun initial statement =>
    evidence.family.certificate.doomed initial (evidence.compiled.original statement evidence.handle)) :=
  evidence.binding

/-- The binding codec of an adaptive claim: the initial transcript of every policy
statement. -/
abbrev codec : BindingCodec (art.Statement F G) (Event F G) := evidence.bound.codec

end SoundnessEvidence

/-- The adaptive game of a verifier on statements and proofs: provers choose a
statement and a proof after their queries, with a pathwise weighted budget. -/
noncomputable def adaptiveGame {Result : Type}
    (verifier : art.Statement F G → Proof F G → OracleComp (Oracle F G regime.Answer) Result)
    (event : art.Statement F G × Result → Prop) : Game :=
  oracleGame (fun _ : History F G => regime.Answer)
    (OracleComp (Oracle F G regime.Answer) (art.Statement F G × Proof F G)) ENNReal
    (fun cost prover => WorstCaseCostBound prover ⟨Typed.keyCharge evidence.family.charge⟩ cost)
    (fun prover => prover >>= fun claimed => (fun result => (claimed.1, result)) <$>
      verifier claimed.1 claimed.2) event

/-- The compiled adaptive game: the verifier starts from the binding codec's
initial transcript of the chosen statement. -/
noncomputable def compiledAdaptiveGame : Game :=
  adaptiveGame evidence (fun statement => evidence.verify statement (evidence.codec.encode statement))
    fun result => relation.applicationFalse result.1 ∧ Zkc.Transcript.Accepted (· = some true) result.2.1

/-- The Fiat–Shamir and construction stages for adaptive statements, for the
statements a predicate counts as false, whose validators are doomed. -/
noncomputable def adaptiveStages (falseStatement : art.Statement F G → Prop)
    (doomed : ∀ statement, falseStatement statement → evidence.family.certificate.doomed
      (evidence.codec.encode statement) (evidence.compiled.original statement evidence.handle))
    (implies : ∀ statement (outcome : PIR.Outcome (Option Bool)),
      relation.applicationFalse statement ∧ Zkc.Transcript.Accepted (· = some true) outcome →
        falseStatement statement ∧ Zkc.Transcript.Accepted (· = some true) outcome) :
    Relation Game.trivial (compiledAdaptiveGame evidence) :=
  (weightedRelation (R := fun _ : History F G => regime.Answer) evidence.family.certificate
    (fun statement => evidence.compiled.original statement evidence.handle) evidence.codec.encode
    evidence.codec.determined falseStatement doomed (⨆ statement, evidence.cost statement)
    fun statement => evidence.costBound_iSup statement _).comp
  (Relation.ofImage _ _ _ id (fun result accepted => implies result.1 result.2.1 accepted) fun prover => by
    rw [id_map]
    exact congrArg (prover >>= ·) (funext fun claimed => congrArg ((fun result => (claimed.1, result)) <$> ·)
      (evidence.verify_eq claimed.1 (evidence.codec.encode claimed.1) claimed.2)))

/-- The adaptive stages through the evidence's coverage. -/
noncomputable def adaptiveIdeal : Relation Game.trivial (compiledAdaptiveGame evidence) :=
  match evidence.bound.coverage with
  | .rejects covers unmapped =>
      adaptiveStages evidence relation.applicationFalse
        ((StatementBinding.mk evidence.codec relation.models relation.functional).doomed_of_covers covers
          (fun statement model denotes falseModel => by
            rw [evidence.model statement model denotes]
            exact evidence.family.doomed model _ falseModel) unmapped)
        fun _ _ holds => holds
  | .implies implication =>
      adaptiveStages evidence relation.FalseStatement
        (fun statement falseStatement => evidence.original_doomed falseStatement _)
        fun statement outcome holds => implication (statement, outcome) holds

theorem adaptiveStages_loss (falseStatement : art.Statement F G → Prop)
    (doomed : ∀ statement, falseStatement statement → evidence.family.certificate.doomed
      (evidence.codec.encode statement) (evidence.compiled.original statement evidence.handle))
    (implies : ∀ statement (outcome : PIR.Outcome (Option Bool)),
      relation.applicationFalse statement ∧ Zkc.Transcript.Accepted (· = some true) outcome →
        falseStatement statement ∧ Zkc.Transcript.Accepted (· = some true) outcome) (cost : ENNReal) :
    (adaptiveStages evidence falseStatement doomed implies).loss cost =
      cost + ⨆ statement, evidence.cost statement :=
  zero_add _

theorem adaptiveIdeal_loss (cost : ENNReal) :
    (adaptiveIdeal evidence).loss cost = cost + ⨆ statement, evidence.cost statement := by
  unfold adaptiveIdeal
  split <;> exact adaptiveStages_loss _ _ _ _ cost

end Adaptive

/-- **Ordinary soundness of the compiled verifier's ideal meaning, adaptive
statement.** A prover that chooses a policy statement, malformed ones included,
and a typed proof after its oracle queries, charging at most `proverCost` on
every path, makes the compiled verifier, started from the binding codec's
initial transcript of the chosen statement, accept a statement the application
counts as false with probability at most `proverCost` plus the supremum of the
original validator's per-statement charges. -/
theorem adaptive_soundness (evidence : SoundnessEvidence art .idealMeaning .adaptive relation regime)
    (prover : OracleComp (Oracle F G regime.Answer) (art.Statement F G × Proof F G)) (proverCost : ENNReal)
    (proverBound : WorstCaseCostBound prover ⟨Typed.keyCharge evidence.family.charge⟩ proverCost) :
    Pr{let result ← (simulateQ randomOracle (prover >>= fun claimed =>
        (fun result => (claimed.1, result)) <$>
          evidence.verify claimed.1 (evidence.codec.encode claimed.1) claimed.2)).run' ∅}[
      relation.applicationFalse result.1 ∧ Zkc.Transcript.Accepted (· = some true) result.2.1] ≤
      proverCost + ⨆ statement, evidence.cost statement := by
  have bounded := (adaptiveIdeal evidence).bounded proverCost prover proverBound
  rwa [adaptiveIdeal_loss] at bounded

section Bytes
variable {c : Compiled art}

namespace LoweringEvidence
variable (lowering : LoweringEvidence art c F G)

/-- The typed proof that proof bytes decode to, after the framing header, at the
executable validator's receive types for a statement. -/
def decoded (codec : Zkc.Executable.PhysicalType → List UInt8 → Option (Payload F G))
    (statement : art.Statement F G) (bytes : List UInt8) : Proof F G :=
  Zkc.Executable.decodeProof codec (Zkc.Executable.Plan.types (encodeValues statement) lowering.lowered.plan)
    (bytes.drop 40)

/-- Host validation of proof bytes for a statement: the framing header must name
the expected binding, then the executable validator runs under the checked
context, at an instruction budget, on the statement's published values and the
initial transcript, and accepts at the selected output with the whole proof
read. -/
def validate {m : Type → Type} [Monad m] (challenge : History F G → m F)
    (codec : Zkc.Executable.PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat)
    (binding : List UInt8) (statement : art.Statement F G) (initial : History F G) (bytes : List UInt8) :
    m Bool :=
  Zkc.Executable.validate Zkc.Executable.installed lowering.validator c.context challenge codec budget binding
    c.position (encodeValues statement) initial bytes

/-- Host validation prunes, by rejections, the complete acceptance of the
compiled verifier on the decoded proof, at every budget and with every framing
header. -/
theorem prunes {m : Type → Type} [Monad m] [LawfulMonad m] (challenge : History F G → m F)
    (codec : Zkc.Executable.PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat)
    (binding : List UInt8) (statement : art.Statement F G) (initial : History F G) (bytes : List UInt8) :
    Zkc.Executable.Prunes (fun accepted => accepted = false)
      (lowering.validate challenge codec budget binding statement initial bytes)
      (verdict <$> c.verifier challenge statement initial (lowering.decoded codec statement bytes)) := by
  have pruned := Zkc.Executable.validate_prunes_export Zkc.Executable.installed lowering.validator c.context
    challenge (helperTable c.imported.program F G) codec budget lowering.accepted lowering.prepared
    lowering.sorted binding c.position (encodeValues statement) initial bytes (lowering.admits statement)
  have same : verdict <$> c.verifier challenge statement initial (lowering.decoded codec statement bytes) =
      (fun result => Zkc.Executable.Accepts c.position (Zkc.Executable.idealObservation result)) <$>
        ideal c.context challenge (helperTable c.imported.program F G) art.participant.returned
          art.participant.instructions (encodeValues statement ++ [.transcript initial])
          (lowering.decoded codec statement bytes) := by
    rw [Compiled.verifier, Functor.map_map]
    exact congrArg (· <$> _) (funext fun result => verdict_eq c.position result)
  rw [same]
  exact pruned

end LoweringEvidence

end Bytes

namespace SoundnessEvidence
variable (evidence : SoundnessEvidence art .executableBytes form relation regime)

/-- The lowering evidence of a claim about program bytes. -/
def lowered : LoweringEvidence art evidence.compiled F G := evidence.lowering

end SoundnessEvidence

section FixedBytes
variable (evidence : SoundnessEvidence art .executableBytes form relation regime)
  (codec : Zkc.Executable.PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat)
  (binding : List UInt8)

/-- The fixed-statement game of host validation: provers output proof bytes. -/
noncomputable def bytesGame {Result : Type}
    (verifier : List UInt8 → OracleComp (Oracle F G regime.Answer) Result) (event : Result → Prop) : Game :=
  oracleGame (fun _ : History F G => regime.Answer) (OracleComp (Oracle F G regime.Answer) (List UInt8))
    ENNReal (fun cost prover => WorstCaseCostBound prover ⟨Typed.keyCharge evidence.family.charge⟩ cost)
    (fun prover => prover >>= verifier) event

/-- The decoding stage: a prover of bytes is the prover of the typed proofs its
bytes decode to, with the same weighted budget. -/
noncomputable def fixedDecoding (statement : art.Statement F G) (initial : History F G) :
    Relation (fixedGame evidence (evidence.verify statement initial))
      (bytesGame evidence (fun bytes => evidence.verify statement initial
        (evidence.lowered.decoded codec statement bytes))
        fun result => Zkc.Transcript.Accepted (· = some true) result.1) :=
  Relation.ofLe (fun prover => evidence.lowered.decoded codec statement <$> prover) (fun cost => cost)
    (fun cost prover admissible => Typed.worstCaseCostBound_map _ prover _ cost admissible)
    fun cost prover _ => by
      have same : (prover >>= fun bytes => evidence.verify statement initial
          (evidence.lowered.decoded codec statement bytes)) =
          (evidence.lowered.decoded codec statement <$> prover) >>= evidence.verify statement initial :=
        (bind_map_left _ _ _).symm
      exact le_of_eq (congrArg (fun computation => Pr{let result ← (simulateQ randomOracle computation).run' ∅}[
        Zkc.Transcript.Accepted (· = some true) result.1]) same)

/-- The pruning stage: host validation prunes the complete acceptance of the
decoded proof by rejections. -/
noncomputable def fixedPruning (statement : art.Statement F G) (initial : History F G) :
    Relation (bytesGame evidence (fun bytes => evidence.verify statement initial
        (evidence.lowered.decoded codec statement bytes))
        fun result => Zkc.Transcript.Accepted (· = some true) result.1)
      (bytesGame evidence (evidence.lowered.validate regime.challenge codec budget binding statement initial)
        fun accepted => accepted = true) :=
  Relation.ofPrunesImage _ _ _ verdict (rejects := fun accepted => accepted = false)
    (fun _ rejected accepted => by simp_all) (fun _ accepted => accepted_of_verdict accepted)
    fun prover => by
      rw [map_bind]
      exact .bind _ _ _ fun bytes => evidence.lowered.prunes _ codec budget binding statement initial bytes

/-- The program-bytes stages composed. -/
noncomputable def fixedBytes (statement : art.Statement F G) (falseStatement : relation.FalseStatement statement)
    (initial : History F G) :
    Relation Game.trivial
      (bytesGame evidence (evidence.lowered.validate regime.challenge codec budget binding statement initial)
        fun accepted => accepted = true) :=
  ((fixedIdeal evidence statement falseStatement initial).comp
    (fixedDecoding evidence codec statement initial)).comp
    (fixedPruning evidence codec budget binding statement initial)

theorem fixedBytes_loss (statement : art.Statement F G) (falseStatement : relation.FalseStatement statement)
    (initial : History F G) (cost : ENNReal) :
    (fixedBytes evidence codec budget binding statement falseStatement initial).loss cost =
      cost + evidence.cost statement := by
  change 0 + (0 + (fixedIdeal evidence statement falseStatement initial).loss cost) = _
  rw [zero_add, zero_add, fixedIdeal_loss]

end FixedBytes

/-- **Ordinary soundness of host validation of program bytes, fixed statement.**
For a policy statement that denotes a false model statement, every initial
transcript, every codec of the native message bytes, every instruction budget
and every expected binding, a prover of proof bytes whose oracle queries charge
at most `proverCost` on every path makes host validation accept with
probability at most `proverCost` plus the original validator's charge on the
statement. -/
theorem fixed_soundness_bytes (evidence : SoundnessEvidence art .executableBytes .fixed relation regime)
    (codec : Zkc.Executable.PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat)
    (binding : List UInt8) (statement : art.Statement F G) (falseStatement : relation.FalseStatement statement)
    (initial : History F G) (prover : OracleComp (Oracle F G regime.Answer) (List UInt8)) (proverCost : ENNReal)
    (proverBound : WorstCaseCostBound prover ⟨Typed.keyCharge evidence.family.charge⟩ proverCost) :
    Pr{let accepted ← (simulateQ randomOracle (prover >>=
        evidence.lowered.validate regime.challenge codec budget binding statement initial)).run' ∅}[
      accepted = true] ≤ proverCost + evidence.cost statement := by
  have bounded := (fixedBytes evidence codec budget binding statement falseStatement initial).bounded proverCost
    prover proverBound
  rwa [fixedBytes_loss] at bounded

section AdaptiveBytes
variable (evidence : SoundnessEvidence art .executableBytes .adaptive relation regime)
  (codec : Zkc.Executable.PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat)
  (binding : List UInt8)

/-- The adaptive game of host validation: provers choose a statement and output
proof bytes. -/
noncomputable def adaptiveBytesGame {Result : Type}
    (verifier : art.Statement F G → List UInt8 → OracleComp (Oracle F G regime.Answer) Result)
    (event : art.Statement F G × Result → Prop) : Game :=
  oracleGame (fun _ : History F G => regime.Answer)
    (OracleComp (Oracle F G regime.Answer) (art.Statement F G × List UInt8)) ENNReal
    (fun cost prover => WorstCaseCostBound prover ⟨Typed.keyCharge evidence.family.charge⟩ cost)
    (fun prover => prover >>= fun claimed => (fun result => (claimed.1, result)) <$>
      verifier claimed.1 claimed.2) event

/-- The adaptive decoding stage. -/
noncomputable def adaptiveDecoding :
    Relation (compiledAdaptiveGame evidence)
      (adaptiveBytesGame evidence (fun statement bytes => evidence.verify statement
        (evidence.codec.encode statement) (evidence.lowered.decoded codec statement bytes))
        fun result => relation.applicationFalse result.1 ∧ Zkc.Transcript.Accepted (· = some true) result.2.1) :=
  Relation.ofLe (fun prover => (fun claimed : art.Statement F G × List UInt8 =>
      (claimed.1, evidence.lowered.decoded codec claimed.1 claimed.2)) <$> prover) (fun cost => cost)
    (fun cost prover admissible => Typed.worstCaseCostBound_map _ prover _ cost admissible)
    fun cost prover _ => by
      have same : (prover >>= fun claimed : art.Statement F G × List UInt8 =>
          (fun result => (claimed.1, result)) <$> evidence.verify claimed.1 (evidence.codec.encode claimed.1)
            (evidence.lowered.decoded codec claimed.1 claimed.2)) =
          ((fun claimed : art.Statement F G × List UInt8 =>
            (claimed.1, evidence.lowered.decoded codec claimed.1 claimed.2)) <$> prover) >>=
            fun claimed => (fun result => (claimed.1, result)) <$>
              evidence.verify claimed.1 (evidence.codec.encode claimed.1) claimed.2 :=
        (bind_map_left (fun claimed : art.Statement F G × List UInt8 =>
          (claimed.1, evidence.lowered.decoded codec claimed.1 claimed.2)) prover
          fun claimed => (fun result => (claimed.1, result)) <$>
            evidence.verify claimed.1 (evidence.codec.encode claimed.1) claimed.2).symm
      exact le_of_eq (congrArg (fun computation => Pr{let result ← (simulateQ randomOracle computation).run' ∅}[
        relation.applicationFalse result.1 ∧ Zkc.Transcript.Accepted (· = some true) result.2.1]) same)

/-- The adaptive pruning stage. -/
noncomputable def adaptivePruning :
    Relation (adaptiveBytesGame evidence (fun statement bytes => evidence.verify statement
        (evidence.codec.encode statement) (evidence.lowered.decoded codec statement bytes))
        fun result => relation.applicationFalse result.1 ∧ Zkc.Transcript.Accepted (· = some true) result.2.1)
      (adaptiveBytesGame evidence (fun statement => evidence.lowered.validate regime.challenge codec budget binding
        statement (evidence.codec.encode statement))
        fun result => relation.applicationFalse result.1 ∧ result.2 = true) :=
  Relation.ofPrunesImage _ _ _
    (fun result : art.Statement F G × (PIR.Outcome (Option Bool) × Proof F G) => (result.1, verdict result.2))
    (rejects := fun result => result.2 = false)
    (fun _ rejected accepted => by simp_all)
    (fun _ accepted => ⟨accepted.1, accepted_of_verdict accepted.2⟩)
    fun prover => by
      rw [map_bind]
      refine .bind _ _ _ fun claimed => ?_
      rw [Functor.map_map]
      have pruned := (evidence.lowered.prunes regime.challenge codec budget binding claimed.1
        (evidence.codec.encode claimed.1) claimed.2).map (fun accepted => (claimed.1, accepted))
        (rejects' := fun result => result.2 = false) fun _ rejected => rejected
      rwa [Functor.map_map] at pruned

/-- The adaptive program-bytes stages composed. -/
noncomputable def adaptiveBytes :
    Relation Game.trivial
      (adaptiveBytesGame evidence (fun statement => evidence.lowered.validate regime.challenge codec budget binding
        statement (evidence.codec.encode statement))
        fun result => relation.applicationFalse result.1 ∧ result.2 = true) :=
  ((adaptiveIdeal evidence).comp (adaptiveDecoding evidence codec)).comp
    (adaptivePruning evidence codec budget binding)

theorem adaptiveBytes_loss (cost : ENNReal) :
    (adaptiveBytes evidence codec budget binding).loss cost = cost + ⨆ statement, evidence.cost statement := by
  change 0 + (0 + (adaptiveIdeal evidence).loss cost) = _
  rw [zero_add, zero_add, adaptiveIdeal_loss]

end AdaptiveBytes

/-- **Ordinary soundness of host validation of program bytes, adaptive
statement.** A prover that chooses a policy statement, malformed ones included,
and outputs proof bytes after its oracle queries, charging at most `proverCost`
on every path, makes host validation, started from the binding codec's initial
transcript of the chosen statement, accept a statement the application counts
as false with probability at most `proverCost` plus the supremum of the
original validator's per-statement charges, for every codec of the native
message bytes, instruction budget and expected binding. -/
theorem adaptive_soundness_bytes (evidence : SoundnessEvidence art .executableBytes .adaptive relation regime)
    (codec : Zkc.Executable.PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat)
    (binding : List UInt8) (prover : OracleComp (Oracle F G regime.Answer) (art.Statement F G × List UInt8))
    (proverCost : ENNReal)
    (proverBound : WorstCaseCostBound prover ⟨Typed.keyCharge evidence.family.charge⟩ proverCost) :
    Pr{let result ← (simulateQ randomOracle (prover >>= fun claimed =>
        (fun accepted => (claimed.1, accepted)) <$> evidence.lowered.validate regime.challenge codec budget
          binding claimed.1 (evidence.codec.encode claimed.1) claimed.2)).run' ∅}[
      relation.applicationFalse result.1 ∧ result.2 = true] ≤
      proverCost + ⨆ statement, evidence.cost statement := by
  have bounded := (adaptiveBytes evidence codec budget binding).bounded proverCost prover proverBound
  rwa [adaptiveBytes_loss] at bounded

end Endpoints

end ZkcSecurity.Endpoint
