module

public import ZkcSecurity.Endpoint.Soundness
public import ZkcSecurity.Endpoint.Sigma
public import ZkcSecurity.VCVio.Pruning

@[expose] public section

/-! # Knowledge soundness endpoints

Fixed-statement knowledge soundness of a compiled Proof Entry whose verifier is
the Fiat–Shamir transform of a Sigma protocol, through the generic Sigma bridge
(`ZkcSecurity.Endpoint.Sigma`). Knowledge claims are not stage relations: their
conclusion is an extraction probability, not a bad-event bound, so they keep
their own endpoint. Adaptive knowledge soundness is a separate property and is
not stated here.

The family evidence (`SigmaFamily`) is the family's mathematics over the checked
context: a model validator for every policy statement, a one-challenge
transcript shape, a Sigma protocol for every policy statement with special
soundness, and two facts about the model validator's transform, proved once per
family for every context and challenge function:

- **verifier correspondence** (`transform_shape`): on the typed proof of a
  commitment and a response, the transform asks one challenge, at the initial
  transcript followed by the commitment's events and the challenge occurrence,
  and returns the protocol's verification;
- **shape** (`off_shape`): every other typed proof is rejected on every path; a
  typed proof is either the proof of what it reads as or never accepted.

Evidence of knowledge soundness (`KnowledgeEvidence`) adds the checked
compilation, the model equation (the admitted original validator is the
family's model validator), the statement/witness-relation correspondence (the
application's witness relation is the protocol's relation at the statement's
protocol statement) and, for program bytes, the lowering evidence.

`knowledge_soundness` concludes for the compiled verifier's ideal meaning, read
through complete acceptance, and `knowledge_soundness_bytes` for host
validation of proof bytes: host validation prunes the ideal acceptance of the
decoded typed proof, which is at most the acceptance of what the proof reads as,
so the bound transfers to the prover of what its bytes decode to, for every
codec, instruction budget and expected binding.
-/

set_option autoImplicit false

namespace ZkcSecurity.Endpoint
open OracleComp OracleSpec
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.FiatShamir

section Family
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The family evidence of knowledge soundness through the Sigma bridge, over a
checked context and policy statements. -/
structure SigmaFamily (context : Context) (Policy : Type) (Stmt Wit Commit PrvState Resp : Type) where
  /-- The model validator of a policy statement. -/
  validator : Policy → PIR.Proc (Actions F G) (Option Bool)
  shape : Sigma.Shape F G Commit Resp
  /-- The protocol statement of a policy statement. -/
  key : Policy → Stmt
  rel : Policy → Stmt → Wit → Bool
  sigma : (statement : Policy) → SigmaProtocol Stmt Wit Commit PrvState F Resp (rel statement)
  generable : (statement : Policy) → GenerableRelation Stmt Wit (rel statement)
  sound : ∀ statement, (sigma statement).SpeciallySound
  /-- Verifier correspondence: one challenge, then the protocol's verification. -/
  transform_shape : ∀ {m : Type → Type} [Monad m] [LawfulMonad m] (challenge : History F G → m F)
    (statement : Policy) (initial : History F G) (commitment : Commit) (response : Resp),
    transform context challenge (validator statement) initial (shape.proof commitment response) =
      challenge (initial ++ shape.commitments commitment ++ [shape.challenge]) >>= fun answer =>
        pure (.returned (some ((sigma statement).verify (key statement) commitment answer response)), [])
  /-- Every typed proof is the proof of what it reads as, or rejected on every path. -/
  off_shape : ∀ {m : Type → Type} [Monad m] [LawfulMonad m] (challenge : History F G → m F)
    (statement : Policy) (initial : History F G) (proof : Proof F G),
    proof = shape.proof (shape.read proof).1 (shape.read proof).2 ∨
      verdict <$> transform context challenge (validator statement) initial proof =
        (fun _ => false) <$> transform context challenge (validator statement) initial proof

/-- Evidence of fixed-statement knowledge soundness for artifacts, a covered
endpoint and the application's witness relation `holds`. -/
structure KnowledgeEvidence (art : Artifacts) (endpoint : Semantics) (Stmt Wit Commit PrvState Resp : Type)
    (holds : art.Statement F G → Wit → Prop) where
  compiled : Compiled art
  /-- The replaced service handle at which the model equation is read. -/
  handle : Nat
  family : SigmaFamily (F := F) (G := G) compiled.context (art.Statement F G) Stmt Wit Commit PrvState Resp
  /-- The admitted original validator is the family's model validator. -/
  model : ∀ statement, compiled.original statement handle = family.validator statement
  /-- The application's witness relation is the protocol's relation. -/
  relation : ∀ statement witness,
    holds statement witness ↔ family.rel statement (family.key statement) witness = true
  lowering : LoweringRequirement art compiled F G endpoint
  hypotheses : List Hypothesis

end Family

section Endpoints
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
  {art : Artifacts} {endpoint : Semantics} {Stmt Wit Commit PrvState Resp : Type}
  {holds : art.Statement F G → Wit → Prop}

namespace KnowledgeEvidence
variable (evidence : KnowledgeEvidence art endpoint Stmt Wit Commit PrvState Resp holds)

/-- The compiled verifier's complete acceptance of a commitment and a response,
every challenge answered by the history oracle. -/
def verify (statement : art.Statement F G) (initial : History F G) (proof : Commit × Resp) :
    OracleComp (Sigma.HistorySpec F G) Bool :=
  verdict <$> evidence.compiled.verifier Sigma.historyChallenge statement initial
    (evidence.family.shape.proof proof.1 proof.2)

/-- The compiled verifier corresponds to the family's Sigma protocol, at every
statement and initial transcript. -/
theorem corresponds (statement : art.Statement F G) (initial : History F G) :
    Sigma.Corresponds evidence.family.shape (evidence.family.sigma statement) (evidence.family.key statement)
      initial (evidence.verify statement initial) := by
  intro proof
  rw [verify, Compiled.transform_eq _ _ statement evidence.handle, evidence.model,
    evidence.family.transform_shape, map_bind]
  simp [verdict]

/-- On every typed proof, the compiled verifier's complete acceptance is that of
the proof's reading, or it rejects on every path. -/
theorem verdict_cases {m : Type → Type} [Monad m] [LawfulMonad m] (challenge : History F G → m F)
    (statement : art.Statement F G) (initial : History F G) (proof : Proof F G) :
    verdict <$> evidence.compiled.verifier challenge statement initial proof =
        verdict <$> evidence.compiled.verifier challenge statement initial
          (evidence.family.shape.proof (evidence.family.shape.read proof).1 (evidence.family.shape.read proof).2) ∨
      ∃ (β : Type) (rejecting : m β),
        verdict <$> evidence.compiled.verifier challenge statement initial proof = (fun _ => false) <$> rejecting := by
  rcases evidence.family.off_shape challenge statement initial proof with canonical | rejects
  · exact .inl (by rw [← canonical])
  · refine .inr ⟨_, transform evidence.compiled.context challenge (evidence.family.validator statement) initial
      proof, ?_⟩
    rw [Compiled.transform_eq _ _ statement evidence.handle, evidence.model]
    exact rejects

/-- The probability that the compiled verifier accepts the prover's commitment
and response. -/
noncomputable def acceptance [SampleableType F] (prover : Sigma.Prover F G Stmt Commit Resp)
    (statement : art.Statement F G) (initial : History F G) : ENNReal :=
  Sigma.acceptance prover (evidence.verify statement initial) (evidence.family.key statement) initial

end KnowledgeEvidence

/-- The Sigma bridge applied to evidence at any covered endpoint: the bound of
`knowledge_soundness` for the compiled verifier's ideal meaning. -/
theorem KnowledgeEvidence.knowledge [DecidableEq Commit] [SampleableType F] [Fintype F] [Inhabited F]
    [SampleableType Wit] (evidence : KnowledgeEvidence art endpoint Stmt Wit Commit PrvState Resp holds)
    (statement : art.Statement F G) (initial : History F G) (prover : Sigma.Prover F G Stmt Commit Resp)
    (budget : Nat)
    (bounded : IsQueryBoundP (prover (evidence.family.key statement) initial) (· matches .inr _) budget) :
    let accepting := evidence.acceptance prover statement initial
    accepting * (accepting / (budget + 1 : ENNReal) - _root_.FiatShamir.challengeSpaceInv F) ≤
      Pr{let witness ← _root_.FiatShamir.knowledgeExtractor (evidence.family.sigma statement)
          (evidence.family.generable statement) (History F G ⊕ History F G)
          (evidence.family.shape.reduce prover) (.inl initial) budget (evidence.family.key statement)}[
        holds statement witness] := by
  have bridge := evidence.family.shape.knowledge_soundness (evidence.family.sigma statement)
    (evidence.family.generable statement) (evidence.family.sound statement) prover
    (evidence.family.key statement) initial (evidence.corresponds statement initial) budget bounded
  simp only [KnowledgeEvidence.acceptance, evidence.relation]
  exact bridge

/-- **Fixed-statement knowledge soundness of the compiled verifier's ideal
meaning.** For every policy statement and initial transcript, every prover that
sees the protocol statement and the initial transcript and makes at most
`budget` transcript-oracle queries on every path is accepted by the compiled
verifier, read through complete acceptance, with probability `accepting` such
that VCVio's replay extractor, run on the routed prover, outputs a witness of
the application's relation with probability at least
`accepting * (accepting / (budget + 1) - 1 / |F|)`. Challenges are exactly
uniform field elements of one lazily sampled oracle on typed histories, shared
by the prover and verification. Subtraction is truncated in `ENNReal`. -/
theorem knowledge_soundness [DecidableEq Commit] [SampleableType F] [Fintype F] [Inhabited F]
    [SampleableType Wit] (evidence : KnowledgeEvidence art .idealMeaning Stmt Wit Commit PrvState Resp holds)
    (statement : art.Statement F G) (initial : History F G) (prover : Sigma.Prover F G Stmt Commit Resp)
    (budget : Nat)
    (bounded : IsQueryBoundP (prover (evidence.family.key statement) initial) (· matches .inr _) budget) :
    let accepting := evidence.acceptance prover statement initial
    accepting * (accepting / (budget + 1 : ENNReal) - _root_.FiatShamir.challengeSpaceInv F) ≤
      Pr{let witness ← _root_.FiatShamir.knowledgeExtractor (evidence.family.sigma statement)
          (evidence.family.generable statement) (History F G ⊕ History F G)
          (evidence.family.shape.reduce prover) (.inl initial) budget (evidence.family.key statement)}[
        holds statement witness] :=
  evidence.knowledge statement initial prover budget bounded

section Bytes

/-- A prover of proof bytes for a fixed statement, with uniform coins and the
transcript oracle on every history. -/
abbrev BytesProver (F G Stmt : Type) := Stmt → History F G → OracleComp (Sigma.HistorySpec F G) (List UInt8)

namespace KnowledgeEvidence
variable (evidence : KnowledgeEvidence art .executableBytes Stmt Wit Commit PrvState Resp holds)

/-- The lowering evidence of a claim about program bytes. -/
def lowered : LoweringEvidence art evidence.compiled F G := evidence.lowering

/-- The prover of what its proof bytes decode to and read as, for a statement. -/
def decodedProver (codec : Zkc.Executable.PhysicalType → List UInt8 → Option (Payload F G))
    (statement : art.Statement F G) (prover : BytesProver F G Stmt) : Sigma.Prover F G Stmt Commit Resp :=
  fun key message => (fun bytes => evidence.family.shape.read (evidence.lowered.decoded codec statement bytes)) <$>
    prover key message

/-- The knowledge experiment of host validation: the prover sees the protocol
statement and the initial transcript; its coins and oracle queries precede host
validation of its bytes in one initially empty cache. -/
def bytesRun (codec : Zkc.Executable.PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat)
    (binding : List UInt8) (prover : BytesProver F G Stmt) (statement : art.Statement F G)
    (initial : History F G) : OracleComp (_root_.FiatShamir.Fork.wrappedSpec F) Bool :=
  StateT.run' (simulateQ (Sigma.forwardUniform (F := F) (G := G) + Sigma.historyOracle (F := F) (G := G)) (do
    let bytes ← prover (evidence.family.key statement) initial
    evidence.lowered.validate Sigma.historyChallenge codec budget binding statement initial bytes))
    (∅ : Sigma.Cache F G)

section Probability
variable [SampleableType F]

local instance : ∀ t, MeasurableSpace ((_root_.FiatShamir.Fork.wrappedSpec F).Range t) :=
  fun _ => ⊤
local instance : ∀ t, DiscreteMeasurableSpace ((_root_.FiatShamir.Fork.wrappedSpec F).Range t) :=
  fun _ => inferInstance
noncomputable local instance : IsUniformMeasureSpec (_root_.FiatShamir.Fork.wrappedSpec F) :=
  IsUniformMeasureSpec.ofFiniteNonempty _

/-- The probability that host validation accepts the prover's proof bytes. -/
noncomputable def bytesAcceptance (codec : Zkc.Executable.PhysicalType → List UInt8 → Option (Payload F G))
    (budget : Nat) (binding : List UInt8) (prover : BytesProver F G Stmt) (statement : art.Statement F G)
    (initial : History F G) : ENNReal :=
  Pr{let accepted ← evidence.bytesRun codec budget binding prover statement initial}[accepted = true]

/-- Host validation accepts proof bytes at most as often as the compiled verifier
accepts what they decode to and read as, for every codec, instruction budget and
expected binding. -/
theorem bytesAcceptance_le
    (codec : Zkc.Executable.PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat)
    (binding : List UInt8) (prover : BytesProver F G Stmt) (statement : art.Statement F G)
    (initial : History F G) :
    evidence.bytesAcceptance codec budget binding prover statement initial ≤
      evidence.acceptance (evidence.decodedProver codec statement prover) statement initial := by
  unfold bytesAcceptance bytesRun acceptance Sigma.acceptance Sigma.run decodedProver
  refine (ZkcSecurity.VCVio.Pruning.Prunes.prEvent_le
    (Sigma.forwardUniform (F := F) (G := G) + Sigma.historyOracle (F := F) (G := G))
    (rejects := fun accepted => accepted = false)
    (fun _ rejected accepted => by simp_all)
    (.bind _ _ (fun bytes => verdict <$> evidence.compiled.verifier Sigma.historyChallenge statement initial
      (evidence.lowered.decoded codec statement bytes)) fun bytes =>
        evidence.lowered.prunes Sigma.historyChallenge codec budget binding statement initial bytes) _).trans ?_
  simp only [bind_map_left, simulateQ_bind, StateT.run'_bind']
  refine ZkcSecurity.VCVio.Pruning.prEvent_bind_mono _ _ _ _ fun pair => ?_
  obtain ⟨bytes, cache⟩ := pair
  rcases evidence.verdict_cases Sigma.historyChallenge statement initial
    (evidence.lowered.decoded codec statement bytes) with same | ⟨β, rejecting, rejects⟩
  · rw [same]
    exact le_rfl
  · rw [rejects, simulateQ_map, StateT.run'_map', prEvent_map,
      prEvent_eq_zero_of_forall_not _ _ fun _ => Bool.false_ne_true]
    exact zero_le

end Probability

end KnowledgeEvidence

/-- **Fixed-statement knowledge soundness of host validation of program bytes.**
For every policy statement, initial transcript, codec of the native message
bytes, instruction budget and expected binding, every prover of proof bytes that
makes at most `queries` transcript-oracle queries on every path is accepted by
host validation with probability `accepting` such that VCVio's replay
extractor, run on the routed prover of what the bytes decode to, outputs a
witness of the application's relation with probability at least
`accepting * (accepting / (queries + 1) - 1 / |F|)`. -/
theorem knowledge_soundness_bytes [DecidableEq Commit] [SampleableType F] [Fintype F] [Inhabited F]
    [SampleableType Wit] (evidence : KnowledgeEvidence art .executableBytes Stmt Wit Commit PrvState Resp holds)
    (codec : Zkc.Executable.PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat)
    (binding : List UInt8) (statement : art.Statement F G) (initial : History F G)
    (prover : BytesProver F G Stmt) (queries : Nat)
    (bounded : IsQueryBoundP (prover (evidence.family.key statement) initial) (· matches .inr _) queries) :
    let accepting := evidence.bytesAcceptance codec budget binding prover statement initial
    accepting * (accepting / (queries + 1 : ENNReal) - _root_.FiatShamir.challengeSpaceInv F) ≤
      Pr{let witness ← _root_.FiatShamir.knowledgeExtractor (evidence.family.sigma statement)
          (evidence.family.generable statement) (History F G ⊕ History F G)
          (evidence.family.shape.reduce (evidence.decodedProver codec statement prover)) (.inl initial) queries
          (evidence.family.key statement)}[holds statement witness] := by
  intro accepting
  have mapped := (isQueryBoundP_map_iff (prover (evidence.family.key statement) initial)
    (fun bytes => evidence.family.shape.read (evidence.lowered.decoded codec statement bytes)) queries).mpr bounded
  have typed := evidence.knowledge statement initial (evidence.decodedProver codec statement prover)
    queries mapped
  have le := evidence.bytesAcceptance_le codec budget binding prover statement initial
  exact le_trans (mul_le_mul' le (tsub_le_tsub_right (ENNReal.div_le_div_right le _) _)) typed

end Bytes

end Endpoints

end ZkcSecurity.Endpoint
