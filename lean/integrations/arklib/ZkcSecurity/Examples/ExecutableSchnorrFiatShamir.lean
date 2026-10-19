module

public import ZkcSecurity.Examples.CompiledSchnorrFiatShamir
public import ZkcExamples.Executable.SchnorrProof

@[expose] public section

/-! Knowledge soundness of the executable Schnorr verifier.

The subject is the validator participant of the `zkc.program/0` candidate that
the native deployment of `example::Proof` carries and the runtime admits
(`ZkcExamples.Executable.SchnorrProof`). Its meaning is `Zkc.Executable.validate`:
the framing header must name the expected invocation binding, length-framed
messages are decoded at their receive types by a decoder, every instruction is
charged against a budget, local calls enter and leave frames, and the
transcript is an affine unit of the ideal transcript model. The lowering rule
accepted it against the constructed validator of `CompiledSchnorrFiatShamir`.

A prover here outputs proof bytes. `decoded` turns it into a prover of typed
proofs by decoding its bytes. For every proof, host validation either is the
ideal verification of the decoded pair or rejects on every path
(`validate_cases`); acceptance by the executable is therefore bounded by
acceptance of the decoded prover (`acceptance_le`), and the extraction bound of
`CompiledSchnorrFiatShamir.knowledge_soundness` transfers for every decoder,
budget and expected binding (`knowledge_soundness`). No property of the decoder
is needed for this bound. The chain runs through general rules: the lowering
rule (`checkLowering`, `validate_ideal`, `validate_rejects`) and the composed
transcript-construction and participant projection rules
(`Zkc.Construction.compiled_transform` applied to the admitted original,
through `ZkcExamples.Construction.SchnorrProof.compiled_transform`); no equation
about the compiled program's meaning specific to this Entry is assumed. On the
original side, the kernel checks by evaluation that the admitted original's
validator is the common Schnorr experiment the VCVio consumer uses
(`SchnorrProof.process_equation`) and gives the process of the DLog formula the
original retains (`SchnorrProofBinding.formula_process`), from which the
knowledge target is read.

Named assumptions beyond those of `CompiledSchnorrFiatShamir`: the runtime
executes the admitted program as `validate` describes, its installed operations
implement the meanings of `Zkc.Executable.installed`, and its codec is a
function of a message's bytes and type.
-/

namespace ZkcSecurity.Examples.ExecutableSchnorrFiatShamir
open OracleComp OracleSpec
open Zkc.Construction Zkc.Executable
open ZkcExamples.Construction
open ZkcSecurity.Examples.CompiledSchnorrFiatShamir

abbrev executable : Validator := ZkcExamples.Executable.SchnorrProof.validator
abbrev lowered : Lowered := ZkcExamples.Executable.SchnorrProof.lowered

section Bytes
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The typed pair the message bytes after the framing header decode to, or a
default pair. -/
def decodePair (decode : PhysicalType → List UInt8 → Option (Payload F G)) (bytes : List UInt8) :
    G × F :=
  match decodeProof decode ZkcExamples.Executable.SchnorrProof.receives (bytes.drop 40) with
  | [.group _ commitment, .field _ response] => (commitment, response)
  | _ => (0, 0)

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The ideal acceptance of the compiled verifier is the host acceptance of
its observation. -/
theorem accepted_eq (result : PIR.Outcome (List (Value F G)) × Proof F G) :
    accepted (mapOutcome SchnorrProof.acceptance result.1, result.2) =
      Accepts SchnorrProof.acceptancePosition (idealObservation result) := by
  rcases result with ⟨outcome, unread⟩
  cases outcome with
  | stopped stop => simp [accepted, mapOutcome, Accepts, idealObservation, observation, Decision]
  | returned values =>
      simp only [mapOutcome, idealObservation, observation, Accepts, Decision, SchnorrProof.acceptance,
        selectedTrue]
      cases selected : values[SchnorrProof.acceptancePosition]? with
      | none => cases unread <;> simp [accepted]
      | some value =>
          cases value with
          | data payload =>
              cases payload with
              | boolean decision => cases unread <;> cases decision <;> simp [accepted]
              | field => cases unread <;> simp [accepted]
              | group => cases unread <;> simp [accepted]
          | index => cases unread <;> simp [accepted]
          | vector => cases unread <;> simp [accepted]
          | transcript => cases unread <;> simp [accepted]
          | indices => cases unread <;> simp [accepted]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem value_group {payload : Payload F G} {domain : String} {value : G}
    (decoded : payload.value (.group domain) = some value) : payload = .group domain value := by
  cases payload with
  | group other found =>
      simp only [Payload.value] at decoded
      split_ifs at decoded with same
      cases decoded
      rw [same]
  | boolean => simp [Payload.value] at decoded
  | field => simp [Payload.value] at decoded

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem value_field {payload : Payload F G} {domain : String} {value : F}
    (decoded : payload.value (.field domain) = some value) : payload = .field domain value := by
  cases payload with
  | field other found =>
      simp only [Payload.value] at decoded
      split_ifs at decoded with same
      cases decoded
      rw [same]
  | boolean => simp [Payload.value] at decoded
  | group => simp [Payload.value] at decoded

omit [DecidableEq F] in
/-- On a typed proof that is not a commitment followed by a response, the
transform of the original verifier rejects on every path. -/
theorem transform_rejects {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (prior : History F G) (base key : G) (handle : Nat)
    (proof : Proof F G)
    (bad : ∀ (commitment : G) (response : F),
      proof ≠ [.group groupDomain commitment, .field fieldDomain response]) :
    accepted <$> transform SchnorrProof.context challenge
        (Zkc.Protocols.Schnorr.Common.experiment SchnorrProof.wiring base key handle) prior proof =
      (fun _ => false) <$> transform SchnorrProof.context challenge
        (Zkc.Protocols.Schnorr.Common.experiment SchnorrProof.wiring base key handle) prior proof := by
  unfold Zkc.Protocols.Schnorr.Common.experiment
  rcases proof with _ | ⟨first, rest⟩
  · simp [transform_eq_receive, accepted]
  · cases decodedFirst : first.value (.group SchnorrProof.wiring.groupDomain) with
    | none => simp [transform_eq_receive, decodedFirst, accepted]
    | some commitment =>
        have firstEq : first = .group groupDomain commitment := value_group decodedFirst
        rcases rest with _ | ⟨second, rest₂⟩
        · simp [transform_eq_receive, transform_eq_query, transform_eq_send, decodedFirst, accepted,
            Payload.ofValue]
        · cases decodedSecond : second.value (.field SchnorrProof.wiring.fieldDomain) with
          | none => simp [transform_eq_receive, transform_eq_query, transform_eq_send, decodedFirst,
              decodedSecond, accepted, Payload.ofValue]
          | some response =>
              have secondEq : second = .field fieldDomain response := value_field decodedSecond
              rcases rest₂ with _ | ⟨third, rest₃⟩
              · exact absurd (by rw [firstEq, secondEq]) (bad commitment response)
              · simp [transform_eq_done, transform_eq_receive, transform_eq_query, transform_eq_send,
                  decodedFirst, decodedSecond, accepted, Payload.ofValue]

/-- Host validation of proof bytes, with the transcript oracle answering every
challenge. -/
def verifyBytes (decode : PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat)
    (binding : List UInt8) (application : String) (base key : G) (bytes : List UInt8) :
    OracleComp (HistorySpec F G) Bool :=
  validate installed executable SchnorrProof.context historyChallenge decode budget binding
    SchnorrProof.acceptancePosition (ZkcExamples.Executable.SchnorrProof.data base key)
    (initial application base key) bytes

/-- Proof bytes with the expected framing header whose messages decode to a
commitment and a response are validated, at a budget of at least 25, exactly as
the ideal compiled verifier verifies that pair. -/
theorem verifyBytes_eq_verify (decode : PhysicalType → List UInt8 → Option (Payload F G))
    {budget : Nat} (sufficient : 25 ≤ budget) (binding : List UInt8) (application : String)
    (base key : G) (bytes : List UInt8) (header : bytes.take 40 = magic ++ binding)
    {commitment : G} {response : F}
    (decoded : decodeProof decode ZkcExamples.Executable.SchnorrProof.receives (bytes.drop 40) =
      [.group groupDomain commitment, .field fieldDomain response]) :
    verifyBytes decode budget binding application base key bytes =
      verify application base key (commitment, response) := by
  rw [verifyBytes, ZkcExamples.Executable.SchnorrProof.executable_validate historyChallenge decode
    sufficient binding base key (initial application base key) bytes header, decoded]
  unfold verify
  simp only [accepted_eq]

/-- Host validation of proof bytes is the ideal verification of the pair they
decode to, or it rejects on every path: when the budget is below 25, the
framing header names another binding, or the messages are not a commitment
followed by a response. -/
theorem validate_cases (decode : PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat)
    (binding : List UInt8) (application : String) (base key : G) (bytes : List UInt8) :
    verifyBytes decode budget binding application base key bytes =
        verify application base key (decodePair decode bytes) ∨
      ∃ (β : Type) (rejecting : OracleComp (HistorySpec F G) β),
        verifyBytes decode budget binding application base key bytes = (fun _ => false) <$> rejecting := by
  by_cases short : budget < 25 ∨ bytes.take 40 ≠ magic ++ binding
  · exact .inr ⟨Bool, _, ZkcExamples.Executable.SchnorrProof.executable_rejects historyChallenge decode
      binding base key (initial application base key) bytes short⟩
  · have sufficient : 25 ≤ budget := by omega
    have header : bytes.take 40 = magic ++ binding := by
      by_contra different
      exact short (.inr different)
    have exec := ZkcExamples.Executable.SchnorrProof.executable_validate historyChallenge decode
      sufficient binding base key (initial application base key) bytes header
    by_cases good : ∃ (commitment : G) (response : F),
        decodeProof decode ZkcExamples.Executable.SchnorrProof.receives (bytes.drop 40) =
          [.group groupDomain commitment, .field fieldDomain response]
    · obtain ⟨commitment, response, decoded⟩ := good
      left
      have pair : decodePair decode bytes = (commitment, response) := by
        unfold decodePair
        rw [decoded]
      rw [pair]
      exact verifyBytes_eq_verify decode sufficient binding application base key bytes header decoded
    · right
      refine ⟨_, transform SchnorrProof.context historyChallenge
        (Zkc.Protocols.Schnorr.Common.experiment SchnorrProof.wiring base key 0)
        (initial application base key) (decodeProof decode ZkcExamples.Executable.SchnorrProof.receives (bytes.drop 40)), ?_⟩
      have compiled := SchnorrProof.compiled_transform historyChallenge base key 0
        (initial application base key) (decodeProof decode ZkcExamples.Executable.SchnorrProof.receives (bytes.drop 40))
      rw [SchnorrProof.verifier_correspondence] at compiled
      rw [verifyBytes, exec]
      calc (fun result => Accepts SchnorrProof.acceptancePosition (idealObservation result)) <$>
            ideal SchnorrProof.context historyChallenge SchnorrProof.table SchnorrProof.participant.returned
              SchnorrProof.participant.instructions
              ((SchnorrProof.inputs base key).map .data ++ [.transcript (initial application base key)])
              (decodeProof decode ZkcExamples.Executable.SchnorrProof.receives (bytes.drop 40))
          = accepted <$> ((fun result => (mapOutcome SchnorrProof.acceptance result.1, result.2)) <$>
              ideal SchnorrProof.context historyChallenge SchnorrProof.table SchnorrProof.participant.returned
                SchnorrProof.participant.instructions
                ((SchnorrProof.inputs base key).map .data ++ [.transcript (initial application base key)])
                (decodeProof decode ZkcExamples.Executable.SchnorrProof.receives (bytes.drop 40))) := by
            rw [Functor.map_map]
            simp only [accepted_eq]
        _ = _ := by
            rw [compiled]
            exact transform_rejects historyChallenge _ base key 0 _ fun commitment response same =>
              good ⟨commitment, response, same⟩

end Bytes

/-- Pointwise dominated continuations bound the event after a common draw. -/
theorem prEvent_bind_mono {m : Type → Type} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] {α β : Type} (start : m α) (first second : α → m β) (event : β → Prop)
    (dominated : ∀ value, Pr{let result ← first value}[event result] ≤
      Pr{let result ← second value}[event result]) :
    Pr{let result ← start >>= first}[event result] ≤
      Pr{let result ← start >>= second}[event result] := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete]
  exact MeasureTheory.lintegral_mono dominated

section Experiment
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
  [SampleableType F] [SampleableType G]

/-- A prover of proof bytes, with uniform coins and the transcript oracle on
every history. -/
abbrev ByteProver (F G : Type) := G → History F G → OracleComp (HistorySpec F G) (List UInt8)

/-- The byte prover's proofs, decoded as pairs. -/
def decoded (decode : PhysicalType → List UInt8 → Option (Payload F G)) (prover : ByteProver F G) :
    Prover F G :=
  fun key message => decodePair decode <$> prover key message

/-- The prover sees the statement and initialized transcript; its coins and
oracle queries precede host validation of its bytes in one initially empty
cache. -/
def runBytes (decode : PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat)
    (binding : List UInt8) (prover : ByteProver F G) (application : String) (base key : G) :
    OracleComp (_root_.FiatShamir.Fork.wrappedSpec F) Bool :=
  StateT.run' (simulateQ (forwardUniform (F := F) (G := G) + historyOracle (F := F) (G := G)) (do
    let bytes ← prover key (initial application base key)
    verifyBytes decode budget binding application base key bytes)) (∅ : Cache F G)

local instance : ∀ t, MeasurableSpace ((_root_.FiatShamir.Fork.wrappedSpec F).Range t) :=
  fun _ => ⊤
local instance : ∀ t, DiscreteMeasurableSpace ((_root_.FiatShamir.Fork.wrappedSpec F).Range t) :=
  fun _ => inferInstance
noncomputable local instance : IsUniformMeasureSpec (_root_.FiatShamir.Fork.wrappedSpec F) :=
  IsUniformMeasureSpec.ofFiniteNonempty _

/-- Probability that host validation accepts the prover's proof bytes. -/
noncomputable def acceptanceBytes (decode : PhysicalType → List UInt8 → Option (Payload F G))
    (budget : Nat) (binding : List UInt8) (prover : ByteProver F G) (application : String)
    (base key : G) : ENNReal :=
  Pr{let result ← runBytes decode budget binding prover application base key}[result = true]

omit [SampleableType G] in
/-- The executable accepts proof bytes at most as often as the ideal compiled
verifier accepts their decoded pairs, for every decoder, budget and expected
binding. -/
theorem acceptance_le (decode : PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat)
    (binding : List UInt8) (prover : ByteProver F G) (application : String) (base key : G) :
    acceptanceBytes decode budget binding prover application base key ≤
      acceptance (decoded decode prover) application base key := by
  unfold acceptanceBytes acceptance runBytes CompiledSchnorrFiatShamir.run decoded
  simp only [bind_map_left, simulateQ_bind, StateT.run'_bind']
  refine prEvent_bind_mono _ _ _ _ fun pair => ?_
  obtain ⟨bytes, cache⟩ := pair
  rcases validate_cases decode budget binding application base key bytes with same | ⟨β, rejecting, rejects⟩
  · rw [same]
  · rw [rejects, simulateQ_map, StateT.run'_map', prEvent_map,
      prEvent_eq_zero_of_forall_not _ _ fun _ => Bool.false_ne_true]
    exact zero_le

variable [Fintype F] [Inhabited F]

/-- Knowledge soundness of the executable Schnorr verifier under the named
assumptions above, for every prover of proof bytes with the transcript oracle on
all histories, every decoder, host budget and expected binding. `queries`
bounds the prover's oracle queries; the extractor runs on the decoded prover,
and the conclusion is the authored relation retained by the Proof Entry. -/
theorem knowledge_soundness (decode : PhysicalType → List UInt8 → Option (Payload F G))
    (budget : Nat) (binding : List UInt8) (prover : ByteProver F G) (application : String)
    (base key : G) (queries : Nat)
    (bounded : IsQueryBoundP (prover key (initial application base key)) (· matches .inr _) queries) :
    let accepting := acceptanceBytes decode budget binding prover application base key
    accepting * (accepting / (queries + 1 : ENNReal) - _root_.FiatShamir.challengeSpaceInv F) ≤
      Pr{let witness ← _root_.FiatShamir.knowledgeExtractor (_root_.Schnorr.sigma F G base)
          (ZkcSecurity.Examples.StructuredSchnorrFiatShamir.generable base) (History F G ⊕ History F G)
          (reduce (decoded decode prover)) (.inl (initial application base key)) queries key}[
        ZkcExamples.Construction.SchnorrProofBinding.Relation base key witness] := by
  intro accepting
  have mapped := (isQueryBoundP_map_iff (prover key (initial application base key))
    (decodePair decode) queries).mpr bounded
  have typed := CompiledSchnorrFiatShamir.knowledge_soundness (decoded decode prover) application base
    key queries (by
      convert mapped using 2
      rfl)
  have le := acceptance_le decode budget binding prover application base key
  refine le_trans ?_ typed
  exact mul_le_mul' le (tsub_le_tsub_right (ENNReal.div_le_div_right le _) _)

end Experiment

end ZkcSecurity.Examples.ExecutableSchnorrFiatShamir
