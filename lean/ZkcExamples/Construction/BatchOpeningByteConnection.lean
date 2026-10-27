module

public import ZkcExamples.Construction.BatchOpeningConnection
public import ZkcExamples.Construction.BatchOpeningCodec

@[expose] public section

/-! Connection of the actual constructed batch producer/validator to the selected
interpreted bytes. Each proof frame is decoded completely; additional frames are
left unread, as in Domain execution. Scalar words and sequence lengths use eight
little-endian bytes. This is not native ZKCV framing or KZG security.
-/
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace ZkcExamples.Construction.BatchOpeningByteConnection
open Zkc.Source Zkc.Construction Zkc.DataCodec
open Zkc.Source.Structured (indexLimit)
open BatchOpeningCodec

/-- The codec's nominal schema is exactly the exported source and artifact ABI. -/
theorem schema_agreement : BatchOpening.openingTy = openingTy ∧ BatchOpening.batchTy = batchTy ∧
    BatchOpening.producer.inputs = [.data batchTy] ∧
    BatchOpening.validator.inputs = [.data (.field "koala-bear"), .data (.field "koala-bear")] ∧
    BatchOpening.validator.outputs = [.data .boolean, .data batchTy] ∧
    BatchOpening.validator.returned = [3, 2] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> kernel_rfl

/-- Context coordinates, source roles, scopes, and the actual single message
agree. The interpreted format identifier is an out-of-band codec selection. -/
theorem context_agreement :
    BatchOpening.producer.policy = BatchOpening.validator.policy ∧
    exportContext BatchOpening.snapshot BatchOpening.validator = some BatchOpening.context ∧
    context.entry = BatchOpening.context.entry ∧
    context.producer = BatchOpening.context.producer ∧ context.validator = BatchOpening.context.validator ∧
    context.schema = BatchOpening.batchTy ∧ context.orderedFields = ["point", "value"] ∧
    BatchOpening.context.profile = .plain ∧
    BatchOpening.context.role context.producer = "role00000000" ∧
    BatchOpening.context.role context.validator = "role00000001" ∧
    BatchOpeningBodies.runSignature.inputScopes = [[1], [1], [0]] ∧
    BatchOpeningBodies.runSignature.outputScopes = [[1], [1]] ∧
    BatchOpening.producer.instructions = [⟨.send context.messageSite context.messageSite
      (BatchOpening.context.role context.validator), [0], [], []⟩] ∧
    BatchOpening.validator.instructions = [⟨.receive context.messageSite context.messageSite
      (BatchOpening.context.role context.producer) context.schema, [], [.data context.schema], []⟩,
      ⟨.call BatchOpeningBodies.checkBatchHelper.name, [0, 1, 2], [.data .boolean], []⟩] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> kernel_rfl

theorem payload_agreement (batch : Batch) : BatchOpening.payload model batch = toPayload batch := rfl

theorem decision_agreement (point value : Scalar) (batch : Batch) :
    BatchOpeningConnection.decision point value batch = checkBatch point value batch := by
  simp only [BatchOpeningConnection.decision, checkBatch, Bool.beq_eq_decide_eq]

abbrev inputs (point value : Scalar) := BatchOpeningConnection.inputs (G := Scalar) point value
abbrev received (point value : Scalar) (batch : Batch) := BatchOpeningConnection.received (G := Scalar) point value batch
abbrev result (point value : Scalar) (batch : Batch) := BatchOpeningConnection.result (G := Scalar) point value batch

/-- Both actual returned coordinates and the complete physical frame use the
same selected decision, for true and false answers alike. -/
theorem result_eq (point value : Scalar) (batch : Batch) :
    result point value batch =
      ⟨[.data (.boolean (checkBatch point value batch)), .data (toPayload batch)],
        [.data (.field "koala-bear" point), .data (.field "koala-bear" value),
          .data (toPayload batch), .data (.boolean (checkBatch point value batch))]⟩ := by
  rw [← decision_agreement]
  rfl

/-- Runtime proof framing is explicit. Bytes inside one frame must be exhausted;
frames after the received message remain available to the caller. -/
structure ByteState (S : Type) where
  environment : Domain.Environment carriers
  proof : List Bytes
  oracle : S

/-- Only the effect handler changes. Arithmetic, helpers, control, return slots,
and all physical checkpoints use the existing actual Domain Process. Services
are refused in this selected plain transport; the artifact has no service call. -/
def handler {S : Type} (mode : Domain.Mode) (supplied : BatchOpeningCodec.Context) :
    PIR.Handler (Domain.effects carriers) (ByteState S) (Domain.Event carriers)
  | .checkpoint env, state => ⟨.returned (), { state with environment := env }, []⟩
  | .observe event, state => ⟨.returned (), state, [event]⟩
  | .receive ty _ _ _, state =>
      match mode, state.proof with
      | .validator, input :: unread =>
          match decode supplied input >>= (·.value ty) with
          | none => ⟨.stopped .refused, state, []⟩
          | some batch => ⟨.returned batch, { state with proof := unread }, []⟩
      | _, _ => ⟨.stopped .refused, state, []⟩
  | .send _ _ _ payload, state =>
      match mode with
      | .validator => ⟨.returned (), state, []⟩
      | .producer =>
          match encode supplied payload with
          | none => ⟨.stopped .refused, state, []⟩
          | some output => ⟨.returned (), { state with proof := state.proof ++ [output] }, []⟩
  | .query .., state => ⟨.stopped .refused, state, []⟩
  | .localService .., state => ⟨.stopped .refused, state, []⟩

def decodeBatch (supplied : BatchOpeningCodec.Context) (input : Bytes) : Option Batch :=
  decode supplied input >>= (·.value batchTy)

theorem decodeBatch_eq (supplied : BatchOpeningCodec.Context) (input : Bytes) :
    decodeBatch supplied input = if supplied = context then batchCodec.decode input else none := by
  by_cases same : supplied = context
  · subst supplied
    simp only [decodeBatch, decode, ↓reduceIte, PayloadCodec.decode]
    cases parsed : batchCodec.decode input <;>
      simp [payloadCodec, PayloadCodec.pack, Domain.Payload.value]
  · simp [decodeBatch, decode, same]

theorem decodeBatch_sound {supplied : BatchOpeningCodec.Context} {input : Bytes} {batch : Batch}
    (decoded : decodeBatch supplied input = some batch) :
    supplied = context ∧ batch.length ≤ maximumOpenings ∧ input = batchCodec.bytes batch := by
  rw [decodeBatch_eq] at decoded
  split at decoded
  · obtain ⟨admitted, canonical⟩ := batchCodec.decode_sound decoded
    exact ⟨by assumption, (batch_admitted batch).1 admitted, canonical⟩
  · cases decoded

theorem runtime_admitted (batch : Batch) (bounded : batch.length ≤ maximumOpenings) :
    batch.length < indexLimit := by
  have : maximumOpenings < indexLimit := by decide
  omega

def validate {S : Type} (point value : Scalar) (supplied : BatchOpeningCodec.Context) (proof : List Bytes) (initial : S) :=
  (Domain.participant model BatchOpening.program BatchOpening.context BatchOpening.validator (inputs point value)).run
    (handler .validator supplied) ⟨inputs point value, proof, initial⟩

def produce {S : Type} (batch : Batch) (supplied : BatchOpeningCodec.Context) (preceding : List Bytes) (initial : S) :=
  (Domain.participant model BatchOpening.program BatchOpening.context BatchOpening.producer
    [.data (toPayload batch)]).run (handler .producer supplied) ⟨[.data (toPayload batch)], preceding, initial⟩

/-- The complete actual producer result, including codec refusal, existing
proof prefix, oracle state, returns, physical frame and observations. -/
theorem produce_equation {S : Type} (batch : Batch) (supplied : BatchOpeningCodec.Context)
    (preceding : List Bytes) (initial : S) :
    produce batch supplied preceding initial =
      match encode supplied (toPayload batch) with
      | none => ⟨.stopped .refused, ⟨[.data (toPayload batch)], preceding, initial⟩, []⟩
      | some output => ⟨.returned ⟨[], [.data (toPayload batch)]⟩,
          ⟨[.data (toPayload batch)], preceding ++ [output], initial⟩, []⟩ := by
  unfold produce
  rw [← payload_agreement]
  erw [BatchOpening.producer_process]
  simp only [PIR.Process.run, handler, PIR.Execution.follow]
  cases encoded : encode supplied (BatchOpening.payload model batch) <;> rfl

theorem produce_encoded {S : Type} (batch : Batch) (bounded : batch.length ≤ maximumOpenings)
    (preceding : List Bytes) (initial : S) :
    produce batch context preceding initial =
      ⟨.returned ⟨[], [.data (toPayload batch)]⟩,
        ⟨[.data (toPayload batch)], preceding ++ [batchCodec.bytes batch], initial⟩, []⟩ := by
  rw [produce_equation, encode_success batch bounded]

/-- One whole validator equation for every peer byte string, including false
decisions. Malformed heads remain unread with the input physical frame. Successful
receives consume exactly one frame and retain both returned data coordinates. -/
theorem validate_equation {S : Type} (point value : Scalar) (supplied : BatchOpeningCodec.Context)
    (proof : List Bytes) (initial : S) :
    validate point value supplied proof initial =
      match proof with
      | [] => ⟨.stopped .refused, ⟨inputs point value, [], initial⟩, []⟩
      | input :: unread =>
          match decodeBatch supplied input with
          | none => ⟨.stopped .refused, ⟨inputs point value, proof, initial⟩, []⟩
          | some batch => ⟨.returned (result point value batch),
              ⟨(result point value batch).environment, unread, initial⟩, []⟩ := by
  unfold validate
  rw [BatchOpeningConnection.validator_equation]
  cases proof with
  | nil => rfl
  | cons input unread =>
      cases decoded : decodeBatch supplied input with
      | none =>
          have decoded' : (decode supplied input >>= (·.value BatchOpening.batchTy)) = none := decoded
          simp only [PIR.Process.run, handler, decoded', PIR.Execution.follow, decoded]
          rfl
      | some batch =>
          have admitted := runtime_admitted batch (decodeBatch_sound decoded).2.1
          have decoded' : (decode supplied input >>= (·.value BatchOpening.batchTy)) = some batch := decoded
          simp only [PIR.Process.run, handler, decoded', PIR.Execution.follow, admitted, ↓reduceIte, decoded]
          rfl

theorem validate_encoded {S : Type} (point value : Scalar) (batch : Batch)
    (bounded : batch.length ≤ maximumOpenings) (unread : List Bytes) (initial : S) :
    validate point value context (batchCodec.bytes batch :: unread) initial =
      ⟨.returned (result point value batch), ⟨(result point value batch).environment, unread, initial⟩, []⟩ := by
  rw [validate_equation]
  have decoded : decodeBatch context (batchCodec.bytes batch) = some batch := by
    rw [decodeBatch_eq, ite_eq_left rfl]
    exact batchCodec.decode_bytes ((batch_admitted batch).2 bounded)
  simp only [decoded]

theorem validate_malformed {S : Type} (point value : Scalar) (supplied : BatchOpeningCodec.Context) (input : Bytes)
    (malformed : decode supplied input = none) (unread : List Bytes) (initial : S) :
    validate point value supplied (input :: unread) initial =
      ⟨.stopped .refused, ⟨inputs point value, input :: unread, initial⟩, []⟩ := by
  rw [validate_equation]
  simp [decodeBatch, malformed]

theorem validate_trailing {S : Type} (point value : Scalar) (batch : Batch)
    (bounded : batch.length ≤ maximumOpenings) (suffix : Bytes) (nonempty : suffix ≠ [])
    (unread : List Bytes) (initial : S) :
    validate point value context ((batchCodec.bytes batch ++ suffix) :: unread) initial =
      ⟨.stopped .refused, ⟨inputs point value, (batchCodec.bytes batch ++ suffix) :: unread, initial⟩, []⟩ := by
  exact validate_malformed _ _ _ _ (trailing_refused batch bounded suffix nonempty) unread initial

/-- Larger batches remain ordinary typed adversary messages. This selected
byte boundary refuses them rather than restricting the source message type. -/
theorem encode_oversized (batch : Batch) (tooLarge : maximumOpenings < batch.length) :
    encode context (toPayload batch) = none := by
  simp only [encode, ↓reduceIte, toPayload, PayloadCodec.encode_pack, Codec.encode]
  exact ite_eq_right (fun admitted => Nat.not_lt_of_ge ((batch_admitted batch).1 admitted) tooLarge)

end ZkcExamples.Construction.BatchOpeningByteConnection
