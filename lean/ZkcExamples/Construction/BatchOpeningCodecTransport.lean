module

public import ZkcExamples.Construction.BatchOpeningCodec

@[expose] public section

/-! An interpreted-byte realization of the selected one-message client.
Wire events retain the exact context. This is a mathematical handler, not an
implementation of the native ZKCV protocol or a native compiler theorem.
-/

set_option autoImplicit false

namespace ZkcExamples.Construction.BatchOpeningCodecTransport
open Zkc
open Zkc.Source.Structured
open Zkc.Construction.Domain (Payload)
open Zkc.DataCodec
open BatchOpeningCodec

inductive WireAction where
  | send (context : Context) (site : String) (receiver : Nat) (bytes : Bytes)
  | receive (context : Context) (site : String) (sender : Nat)

def wireInterface : PIR.Signature where
  Op := WireAction
  Reply
    | .send .. => Unit
    | .receive .. => Bytes

/-- Encode the actual sent value and decode the actual received bytes. Every
malformed input remains available to the wire peer and produces refusal.
Other nominal schemas and service queries also refuse explicitly. -/
def transport (supplied : Context) :
    PIR.OperationInterpretation (participantInterfaceOn carriers) wireInterface
  | .send (ty := ty) site receiver value =>
    match Payload.ofValue ty value >>= encode supplied with
    | none => .halt .refused
    | some bytes => .call (.send supplied site receiver bytes) .done
  | .receive ty site sender =>
    .call (.receive supplied site sender) fun input =>
      match decode supplied input >>= (·.value ty) with
      | none => .halt .refused
      | some value => .done value
  | .query .. => .halt .refused

/-- Artifact hook: the actual producer must have this selected send behavior. -/
def producer (batch : Batch) : PIR.Process (participantInterfaceOn carriers) Unit :=
  .call (.send (ty := batchTy) context.messageSite context.validator batch) .done

/-- Artifact hook: the actual validator must have this receive and helper
observation, including its returned decision and delivered batch. -/
def validator (point value : Scalar) : PIR.Process (participantInterfaceOn carriers) (Bool × Batch) :=
  .call (.receive batchTy context.messageSite context.producer) fun batch =>
    .done (checkBatch point value batch, batch)

def outcome (point value : Scalar) (supplied : Context) (input : Bytes) : PIR.Outcome (Bool × Batch) :=
  match receiveBytes point value supplied input with
  | none => .stopped .refused
  | some result => .returned result

theorem producer_bytes (batch : Batch) (bounded : batch.length ≤ maximumOpenings) :
    (producer batch).interpret (transport context) =
      .call (.send context context.messageSite context.validator (batchCodec.bytes batch)) .done := by
  have encoded : (Payload.ofValue batchTy batch >>= encode context) = some (batchCodec.bytes batch) := by
    have packaged : Payload.ofValue batchTy batch = some (toPayload batch) := rfl
    rw [packaged]
    simp only [bind, Option.bind]
    exact encode_success batch bounded
  simp only [producer, PIR.Process.interpret, transport, encoded, PIR.Process.bind]
  rfl

/-- Equality for all peer bytes, including malformed and excessive encodings.
The only outcome change introduced by decoding is the explicit refusal. -/
theorem validator_bytes (point value : Scalar) (supplied : Context) :
    (validator point value).interpret (transport supplied) =
      .call (.receive supplied context.messageSite context.producer) fun input =>
        match outcome point value supplied input with
        | .returned result => .done result
        | .stopped reason => .halt reason := by
  simp only [validator, PIR.Process.interpret, transport, PIR.Process.bind]
  congr 1
  funext input
  simp only [outcome, receiveBytes]
  cases decoded : decode supplied input with
  | none => rfl
  | some payload =>
    cases read : payload.value batchTy with
    | none => simp [receive, read, PIR.Process.bind]
    | some batch => simp [receive, read, PIR.Process.bind]

theorem received_encoded (point value : Scalar) (batch : Batch) (bounded : batch.length ≤ maximumOpenings) :
    outcome point value context (batchCodec.bytes batch) = .returned (checkBatch point value batch, batch) := by
  simp [outcome, delivered point value batch bounded]

theorem received_malformed (point value : Scalar) (supplied : Context) (input : Bytes)
    (refused : decode supplied input = none) : outcome point value supplied input = .stopped .refused := by
  simp [outcome, receiveBytes, refused]

theorem received_trailing (point value : Scalar) (batch : Batch) (bounded : batch.length ≤ maximumOpenings)
    (suffix : Bytes) (nonempty : suffix ≠ []) :
    outcome point value context (batchCodec.bytes batch ++ suffix) = .stopped .refused := by
  exact received_malformed _ _ _ _ (trailing_refused batch bounded suffix nonempty)

end ZkcExamples.Construction.BatchOpeningCodecTransport
