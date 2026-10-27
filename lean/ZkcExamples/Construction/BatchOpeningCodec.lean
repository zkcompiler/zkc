module

public import Zkc.DataCodec.Composition
public import Zkc.DataCodec.Payload
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-! Selected interpreted-byte transport for the actual batch-opening fixture's
data layout. Artifact-to-process correspondence is a separate integration hook;
this module proves the codec and typed payload laws, not native execution or
commitment security. In particular these are not ZKCV provider bytes.
-/

set_option autoImplicit false

namespace ZkcExamples.Construction.BatchOpeningCodec
open Zkc.Source.Structured
open Zkc.Construction.Domain (Payload)
open Zkc.DataCodec

abbrev Scalar := ZMod 2130706433

/-- Fixed scalar model. Nominal equality still controls every payload cast,
even though the host field carrier is the same for every identity. -/
abbrev carriers : Carriers := uniformCarriers Scalar Scalar

/-- The same carriers with computable ring/equality operations, ready for the
actual structured helper's interpretation. No group operation is used here. -/
abbrev model : DomainModel := ringModel Scalar Scalar

/-- Exact nominal identity retained by the fixture's typed source export. -/
def openingIdentity : String :=
  "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e67313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]"

abbrev openingTy : Ty :=
  .product openingIdentity "case00000000" (.cons (.field "koala-bear") (.cons (.field "koala-bear") .nil))

abbrev batchTy : Ty := .sequence openingTy

abbrev Opening := carriers.Value openingTy
abbrev Batch := carriers.Value batchTy

def opening (point value : Scalar) : Opening := (point, value, ())

/-- Maximum sixteen openings. Lists outside this bound remain mathematical
values and adversarial payloads; only this transport refuses them. -/
def maximumOpenings : Nat := 16

def scalarCodec : Codec Scalar := Codec.fin 2130706433 (by decide)

def openingCodec : Codec Opening := scalarCodec.pair (scalarCodec.pair Codec.unit)

def batchCodec : Codec Batch := openingCodec.sequence (maximumOpenings + 1) (by decide)

/-- Additional composition client: up to four batches, each up to sixteen
openings. This is distinct from the fixture's single-batch message schema. -/
def nestedBatchCodec : Codec (List Batch) := batchCodec.sequence 5 (by decide)

abbrev payloadCodec : PayloadCodec carriers := ⟨batchTy, rfl, batchCodec⟩

def toPayload (batch : Batch) : Payload carriers := payloadCodec.pack batch

/-- Exact context is supplied out of band and checked by equality. A digest
of this object is not substituted for its identity by these theorems. Field
names retain point/value ordering even though both field sorts coincide. -/
structure Context where
  format : String
  entry : String
  messageSite : String
  producer : Nat
  validator : Nat
  schema : Ty
  orderedFields : List String
  maximumOpenings : Nat
  deriving DecidableEq

def context : Context where
  format := "zkc.interpreted-batch/0"
  entry := "zkl_206d594942dc6f123848ad35c8fcdc7017b483db9ccd5c0651d1ad5c850eceab"
  messageSite := "label_6261746368_0"
  producer := 0
  validator := 1
  schema := batchTy
  orderedFields := ["point", "value"]
  maximumOpenings := maximumOpenings

/-- `none` is the selected codec's single rejection result, covering context,
nominal type, canonical spelling, length and transport-limit failures. -/
def encode (supplied : Context) (payload : Payload carriers) : Option Bytes :=
  if supplied = context then payloadCodec.encode payload else none

def decode (supplied : Context) (input : Bytes) : Option (Payload carriers) :=
  if supplied = context then payloadCodec.decode input else none

theorem opening_admitted (value : Opening) : openingCodec.admitted value := by
  exact ⟨trivial, trivial, trivial⟩

theorem batch_admitted (batch : Batch) : batchCodec.admitted batch ↔ batch.length ≤ maximumOpenings := by
  change (batch.length < maximumOpenings + 1 ∧ ∀ value ∈ batch, openingCodec.admitted value) ↔ _
  simp only [opening_admitted, implies_true, and_true, Nat.lt_succ_iff]

theorem encode_success (batch : Batch) (bounded : batch.length ≤ maximumOpenings) :
    encode context (toPayload batch) = some (batchCodec.bytes batch) := by
  simp only [encode, ↓reduceIte, toPayload]
  exact payloadCodec.encode_success ((batch_admitted batch).2 bounded)

theorem roundtrip (batch : Batch) (bounded : batch.length ≤ maximumOpenings) :
    decode context (batchCodec.bytes batch) = some (toPayload batch) := by
  simp only [decode, ↓reduceIte, toPayload]
  exact payloadCodec.decode_bytes ((batch_admitted batch).2 bounded)

theorem canonical {input : Bytes} {payload : Payload carriers}
    (decoded : decode context input = some payload) : encode context payload = some input := by
  simpa [encode, decode] using payloadCodec.encode_decode (by simpa [decode] using decoded)

theorem decode_encode {input : Bytes} {payload : Payload carriers}
    (encoded : encode context payload = some input) : decode context input = some payload := by
  simpa [decode] using payloadCodec.decode_encode (by simpa [encode] using encoded)

theorem trailing_refused (batch : Batch) (bounded : batch.length ≤ maximumOpenings)
    (suffix : Bytes) (nonempty : suffix ≠ []) :
    decode context (batchCodec.bytes batch ++ suffix) = none := by
  simp only [decode, ↓reduceIte]
  exact payloadCodec.trailing_refused ((batch_admitted batch).2 bounded) suffix nonempty

theorem wrong_context (supplied : Context) (different : supplied ≠ context) (input : Bytes) :
    decode supplied input = none := by simp [decode, different]

theorem wrong_nominal (payload : Payload carriers) (different : payload.ty ≠ batchTy) :
    encode context payload = none := by
  simp only [encode, ↓reduceIte]
  exact payloadCodec.wrong_type payload different

/-- Intended point/value decision after the typed receive. Integration with
the actual compiled helper must establish this observation equation. -/
def checkBatch (point value : Scalar) (batch : Batch) : Bool :=
  batch.all fun record => record.1 == point && record.2.1 == value

def receive (point value : Scalar) (payload : Payload carriers) : Option (Bool × Batch) := do
  let batch ← payload.value batchTy
  some (checkBatch point value batch, batch)

def receiveBytes (point value : Scalar) (supplied : Context) (input : Bytes) : Option (Bool × Batch) :=
  decode supplied input >>= receive point value

/-- Codec success delivers exactly the typed payload and its point/value
decision. No relation-validity premise is imposed on the transmitted batch. -/
theorem delivered (point value : Scalar) (batch : Batch) (bounded : batch.length ≤ maximumOpenings) :
    receiveBytes point value context (batchCodec.bytes batch) = some (checkBatch point value batch, batch) := by
  simp [receiveBytes, roundtrip batch bounded, receive, toPayload, payloadCodec,
    PayloadCodec.pack, Payload.value]

theorem checkBatch_true_iff (point value : Scalar) (batch : Batch) :
    checkBatch point value batch = true ↔ ∀ record ∈ batch, record.1 = point ∧ record.2.1 = value := by
  simp [checkBatch]

theorem opening_bytes_length (value : Opening) : (openingCodec.bytes value).length = 16 := by
  simp [openingCodec, scalarCodec, Codec.pair, Codec.fin, Codec.unit, Zkc.Construction.le64_length]

theorem batch_bytes_length (batch : Batch) :
    (batchCodec.bytes batch).length = 8 + 16 * batch.length := by
  change (Zkc.Construction.le64 batch.length ++ batch.flatMap openingCodec.bytes).length = _
  induction batch with
  | nil => simp [Zkc.Construction.le64_length]
  | cons value tail ih =>
    simp only [List.length_append, Zkc.Construction.le64_length] at ih ⊢
    simp only [List.flatMap_cons, List.length_append, opening_bytes_length, List.length_cons]
    omega

/-- Accepted complete messages have at most 264 bytes, derived from the
proved canonical spelling and the element limit, not from finite tests. -/
theorem accepted_size {input : Bytes} {payload : Payload carriers}
    (decoded : decode context input = some payload) : input.length ≤ 264 := by
  have parsed : payloadCodec.decode input = some payload := by simpa [decode] using decoded
  change (batchCodec.decode input).map payloadCodec.pack = some payload at parsed
  obtain ⟨batch, actual, _⟩ := Option.map_eq_some_iff.mp parsed
  obtain ⟨admitted, rfl⟩ := batchCodec.decode_sound actual
  have := (batch_admitted batch).1 admitted
  rw [batch_bytes_length]
  simp only [maximumOpenings] at this
  omega

end ZkcExamples.Construction.BatchOpeningCodec
