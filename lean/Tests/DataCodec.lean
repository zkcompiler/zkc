import ZkcExamples.Construction.BatchOpeningCodecTransport

/-! Controls for the selected interpreted-byte codec. General roundtrip,
canonicality and prefix separation are proved in the codec owners; these
controls exercise concrete successful values and each selected refusal. -/

namespace Tests.DataCodec
open Zkc.DataCodec
open Zkc.Source.Structured
open Zkc.Construction.Domain (Payload)
open ZkcExamples.Construction.BatchOpeningCodec
open ZkcExamples.Construction.BatchOpeningCodecTransport
open Zkc.Construction (le64)

def sample : Batch := [opening 2 3, opening 2 3]

theorem exact_spelling : batchCodec.encode [opening 2 3] =
    some [1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem delivered_true : receiveBytes 2 3 context (batchCodec.bytes sample) = some (true, sample) := by
  decide +kernel

theorem delivered_false : receiveBytes 2 4 context (batchCodec.bytes sample) = some (false, sample) := by
  decide +kernel

theorem empty_delivered : receiveBytes 2 3 context (le64 0) = some (true, []) := by
  decide +kernel

/-- Structural transport does not exclude batches that fail the relation. -/
theorem invalid_claim_still_encodes : (encode context (toPayload [opening 2 4])).isSome = true := by
  decide +kernel

theorem maximum_encodes : (encode context (toPayload (List.replicate 16 (opening 0 0)))).isSome = true := by
  decide +kernel

theorem excess_encode_refused : encode context (toPayload (List.replicate 17 (opening 0 0))) = none := by
  decide +kernel

/-- The excessive declared count refuses before requiring its body. -/
theorem excess_count_refused : decode context (le64 17) = none := by
  decide +kernel

theorem huge_count_refused : decode context (le64 (2 ^ 64 - 1)) = none := by
  decide +kernel

theorem empty_length_refused : decode context [] = none := by decide +kernel

theorem truncated_length_refused : decode context [1, 0, 0, 0, 0, 0, 0] = none := by
  decide +kernel

theorem truncated_record_refused : decode context (le64 1 ++ le64 2) = none := by
  decide +kernel

theorem trailing_byte_refused : decode context (batchCodec.bytes sample ++ [0]) = none := by
  exact trailing_refused sample (by decide) [0] (by decide)

theorem canonical_scalar_maximum : (scalarCodec.encode (2130706432 : Scalar)).isSome = true := by
  decide +kernel

theorem scalar_modulus_refused : decode context (le64 1 ++ le64 2130706433 ++ le64 0) = none := by
  decide +kernel

theorem scalar_largest_word_refused : decode context (le64 1 ++ le64 (2 ^ 64 - 1) ++ le64 0) = none := by
  decide +kernel

theorem reordered_context_refused :
    decode { context with orderedFields := ["value", "point"] } (batchCodec.bytes sample) = none := by
  apply wrong_context
  decide +kernel

theorem changed_limit_context_refused :
    decode { context with maximumOpenings := 17 } (batchCodec.bytes sample) = none := by
  apply wrong_context
  decide +kernel

theorem changed_application_refused :
    decode { context with entry := "different-entry" } (batchCodec.bytes sample) = none := by
  apply wrong_context
  decide +kernel

theorem reordered_data_distinct (point value : Scalar) (different : point ≠ value) :
    openingCodec.bytes (opening point value) ≠ openingCodec.bytes (opening value point) := by
  intro same
  have equal := openingCodec.bytes_injective (opening_admitted _) (opening_admitted _) same
  exact different (congrArg Prod.fst equal)

def wrongProduct : Payload carriers :=
  ⟨.sequence (.product "other-opening" "case00000000"
    (.cons (.field "koala-bear") (.cons (.field "koala-bear") .nil))), rfl, [(2, 3, ())]⟩

theorem wrong_product_refused : encode context wrongProduct = none := by
  apply wrong_nominal
  decide +kernel

def wrongConstructor : Payload carriers :=
  ⟨.sequence (.product openingIdentity "other-case"
    (.cons (.field "koala-bear") (.cons (.field "koala-bear") .nil))), rfl, []⟩

theorem wrong_constructor_empty_refused : encode context wrongConstructor = none := by
  apply wrong_nominal
  decide +kernel

def wrongField : Payload carriers :=
  ⟨.sequence (.product openingIdentity "case00000000"
    (.cons (.field "other-field") (.cons (.field "koala-bear") .nil))), rfl, [(2, 3, ())]⟩

theorem wrong_field_refused : encode context wrongField = none := by
  apply wrong_nominal
  decide +kernel

def scalarSequence : PayloadCodec carriers :=
  ⟨.sequence (.field "koala-bear"), rfl, scalarCodec.sequence 17 (by decide)⟩

theorem empty_vector_is_not_sequence :
    scalarSequence.encode (Payload.vector "koala-bear" []) = none := by
  apply PayloadCodec.wrong_type
  decide +kernel

theorem vector_is_not_sequence :
    scalarSequence.encode (Payload.vector "koala-bear" [2, 3]) = none := by
  apply PayloadCodec.wrong_type
  decide +kernel

theorem nested_roundtrip :
    nestedBatchCodec.decode (nestedBatchCodec.bytes [[], sample]) = some [[], sample] := by
  apply Codec.decode_bytes
  decide +kernel

theorem nested_inner_limit_refused :
    nestedBatchCodec.encode [List.replicate 17 (opening 0 0)] = none := by
  decide +kernel

theorem nested_outer_limit_refused : nestedBatchCodec.encode [[], [], [], [], []] = none := by
  decide +kernel

/-- Zero-byte elements still use and obey the sequence's element count. -/
theorem zero_byte_elements :
    (Codec.unit.sequence 3 (by decide)).decode (le64 2) = some [(), ()] := by
  decide +kernel

theorem process_delivery : outcome 2 3 context (batchCodec.bytes sample) = .returned (true, sample) := by
  have decision : checkBatch 2 3 sample = true := by decide +kernel
  simpa only [decision] using received_encoded 2 3 sample (by decide)

theorem process_excess_count_refused : outcome 2 3 context (le64 17) = .stopped .refused := by
  exact received_malformed _ _ _ _ excess_count_refused

theorem process_wrong_context_refused :
    outcome 2 3 { context with orderedFields := ["value", "point"] } (batchCodec.bytes sample) =
      .stopped .refused := by
  exact received_malformed _ _ _ _ reordered_context_refused

end Tests.DataCodec
