import ZkcExamples.Construction.BatchOpeningByteConnection
import Tests.DataCodec

/-! Controls through the actual constructed Domain participant and its selected
byte handler. The same whole-result theorem handles acceptance and a false
decision. Codec-only refusals reuse the controls at their owning boundary. -/

set_option autoImplicit false

namespace Tests.BatchOpeningByteConnection
open Zkc.Construction Zkc.DataCodec
open ZkcExamples.Construction
open BatchOpeningCodec BatchOpeningByteConnection

def sample : Batch := [opening 2 3, opening 2 3]

/-- These subsequent frames are deliberately malformed. They stay unread. -/
def unread : List Bytes := [[], [255, 0, 1]]

def expected (accepted : Bool) : Domain.Result carriers :=
  ⟨[.data (.boolean accepted), .data (toPayload sample)],
    [.data (.field "koala-bear" 2), .data (.field "koala-bear" 3),
      .data (toPayload sample), .data (.boolean accepted)]⟩

theorem nonempty_accepted :
    validate 2 3 context (batchCodec.bytes sample :: unread) (37 : Nat) =
      ⟨.returned (expected true), ⟨(expected true).environment, unread, 37⟩, []⟩ := by
  rw [validate_encoded _ _ _ (by decide +kernel), result_eq]
  have checked : checkBatch 2 3 sample = true := by decide +kernel
  rw [checked]
  rfl

/-- A false answer is returned with the delivered batch; it is not a stop. -/
theorem nonempty_false :
    validate 2 3 context (batchCodec.bytes [opening 2 4] :: unread) (37 : Nat) =
      ⟨.returned
        ⟨[.data (.boolean false), .data (toPayload [opening 2 4])],
          [.data (.field "koala-bear" 2), .data (.field "koala-bear" 3),
            .data (toPayload [opening 2 4]), .data (.boolean false)]⟩,
        ⟨[.data (.field "koala-bear" 2), .data (.field "koala-bear" 3),
          .data (toPayload [opening 2 4]), .data (.boolean false)], unread, 37⟩, []⟩ := by
  rw [validate_encoded _ _ _ (by decide +kernel), result_eq]
  have checked : checkBatch 2 3 [opening 2 4] = false := by decide +kernel
  rw [checked]

theorem empty_accepted :
    validate 2 3 context (batchCodec.bytes [] :: unread) (37 : Nat) =
      ⟨.returned (result 2 3 []), ⟨(result 2 3 []).environment, unread, 37⟩, []⟩ := by
  exact validate_encoded _ _ _ (by decide +kernel) _ _

theorem maximum_delivered :
    validate 2 3 context (batchCodec.bytes (List.replicate 16 (opening 2 3)) :: unread) (37 : Nat) =
      ⟨.returned (result 2 3 (List.replicate 16 (opening 2 3))),
        ⟨(result 2 3 (List.replicate 16 (opening 2 3))).environment, unread, 37⟩, []⟩ := by
  exact validate_encoded _ _ _ (by decide +kernel) _ _

theorem producer_appends :
    produce sample context unread (37 : Nat) =
      ⟨.returned ⟨[], [.data (toPayload sample)]⟩,
        ⟨[.data (toPayload sample)], unread ++ [batchCodec.bytes sample], 37⟩, []⟩ := by
  exact produce_encoded _ (by decide +kernel) _ _

/-- Producer and validator agree on the exact bytes without an output-only
replacement for either participant's full result. -/
theorem producer_validator_agree (batch : Batch) (bounded : batch.length ≤ maximumOpenings)
    (initial : Nat) :
    produce batch context [] initial =
        ⟨.returned ⟨[], [.data (toPayload batch)]⟩,
          ⟨[.data (toPayload batch)], [batchCodec.bytes batch], initial⟩, []⟩ ∧
      validate 2 3 context [batchCodec.bytes batch] initial =
        ⟨.returned (result 2 3 batch), ⟨(result 2 3 batch).environment, [], initial⟩, []⟩ :=
  ⟨produce_encoded _ bounded _ _, validate_encoded _ _ _ bounded _ _⟩

theorem missing_frame_refused :
    validate 2 3 context [] (37 : Nat) =
      ⟨.stopped .refused, ⟨inputs 2 3, [], 37⟩, []⟩ := by
  rw [validate_equation]

theorem truncated_length_refused :
    validate 2 3 context ([1, 0, 0, 0, 0, 0, 0] :: unread) (37 : Nat) =
      ⟨.stopped .refused, ⟨inputs 2 3, [1, 0, 0, 0, 0, 0, 0] :: unread, 37⟩, []⟩ := by
  exact validate_malformed _ _ _ _ Tests.DataCodec.truncated_length_refused _ _

theorem truncated_record_refused :
    validate 2 3 context ((le64 1 ++ le64 2) :: unread) (37 : Nat) =
      ⟨.stopped .refused, ⟨inputs 2 3, (le64 1 ++ le64 2) :: unread, 37⟩, []⟩ := by
  exact validate_malformed _ _ _ _ Tests.DataCodec.truncated_record_refused _ _

theorem trailing_current_frame_refused :
    validate 2 3 context ((batchCodec.bytes sample ++ [0]) :: unread) (37 : Nat) =
      ⟨.stopped .refused, ⟨inputs 2 3, (batchCodec.bytes sample ++ [0]) :: unread, 37⟩, []⟩ := by
  exact validate_trailing _ _ _ (by decide +kernel) _ (by decide +kernel) _ _

theorem wrong_context_refused :
    validate 2 3 { context with orderedFields := ["value", "point"] }
      (batchCodec.bytes sample :: unread) (37 : Nat) =
      ⟨.stopped .refused, ⟨inputs 2 3, batchCodec.bytes sample :: unread, 37⟩, []⟩ := by
  apply validate_malformed
  apply wrong_context
  decide +kernel

theorem producer_wrong_context_refused :
    produce sample { context with messageSite := "different-site" } unread (37 : Nat) =
      ⟨.stopped .refused, ⟨[.data (toPayload sample)], unread, 37⟩, []⟩ := by
  rw [produce_equation]
  have different : { context with messageSite := "different-site" } ≠ context := by decide +kernel
  simp only [encode, different, ↓reduceIte]

theorem excess_count_refused :
    validate 2 3 context (le64 17 :: unread) (37 : Nat) =
      ⟨.stopped .refused, ⟨inputs 2 3, le64 17 :: unread, 37⟩, []⟩ := by
  exact validate_malformed _ _ _ _ Tests.DataCodec.excess_count_refused _ _

theorem noncanonical_scalar_refused :
    validate 2 3 context ((le64 1 ++ le64 2130706433 ++ le64 0) :: unread) (37 : Nat) =
      ⟨.stopped .refused, ⟨inputs 2 3, (le64 1 ++ le64 2130706433 ++ le64 0) :: unread, 37⟩, []⟩ := by
  exact validate_malformed _ _ _ _ Tests.DataCodec.scalar_modulus_refused _ _

theorem oversized_producer_refused :
    produce (List.replicate 17 (opening 2 3)) context unread (37 : Nat) =
      ⟨.stopped .refused, ⟨[.data (toPayload (List.replicate 17 (opening 2 3)))], unread, 37⟩, []⟩ := by
  rw [produce_equation, encode_oversized _ (by decide +kernel)]

/-- Seventeen elements are still valid for the source helper's finite domain. -/
theorem larger_typed_batch_retained :
    Domain.callHelper model BatchOpening.program BatchOpeningBodies.checkBatchHelper.name [.data .boolean]
      (received 2 3 (List.replicate 17 (opening 2 3))) = .returned [.data (.boolean true)] := by
  have checked := BatchOpeningConnection.helper_equation (G := Scalar) (2 : Scalar) 3
    (List.replicate 17 (opening 2 3))
  have bounded : (List.replicate 17 (opening 2 3)).length < Zkc.Source.Structured.indexLimit := by decide +kernel
  rw [ite_eq_left bounded] at checked
  exact checked

/-- Runtime exhaustion remains a distinct stop in the typed semantics. -/
theorem helper_exhaustion (batch : Batch) (unbounded : ¬batch.length < Zkc.Source.Structured.indexLimit) :
    Domain.callHelper model BatchOpening.program BatchOpeningBodies.checkBatchHelper.name [.data .boolean]
      (received 2 3 batch) = .stopped .exhausted := by
  have checked := BatchOpeningConnection.helper_equation (G := Scalar) (2 : Scalar) 3 batch
  rwa [ite_eq_right unbounded] at checked

theorem wrong_nominal_send_refused :
    handler .producer context
      (.send context.messageSite context.messageSite "role00000001" Tests.DataCodec.wrongProduct)
      (⟨inputs 2 3, unread, 37⟩ : ByteState Nat) =
      ⟨.stopped .refused, ⟨inputs 2 3, unread, 37⟩, []⟩ := by
  simp only [handler, Tests.DataCodec.wrong_product_refused]

theorem wrong_receive_type_refused :
    handler .validator context (.receive .boolean context.messageSite context.messageSite "role00000000")
      (⟨inputs 2 3, batchCodec.bytes sample :: unread, 37⟩ : ByteState Nat) =
      ⟨.stopped .refused, ⟨inputs 2 3, batchCodec.bytes sample :: unread, 37⟩, []⟩ := by
  simp only [handler, roundtrip sample (by decide +kernel)]
  rfl

end Tests.BatchOpeningByteConnection
