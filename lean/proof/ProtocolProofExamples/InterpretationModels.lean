module

public import ProtocolProof.Components.Interpretation

/-!
# Reusing a decoder component in distinct contexts

The mathematical bit service and the word transport have different answer types.
One local law installs the decoder for arbitrary finite clients. Invalid words
terminate with refusal while retaining the consumed state and observation.
These are complete deterministic models, not claims about a compiled protocol.
-/

@[expose] public section

namespace ProtocolProofExamples.InterpretationModels
open PIR ProtocolProof

abbrev Bits : Signature := ⟨Unit, fun _ ↦ Bool⟩
abbrev Words : Signature := ⟨Unit, fun _ ↦ Nat⟩

/-- The mathematical service explicitly includes malformed encodings in its contract. -/
def bitService : Handler Bits (List Nat) Nat
  | _, [] => ⟨.stopped .exhausted, [], []⟩
  | _, word :: rest =>
      if word < 2 then ⟨.returned (word == 1), rest, [word]⟩
      else ⟨.stopped .refused, rest, [word]⟩

def wordService : Handler Words (List Nat) Nat
  | _, [] => ⟨.stopped .exhausted, [], []⟩
  | _, word :: rest => ⟨.returned word, rest, [word]⟩

def decode : OperationInterpretation Bits Words := fun _ ↦
  .call () fun word ↦ if word < 2 then .done (word == 1) else .halt .refused

def view (word : Nat) : List Nat := [word]

/-- This is the only local representation proof, reused by every following client. -/
theorem decoder : InterpretationContract decode bitService wordService Eq view view where
  operation op s t same := by
    subst t
    cases s with
    | nil => exact ⟨rfl, rfl, rfl⟩
    | cons word rest =>
      by_cases valid : word < 2 <;>
        constructor <;> simp [bitService, wordService, decode, Process.run,
          Execution.follow, valid]

/-- An adaptive second request uses the first decoded bit. -/
def adaptive : Process Bits Bool :=
  .call () fun first ↦ if first then .call () fun second ↦ .done (!second)
    else .done false

/-- A structurally different client nests arbitrary-length finite batches. -/
def batches (outer inner : Nat) : Process Bits Nat :=
  (List.range outer).foldlM (fun count _ ↦
    (List.range inner).foldlM (fun count _ ↦
      .call () fun bit ↦ .done (count + if bit then 1 else 0)) count) 0

theorem adaptive_installed (initial : List Nat) :
    Related Eq view view (adaptive.run bitService initial)
      ((adaptive.interpret decode).run wordService initial) := decoder.run adaptive _ _ rfl

theorem batches_installed (outer inner : Nat) (initial : List Nat) :
    Related Eq view view ((batches outer inner).run bitService initial)
      (((batches outer inner).interpret decode).run wordService initial) :=
  decoder.run (batches outer inner) _ _ rfl

/-- An implementation can itself be installed in another layer without revisiting the caller. -/
theorem composed_decoder :
    InterpretationContract (fun op ↦ (decode op).interpret (fun op ↦ .call op .done))
      bitService wordService (fun s u ↦ ∃ t, s = t ∧ t = u) view view :=
  decoder.comp (InterpretationContract.identity wordService view)

theorem malformed_keeps_consumed_state_and_events :
    ((batches 2 2).interpret decode).run wordService [1, 2, 0] =
      ⟨.stopped .refused, [0], [1, 2]⟩ := rfl

theorem adaptive_complete :
    (adaptive.interpret decode).run wordService [1, 0, 7] =
      ⟨.returned true, [7], [1, 0]⟩ := rfl

/-- Accepting malformed input cannot satisfy the component's fixed local meaning. -/
def unchecked : OperationInterpretation Bits Words := fun _ ↦
  .call () fun word ↦ .done (word == 1)

theorem unchecked_refused :
    ¬ InterpretationContract unchecked bitService wordService Eq view view := by
  intro alleged
  have same := (alleged.operation () [2] [2] rfl).outcome
  cases same

/-- Removing a reached observable event is also detected, even when answers agree. -/
def eraseEventService (op : Unit) (state : List Nat) : Execution (List Nat) Nat Nat :=
  { wordService op state with events := [] }

theorem event_erasure_refused :
    ¬ InterpretationContract decode bitService eraseEventService Eq view view := by
  intro alleged
  have same := (alleged.operation () [1] [1] rfl).events
  cases same

end ProtocolProofExamples.InterpretationModels
