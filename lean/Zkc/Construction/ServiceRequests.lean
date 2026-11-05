module

public import Zkc.Construction.Participant
public import Zkc.Source.Structured.DomainModels

@[expose] public section

/-! One public bounded decoded service contract. Raw ideal replies use finite
carriers. Source services may be adversarial and are checked separately; neither
this decoder nor its exact laws identify native provider bytes. -/
set_option autoImplicit false
namespace Zkc.Construction.Request
open Zkc.Source

/-- Invalid zero bounds have one inert raw reply so the generic total oracle
signature still has a finite nonempty carrier at every key. Formation refuses
that request before any query; for every positive bound this is exactly bound. -/
def replyBound (bound : Nat) : Nat := max bound 1

theorem replyBound_positive (bound : Nat) : 0 < replyBound bound :=
  Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_right bound 1)

theorem replyBound_of_positive {bound : Nat} (positive : 0 < bound) :
    replyBound bound = bound := Nat.max_eq_left positive

abbrev Raw (carriers : Structured.Carriers) (request : Request) : Type :=
  match request.sort with
  | .field field => carriers.Field field
  | .index => Fin (replyBound (request.operands.headD 0))
  | .indices => Fin (request.operands[1]?.getD 0) → Fin (replyBound (request.operands.headD 0))
  | _ => Unit

def decode {carriers : Structured.Carriers} (request : Request) :
    Raw carriers request → Option (carriers.Value request.sort) :=
  match request with
  | ⟨_, _, .field _⟩ => some
  | ⟨_, _, .index⟩ => fun value => some value.val
  | ⟨_, _, .indices⟩ => fun values => some (List.ofFn fun i => (values i).val)
  | ⟨_, _, _⟩ => fun _ => none

def accepts {carriers : Structured.Carriers} (request : Request)
    (value : carriers.Value request.sort) : Bool :=
  request.valid && match request.sort, value with
    | .field _, _ => true
    | .index, index => index < request.operands.headD 0
    | .indices, indices => indices.length == request.operands[1]?.getD 0 &&
        indices.all (· < request.operands.headD 0)
    | _, _ => false

theorem decode_index {carriers : Structured.Carriers} (bound : Nat) (value : Fin (replyBound bound)) :
    decode (carriers := carriers) (.sampleIndex bound) value = some value.val := rfl

theorem decode_block {carriers : Structured.Carriers} (bound count : Nat)
    (values : Fin count → Fin (replyBound bound)) :
    decode (carriers := carriers) (.sampleIndices bound count) values =
      some (List.ofFn fun i => (values i).val) := rfl

theorem decoded_block_count (bound count : Nat) (values : Fin count → Fin (replyBound bound)) :
    (List.ofFn fun i => (values i).val).length = count := List.length_ofFn

theorem decoded_block_bounded (bound count : Nat) (positive : 0 < bound)
    (values : Fin count → Fin (replyBound bound)) :
    ∀ value ∈ List.ofFn (fun i => (values i).val), value < bound := by
  intro value member
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
  simpa only [replyBound_of_positive positive] using (values i).isLt

end Zkc.Construction.Request
