module

public import Zkc.Construction.Encoding
public import Mathlib.Logic.Equiv.Defs

@[expose] public section

/-! Executable partial codecs for selected finite data.

The parser consumes a prefix. Its two laws quantify arbitrary raw input and
arbitrary suffixes; they support composition without assuming honest input.
The complete decoder accepts only an empty suffix. `bytes` is an internal
spelling function; `encode` is the partial public operation, with an explicit
admitted domain. This module makes no native provider correspondence claim.
-/

set_option autoImplicit false

namespace Zkc.DataCodec

abbrev Bytes := List UInt8

structure Codec (α : Type) where
  admitted : α → Prop
  decidableAdmitted : DecidablePred admitted
  bytes : α → Bytes
  parse : Bytes → Option (α × Bytes)
  parse_bytes : ∀ a, admitted a → ∀ rest, parse (bytes a ++ rest) = some (a, rest)
  parse_sound : ∀ input a rest, parse input = some (a, rest) →
    admitted a ∧ input = bytes a ++ rest

namespace Codec
variable {α β : Type}

instance (codec : Codec α) : DecidablePred codec.admitted := codec.decidableAdmitted

def encode (codec : Codec α) (value : α) : Option Bytes :=
  if codec.admitted value then some (codec.bytes value) else none

def decode (codec : Codec α) (input : Bytes) : Option α := do
  let (value, rest) ← codec.parse input
  if rest = [] then some value else none

theorem encode_success (codec : Codec α) {value : α} (admitted : codec.admitted value) :
    codec.encode value = some (codec.bytes value) := by simp [encode, admitted]

theorem encode_isSome (codec : Codec α) (value : α) :
    (codec.encode value).isSome = decide (codec.admitted value) := by
  simp only [encode]; split <;> simp_all

theorem decode_bytes (codec : Codec α) {value : α} (admitted : codec.admitted value) :
    codec.decode (codec.bytes value) = some value := by
  simpa [decode] using congrArg
    (fun parsed => parsed >>= fun (value, rest) => if rest = [] then some value else none)
    (codec.parse_bytes value admitted [])

theorem decode_encode (codec : Codec α) {value : α} {input : Bytes}
    (encoded : codec.encode value = some input) : codec.decode input = some value := by
  unfold encode at encoded
  split at encoded
  · cases Option.some.inj encoded
    exact codec.decode_bytes (by assumption)
  · cases encoded

theorem decode_sound (codec : Codec α) {input : Bytes} {value : α}
    (decoded : codec.decode input = some value) :
    codec.admitted value ∧ input = codec.bytes value := by
  unfold decode at decoded
  cases parsed : codec.parse input with
  | none => simp [parsed] at decoded
  | some result =>
    rcases result with ⟨actual, rest⟩
    simp only [parsed, bind, Option.bind] at decoded
    split at decoded
    · rename_i empty
      cases Option.some.inj decoded
      simpa [empty] using codec.parse_sound input value rest parsed
    · cases decoded

/-- Every accepted byte string has exactly the encoder's spelling. -/
theorem encode_decode (codec : Codec α) {input : Bytes} {value : α}
    (decoded : codec.decode input = some value) : codec.encode value = some input := by
  obtain ⟨admitted, rfl⟩ := codec.decode_sound decoded
  exact codec.encode_success admitted

theorem bytes_injective (codec : Codec α) {first second : α}
    (admittedFirst : codec.admitted first) (admittedSecond : codec.admitted second)
    (same : codec.bytes first = codec.bytes second) : first = second := by
  have := codec.decode_bytes admittedFirst
  rw [same, codec.decode_bytes admittedSecond] at this
  exact Option.some.inj this.symm

/-- Prefix separation is preserved under composition, including the suffix. -/
theorem prefix_injective (codec : Codec α) {first second : α}
    (admittedFirst : codec.admitted first) (admittedSecond : codec.admitted second)
    (firstRest secondRest : Bytes)
    (same : codec.bytes first ++ firstRest = codec.bytes second ++ secondRest) :
    first = second ∧ firstRest = secondRest := by
  have parsed := codec.parse_bytes first admittedFirst firstRest
  rw [same, codec.parse_bytes second admittedSecond secondRest] at parsed
  exact Prod.mk.inj (Option.some.inj parsed.symm)

/-- A complete value cannot be followed by even one unread byte. -/
theorem trailing_refused (codec : Codec α) {value : α} (admitted : codec.admitted value)
    (rest : Bytes) (nonempty : rest ≠ []) :
    codec.decode (codec.bytes value ++ rest) = none := by
  simp [decode, codec.parse_bytes value admitted rest, nonempty]

/-- Transport a codec along an explicit, computable equivalence. -/
def equiv (codec : Codec α) (equivalence : α ≃ β) : Codec β where
  admitted value := codec.admitted (equivalence.symm value)
  decidableAdmitted := fun _ => inferInstance
  bytes value := codec.bytes (equivalence.symm value)
  parse input := codec.parse input |>.map fun (value, rest) => (equivalence value, rest)
  parse_bytes value admitted rest := by
    simp [codec.parse_bytes _ admitted rest]
  parse_sound input value rest parsed := by
    cases original : codec.parse input with
    | none => simp [original] at parsed
    | some result =>
      rcases result with ⟨actual, suffix⟩
      simp only [original, Option.map_some, Option.some.injEq, Prod.mk.injEq] at parsed
      obtain ⟨rfl, rfl⟩ := parsed
      simpa using codec.parse_sound input actual suffix original

/-- Empty product terminator; its empty spelling is safe inside counted data. -/
def unit : Codec Unit where
  admitted _ := True
  decidableAdmitted := fun _ => isTrue trivial
  bytes _ := []
  parse input := some ((), input)
  parse_bytes _ _ _ := rfl
  parse_sound _ value _ parsed := by cases value; simpa using parsed

def pair (left : Codec α) (right : Codec β) : Codec (α × β) where
  admitted value := left.admitted value.1 ∧ right.admitted value.2
  decidableAdmitted := fun _ => inferInstance
  bytes value := left.bytes value.1 ++ right.bytes value.2
  parse input := do
    let (first, middle) ← left.parse input
    let (second, rest) ← right.parse middle
    some ((first, second), rest)
  parse_bytes value admitted rest := by
    simp [List.append_assoc, left.parse_bytes _ admitted.1, right.parse_bytes _ admitted.2]
  parse_sound input value rest parsed := by
    cases firstParse : left.parse input with
    | none => simp [firstParse] at parsed
    | some first =>
      rcases first with ⟨first, middle⟩
      cases secondParse : right.parse middle with
      | none => simp [firstParse, secondParse] at parsed
      | some second =>
        rcases second with ⟨second, suffix⟩
        simp [firstParse, secondParse] at parsed
        obtain ⟨rfl, rfl⟩ := parsed
        obtain ⟨firstAdmitted, inputEq⟩ := left.parse_sound _ _ _ firstParse
        obtain ⟨secondAdmitted, middleEq⟩ := right.parse_sound _ _ _ secondParse
        exact ⟨⟨firstAdmitted, secondAdmitted⟩, by simp [inputEq, middleEq, List.append_assoc]⟩

end Codec
end Zkc.DataCodec
