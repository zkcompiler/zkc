module

public import Zkc.DataCodec

@[expose] public section

set_option autoImplicit false

namespace Zkc.DataCodec
open Zkc.Construction (le64 ofLe64 le64_length ofLe64_le64)
namespace Codec
variable {α : Type}

/-- An exclusive natural bound, explicitly fitting the eight-byte spelling.
The re-encoding check makes canonical acceptance explicit in the algorithm. -/
def boundedNat (limit : Nat) (fits : limit ≤ 2 ^ 64) : Codec Nat where
  admitted value := value < limit
  decidableAdmitted := fun _ => inferInstance
  bytes := le64
  parse input :=
    if 8 ≤ input.length then
      let value := ofLe64 (input.take 8)
      if value < limit ∧ le64 value = input.take 8 then some (value, input.drop 8) else none
    else none
  parse_bytes value admitted rest := by
    have bound : value < 2 ^ 64 := Nat.lt_of_lt_of_le admitted fits
    simp [le64_length, List.take_left' (le64_length value),
      List.drop_left' (le64_length value), ofLe64_le64 value bound, admitted]
  parse_sound input value rest parsed := by
    split at parsed
    · dsimp only at parsed
      split at parsed
      · rename_i canonical
        cases Option.some.inj parsed
        exact ⟨canonical.1, by rw [canonical.2]; exact (List.take_append_drop 8 input).symm⟩
      · cases parsed
    · cases parsed

/-- A canonical finite scalar/index. Values are never reduced modulo `limit`
by the decoder. A spelling at or above the limit is adversarial and refused. -/
def fin (limit : Nat) (fits : limit ≤ 2 ^ 64) : Codec (Fin limit) where
  admitted _ := True
  decidableAdmitted := fun _ => isTrue trivial
  bytes value := le64 value.val
  parse input := do
    let (value, rest) ← (boundedNat limit fits).parse input
    if bound : value < limit then some (⟨value, bound⟩, rest) else none
  parse_bytes value _ rest := by
    have parsed : (boundedNat limit fits).parse (le64 value.val ++ rest) =
        some (value.val, rest) := (boundedNat limit fits).parse_bytes value.val value.isLt rest
    simp [parsed, value.isLt]
  parse_sound input value rest parsed := by
    cases original : (boundedNat limit fits).parse input with
    | none => simp [original] at parsed
    | some result =>
      rcases result with ⟨actual, suffix⟩
      simp only [original, bind, Option.bind] at parsed
      split at parsed
      · cases Option.some.inj parsed
        exact ⟨trivial, ((boundedNat limit fits).parse_sound _ _ _ original).2⟩
      · cases parsed

theorem boundedNat_truncated (limit : Nat) (fits : limit ≤ 2 ^ 64) (input : Bytes)
    (short : input.length < 8) : (boundedNat limit fits).parse input = none := by
  simp [boundedNat, Nat.not_le_of_lt short]

/-- An excessive count/scalar refuses, regardless of whether its body is
truncated, well formed or contains extra adversarial data. -/
theorem boundedNat_out_of_range (limit : Nat) (fits : limit ≤ 2 ^ 64)
    (value : Nat) (wordBound : value < 2 ^ 64) (outside : limit ≤ value) (rest : Bytes) :
    (boundedNat limit fits).parse (le64 value ++ rest) = none := by
  simp [boundedNat, le64_length, List.take_left' (le64_length value),
    ofLe64_le64 value wordBound, Nat.not_lt_of_ge outside]

theorem fin_out_of_range (limit : Nat) (fits : limit ≤ 2 ^ 64)
    (value : Nat) (wordBound : value < 2 ^ 64) (outside : limit ≤ value) (rest : Bytes) :
    (fin limit fits).parse (le64 value ++ rest) = none := by
  simp [fin, boundedNat_out_of_range limit fits value wordBound outside rest]

/-- Parse exactly `count` elements, including zero-byte element codecs. The
recursion is on the already bounded count, never on a chosen inverse. -/
def parseCount (codec : Codec α) : Nat → Bytes → Option (List α × Bytes)
  | 0, input => some ([], input)
  | count + 1, input => do
      let (value, middle) ← codec.parse input
      let (values, rest) ← parseCount codec count middle
      some (value :: values, rest)

theorem parseCount_bytes (codec : Codec α) (values : List α)
    (admitted : ∀ value ∈ values, codec.admitted value) (rest : Bytes) :
    parseCount codec values.length (values.flatMap codec.bytes ++ rest) = some (values, rest) := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, parseCount]
    rw [codec.parse_bytes value (admitted value (by simp))]
    simp [ih (fun item member => admitted item (by simp [member]))]

theorem parseCount_sound (codec : Codec α) (count : Nat) (input : Bytes)
    (values : List α) (rest : Bytes) (parsed : parseCount codec count input = some (values, rest)) :
    values.length = count ∧ (∀ value ∈ values, codec.admitted value) ∧
      input = values.flatMap codec.bytes ++ rest := by
  induction count generalizing input values rest with
  | zero =>
    simp only [parseCount, Option.some.injEq, Prod.mk.injEq] at parsed
    obtain ⟨rfl, rfl⟩ := parsed
    simp
  | succ count ih =>
    simp only [parseCount] at parsed
    cases firstParse : codec.parse input with
    | none => simp [firstParse] at parsed
    | some result =>
      rcases result with ⟨value, middle⟩
      cases remaining : parseCount codec count middle with
      | none => simp [firstParse, remaining] at parsed
      | some result =>
        rcases result with ⟨tail, suffix⟩
        simp [firstParse, remaining] at parsed
        obtain ⟨rfl, rfl⟩ := parsed
        obtain ⟨headAdmitted, inputEq⟩ := codec.parse_sound _ _ _ firstParse
        obtain ⟨lengthEq, tailAdmitted, middleEq⟩ := ih _ _ _ remaining
        exact ⟨by simp [lengthEq], by simpa using And.intro headAdmitted tailAdmitted,
          by simp [inputEq, middleEq, List.append_assoc]⟩

/-- Eight-byte element-count framing followed by the ordered element spellings.
Mathematical lists remain unbounded; this selected transport admits fewer than
`limit` elements. The bound is checked before recursing over peer input. -/
def sequence (codec : Codec α) (limit : Nat) (fits : limit ≤ 2 ^ 64) : Codec (List α) where
  admitted values := values.length < limit ∧ ∀ value ∈ values, codec.admitted value
  decidableAdmitted := fun _ => inferInstance
  bytes values := le64 values.length ++ values.flatMap codec.bytes
  parse input := do
    let (count, middle) ← (boundedNat limit fits).parse input
    parseCount codec count middle
  parse_bytes values admitted rest := by
    simp only [List.append_assoc]
    have header : (boundedNat limit fits).parse
        (le64 values.length ++ (values.flatMap codec.bytes ++ rest)) =
        some (values.length, values.flatMap codec.bytes ++ rest) :=
      (boundedNat limit fits).parse_bytes values.length admitted.1 _
    simp [header, parseCount_bytes codec values admitted.2 rest]
  parse_sound input values rest parsed := by
    cases header : (boundedNat limit fits).parse input with
    | none => simp [header] at parsed
    | some result =>
      rcases result with ⟨count, middle⟩
      simp only [header, bind, Option.bind] at parsed
      obtain ⟨countAdmitted, inputEq⟩ := (boundedNat limit fits).parse_sound _ _ _ header
      change count < limit at countAdmitted
      change input = le64 count ++ middle at inputEq
      obtain ⟨lengthEq, valuesAdmitted, middleEq⟩ := parseCount_sound codec _ _ _ _ parsed
      exact ⟨⟨by simpa [lengthEq] using countAdmitted, valuesAdmitted⟩,
        by simpa [lengthEq, List.append_assoc] using inputEq.trans (congrArg (le64 count ++ ·) middleEq)⟩

end Codec
end Zkc.DataCodec
