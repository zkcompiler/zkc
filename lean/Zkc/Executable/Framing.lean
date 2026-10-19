module

public import Zkc.Executable.Lowering

@[expose] public section

/-! Proof bytes an honest producer writes.

An honest producer frames every message: an eight-byte little-endian length,
then the message's encoding (`frame`). Its proof bytes are the framing magic,
the expected invocation binding and the framed messages (`proofBytes`). When the
host's decoder inverts the producer's encoder at each receive type and every
encoding fits in one proof, the decoded proof of those bytes is the producer's
messages (`decodeProof_frames`), and the framing header is the expected one
(`proofBytes_header`, `proofBytes_body`). These are the codec and size premises
of an executable completeness theorem.
-/

set_option autoImplicit false

namespace Zkc.Executable
open Zkc.Construction

variable {F G : Type}

/-- A count's little-endian bytes. -/
def lengthBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | count + 1, value => UInt8.ofNat (value % 256) :: lengthBytes count (value / 256)

theorem lengthBytes_length : ∀ (count value : Nat), (lengthBytes count value).length = count
  | 0, _ => rfl
  | count + 1, value => by simp [lengthBytes, lengthBytes_length count]

theorem littleEndian_lengthBytes : ∀ (count value : Nat),
    littleEndian (lengthBytes count value) = value % 256 ^ count
  | 0, value => by simp [lengthBytes, littleEndian, Nat.mod_one]
  | count + 1, value => by
      rw [lengthBytes, littleEndian, littleEndian_lengthBytes count, UInt8.toNat_ofNat',
        show (2 : Nat) ^ 8 = 256 by rfl, Nat.mod_mod, pow_succ', Nat.mod_mul]

/-- One length-framed message: its eight-byte little-endian length, then its
bytes. -/
def frame (payload : List UInt8) : List UInt8 := lengthBytes 8 payload.length ++ payload

theorem readFrame_frame (payload rest : List UInt8) (short : payload.length ≤ proofLimit) :
    readFrame (frame payload ++ rest) = some (payload, rest) := by
  have small : payload.length < 256 ^ 8 := lt_of_le_of_lt short (by decide)
  have lengthEq : littleEndian (lengthBytes 8 payload.length) = payload.length := by
    rw [littleEndian_lengthBytes, Nat.mod_eq_of_lt small]
  unfold readFrame
  simp [lengthEq, frame, lengthBytes_length, short]

/-- The framed messages of a proof, each encoded at its receive type. -/
def frames (encode : PhysicalType → Payload F G → List UInt8) : List PhysicalType → Proof F G → List UInt8
  | type :: types, payload :: payloads => frame (encode type payload) ++ frames encode types payloads
  | _, _ => []

/-- When the decoder inverts the encoder at every receive type and every
encoding fits in one proof, the framed messages decode to the messages. -/
theorem decodeProof_frames (decode : PhysicalType → List UInt8 → Option (Payload F G))
    (encode : PhysicalType → Payload F G → List UInt8)
    (roundtrip : ∀ type payload, decode type (encode type payload) = some payload)
    (bounded : ∀ type payload, (encode type payload).length ≤ proofLimit) :
    ∀ (types : List PhysicalType) (payloads : Proof F G), types.length = payloads.length →
      decodeProof decode types (frames encode types payloads) = payloads
  | [], [], _ => rfl
  | [], _ :: _, length => by simp at length
  | _ :: _, [], length => by simp at length
  | type :: types, payload :: payloads, length => by
      simp only [frames, decodeProof, readFrame_frame _ _ (bounded type payload), roundtrip,
        decodeProof_frames decode encode roundtrip bounded types payloads (by simpa using length)]

/-- The proof bytes an honest producer writes: the framing magic, the expected
binding and the framed messages. -/
def proofBytes (encode : PhysicalType → Payload F G → List UInt8) (binding : List UInt8)
    (types : List PhysicalType) (payloads : Proof F G) : List UInt8 :=
  magic ++ binding ++ frames encode types payloads

theorem proofBytes_header (encode : PhysicalType → Payload F G → List UInt8) {binding : List UInt8}
    (bindingLength : binding.length = 32) (types : List PhysicalType) (payloads : Proof F G) :
    (proofBytes encode binding types payloads).take 40 = magic ++ binding := by
  have magicLength : magic.length = 8 := rfl
  simp [proofBytes, List.take_append, magicLength, bindingLength, List.take_of_length_le]

theorem proofBytes_body (encode : PhysicalType → Payload F G → List UInt8) {binding : List UInt8}
    (bindingLength : binding.length = 32) (types : List PhysicalType) (payloads : Proof F G) :
    (proofBytes encode binding types payloads).drop 40 = frames encode types payloads := by
  have magicLength : magic.length = 8 := rfl
  simp [proofBytes, List.drop_append, magicLength, bindingLength]

end Zkc.Executable
