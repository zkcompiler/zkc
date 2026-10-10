import Zkc.Realization.ByteEncoding

/-! Length framing independently of a cryptographic provider. These laws apply
only to the list-byte codec below. Correspondence with the executable ByteArray
cursor or native ingress is a separate obligation, not established here. -/

set_option autoImplicit false

namespace Zkc.Realization.Framing
open ByteEncoding

def frame (payload : Bytes) : Bytes := little 8 payload.length ++ payload

def read (bytes : Bytes) : Option (Bytes × Bytes) :=
  if 8 ≤ bytes.length then
    let length := valueLE (bytes.take 8)
    let rest := bytes.drop 8
    if length ≤ rest.length then some (rest.take length, rest.drop length)
    else none
  else none

theorem frame_length (payload : Bytes) : (frame payload).length = 8 + payload.length := by
  simp [frame]

theorem read_frame_append (payload rest : Bytes) (bound : payload.length < 256^8) :
    read (frame payload ++ rest) = some (payload, rest) := by
  simp only [frame, List.append_assoc, read, List.length_append, little_length]
  simp only [Nat.le_add_right, ↓reduceIte]
  have takeHeader : (little 8 payload.length ++ (payload ++ rest)).take 8 = little 8 payload.length := by
    simp
  have dropHeader : (little 8 payload.length ++ (payload ++ rest)).drop 8 = payload ++ rest := by
    simp
  rw [takeHeader, dropHeader, little_value _ _ bound]
  simp

theorem read_frame (payload : Bytes) (bound : payload.length < 256^8) :
    read (frame payload) = some (payload, []) := by
  simpa using read_frame_append payload [] bound

/-- A frame cannot absorb the next frame's bytes. No delimiter or candidate
supplied type is needed to separate consecutive payloads. -/
theorem read_two (first second rest : Bytes)
    (firstBound : first.length < 256^8) (secondBound : second.length < 256^8) :
    (read (frame first ++ frame second ++ rest)).bind
      (fun (a, remaining) => (read remaining).map fun (b, tail) => (a,b,tail)) =
      some (first,second,rest) := by
  rw [List.append_assoc, read_frame_append _ _ firstBound]
  simp only [Option.bind_some]
  rw [read_frame_append _ _ secondBound]
  rfl

end Zkc.Realization.Framing
