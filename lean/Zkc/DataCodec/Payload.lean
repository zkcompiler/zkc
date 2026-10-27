module

public import Zkc.DataCodec
public import Zkc.Construction.DomainTranscript

@[expose] public section

set_option autoImplicit false

namespace Zkc.DataCodec
open Zkc.Source.Structured
open Zkc.Construction.Domain (Payload)

/-- One codec for one exact nominal data sort, over the existing carriers.
The surrounding deployment must bind this exact schema and codec selection. -/
structure PayloadCodec (carriers : Carriers) where
  ty : Ty
  dataOnly : ty.isService = false
  codec : Codec (carriers.Value ty)

namespace PayloadCodec
variable {carriers : Carriers}

def pack (selected : PayloadCodec carriers) (value : carriers.Value selected.ty) : Payload carriers :=
  ⟨selected.ty, selected.dataOnly, value⟩

def encode (selected : PayloadCodec carriers) (payload : Payload carriers) : Option Bytes :=
  payload.value selected.ty >>= selected.codec.encode

def decode (selected : PayloadCodec carriers) (input : Bytes) : Option (Payload carriers) :=
  selected.codec.decode input |>.map selected.pack

@[simp] theorem value_pack (selected : PayloadCodec carriers) (value : carriers.Value selected.ty) :
    (selected.pack value).value selected.ty = some value := by simp [pack, Payload.value]

theorem encode_pack (selected : PayloadCodec carriers) (value : carriers.Value selected.ty) :
    selected.encode (selected.pack value) = selected.codec.encode value := by
  simp [encode]

theorem encode_success (selected : PayloadCodec carriers) {value : carriers.Value selected.ty}
    (admitted : selected.codec.admitted value) :
    selected.encode (selected.pack value) = some (selected.codec.bytes value) := by
  rw [selected.encode_pack]
  exact selected.codec.encode_success admitted

theorem decode_bytes (selected : PayloadCodec carriers) {value : carriers.Value selected.ty}
    (admitted : selected.codec.admitted value) :
    selected.decode (selected.codec.bytes value) = some (selected.pack value) := by
  simp [decode, selected.codec.decode_bytes admitted]

/-- Canonicality applies to every successful raw-byte decode. -/
theorem encode_decode (selected : PayloadCodec carriers) {input : Bytes} {payload : Payload carriers}
    (decoded : selected.decode input = some payload) : selected.encode payload = some input := by
  unfold decode at decoded
  cases actual : selected.codec.decode input with
  | none => simp [actual] at decoded
  | some value =>
    simp only [actual, Option.map_some, Option.some.injEq] at decoded
    subst payload
    rw [selected.encode_pack]
    exact selected.codec.encode_decode actual

theorem decode_encode (selected : PayloadCodec carriers) {input : Bytes} {payload : Payload carriers}
    (encoded : selected.encode payload = some input) : selected.decode input = some payload := by
  unfold encode at encoded
  cases read : payload.value selected.ty with
  | none => simp [read] at encoded
  | some value =>
    simp only [read, bind, Option.bind] at encoded
    have packed : selected.pack value = payload := by
      have := Payload.ofValue_value read
      simpa [Payload.ofValue, selected.dataOnly, pack] using this
    simp [decode, selected.codec.decode_encode encoded, packed]

theorem wrong_type (selected : PayloadCodec carriers) (payload : Payload carriers)
    (different : payload.ty ≠ selected.ty) : selected.encode payload = none := by
  simp [encode, Payload.value_wrong_type different]

theorem trailing_refused (selected : PayloadCodec carriers) {value : carriers.Value selected.ty}
    (admitted : selected.codec.admitted value) (rest : Bytes) (nonempty : rest ≠ []) :
    selected.decode (selected.codec.bytes value ++ rest) = none := by
  simp [decode, selected.codec.trailing_refused admitted rest nonempty]

end PayloadCodec
end Zkc.DataCodec
