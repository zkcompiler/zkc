module

public section

/-! Merlin 1.0 transcripts: STROBE-128 over Keccak-f[1600].

The three layers, from their published definitions:

- **Keccak-f[1600]**, the permutation of SHA-3 (FIPS 202): 24 rounds of θ, ρ, π, χ, ι on 25
  lanes of 64 bits; the state is 200 bytes, a lane being eight of them least significant first.
- **STROBE-128** (Hamburg, version 1.0.2), at rate 166: the state starts as the permutation of
  `[1, 168, 1, 0, 1, 96] ‖ "STROBEv1.0.2"` and absorbs its protocol label as metadata. An
  operation starts by absorbing the previous start and its flags; one with the flag `C` or `K`
  runs the permutation first when the position is not 0. `AD` absorbs, `PRF` squeezes, and
  the metadata forms carry the flag `M`; `more` continues the operation that is open.
- **Merlin 1.0**: STROBE-128 with the label `Merlin v1.0`, then the message of the transcript's
  label under `dom-sep`. A message is its label as metadata, its length as four bytes least
  significant first as metadata (continued), and the message as `AD`; a challenge is its label
  and its length as metadata and the bytes of a `PRF`.

A transcript is written as 203 numbers: the 200 bytes of the state, the position, the start
of the current operation and its flags. Reading numbers back is total: missing numbers are
zero, and each number is taken below the range of what it stands for.
-/

set_option autoImplicit false

namespace Zkc.Core.Merlin

/-! ## Keccak-f[1600] -/

def roundConstants : Array UInt64 := #[
  0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
  0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
  0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- The rotation of the lane at `x + 5 y`, for ρ. -/
def rotations : Array UInt64 := #[
  0, 1, 62, 28, 27,
  36, 44, 6, 55, 20,
  3, 10, 43, 25, 39,
  41, 45, 15, 21, 8,
  18, 2, 61, 56, 14]

def rotateLeft (value count : UInt64) : UInt64 := (value <<< count) ||| (value >>> (64 - count))

/-- The permutation on 25 lanes, the lane at `x + 5 y`. -/
def keccakF (lanes : Array UInt64) : Array UInt64 := Id.run do
  let mut a := lanes
  for round in [0:24] do
    -- θ
    let column (x : Nat) : UInt64 := a[x]! ^^^ a[x + 5]! ^^^ a[x + 10]! ^^^ a[x + 15]! ^^^ a[x + 20]!
    let columns := (Array.range 5).map column
    let effect (x : Nat) : UInt64 := columns[(x + 4) % 5]! ^^^ rotateLeft columns[(x + 1) % 5]! 1
    a := a.mapIdx fun index lane => lane ^^^ effect (index % 5)
    -- ρ and π: the lane at (x, y) moves to (y, 2x + 3y), rotated
    let mut b : Array UInt64 := Array.replicate 25 0
    for x in [0:5] do
      for y in [0:5] do
        b := b.set! (y + 5 * ((2 * x + 3 * y) % 5)) (rotateLeft a[x + 5 * y]! rotations[x + 5 * y]!)
    -- χ
    a := (Array.range 25).map fun index =>
      let x := index % 5
      let y := index / 5
      b[index]! ^^^ ((~~~ b[(x + 1) % 5 + 5 * y]!) &&& b[(x + 2) % 5 + 5 * y]!)
    -- ι
    a := a.set! 0 (a[0]! ^^^ roundConstants[round]!)
  return a

/-- The permutation on 200 bytes. -/
def permute (state : ByteArray) : ByteArray := Id.run do
  let lane (index : Nat) : UInt64 :=
    (List.range 8).foldr (fun offset value => (value <<< 8) ||| (state.get! (8 * index + offset)).toUInt64) 0
  let lanes := keccakF ((Array.range 25).map lane)
  let mut out := ByteArray.emptyWithCapacity 200
  for index in [0:25] do
    for offset in [0:8] do
      out := out.push (lanes[index]! >>> (8 * offset).toUInt64).toUInt8
  return out

/-! ## STROBE-128 -/

def rate : Nat := 166

def flagI : Nat := 1
def flagA : Nat := 2
def flagC : Nat := 4
def flagK : Nat := 32
def flagM : Nat := 16

structure Strobe where
  state : ByteArray
  position : Nat
  begun : Nat
  flags : Nat

namespace Strobe

def xorAt (state : ByteArray) (index : Nat) (value : Nat) : ByteArray :=
  state.set! index (state.get! index ^^^ value.toUInt8)

def runF (strobe : Strobe) : Strobe :=
  let state := xorAt strobe.state strobe.position strobe.begun
  let state := xorAt state (strobe.position + 1) 0x04
  let state := xorAt state (rate + 1) 0x80
  { strobe with state := permute state, position := 0, begun := 0 }

def absorb (strobe : Strobe) (data : List Nat) : Strobe :=
  data.foldl (init := strobe) fun strobe byte =>
    let strobe := { strobe with state := xorAt strobe.state strobe.position byte
                                position := strobe.position + 1 }
    if strobe.position == rate then strobe.runF else strobe

def squeeze (strobe : Strobe) (count : Nat) : List Nat × Strobe := Id.run do
  let mut strobe := strobe
  let mut out : Array Nat := #[]
  for _ in [0:count] do
    out := out.push (strobe.state.get! strobe.position).toNat
    strobe := { strobe with state := strobe.state.set! strobe.position 0
                            position := strobe.position + 1 }
    if strobe.position == rate then strobe := strobe.runF
  return (out.toList, strobe)

def beginOperation (strobe : Strobe) (flags : Nat) (more : Bool) : Strobe :=
  if more then strobe
  else
    let previous := strobe.begun
    let strobe := { strobe with begun := strobe.position + 1, flags }
    let strobe := strobe.absorb [previous, flags]
    if flags &&& (flagC ||| flagK) != 0 && strobe.position != 0 then strobe.runF else strobe

def metaAd (strobe : Strobe) (data : List Nat) (more : Bool) : Strobe :=
  (strobe.beginOperation (flagM ||| flagA) more).absorb data

def ad (strobe : Strobe) (data : List Nat) (more : Bool) : Strobe :=
  (strobe.beginOperation flagA more).absorb data

def prf (strobe : Strobe) (count : Nat) (more : Bool) : List Nat × Strobe :=
  (strobe.beginOperation (flagI ||| flagA ||| flagC) more).squeeze count

def initial : ByteArray := Id.run do
  let mut state := ByteArray.mk (Array.replicate 200 0)
  let header := [1, rate + 2, 1, 0, 1, 96] ++ "STROBEv1.0.2".toUTF8.toList.map (·.toNat)
  for (byte, index) in header.zip (List.range header.length) do
    state := state.set! index byte.toUInt8
  return permute state

def new (label : List Nat) : Strobe :=
  ({ state := initial, position := 0, begun := 0, flags := 0 } : Strobe).metaAd label false

end Strobe

/-! ## Merlin 1.0 -/

def bytesOfText (text : String) : List Nat := text.toUTF8.toList.map (·.toNat)

/-- A number as four bytes, least significant first. -/
def u32 (value : Nat) : List Nat := (List.range 4).map fun index => (value >>> (8 * index)) % 256

structure Transcript where
  strobe : Strobe

namespace Transcript

def appendMessage (transcript : Transcript) (label message : List Nat) : Transcript :=
  let strobe := transcript.strobe.metaAd label false
  let strobe := strobe.metaAd (u32 message.length) true
  ⟨strobe.ad message false⟩

def challengeBytes (transcript : Transcript) (label : List Nat) (count : Nat) :
    List Nat × Transcript :=
  let strobe := transcript.strobe.metaAd label false
  let strobe := strobe.metaAd (u32 count) true
  let (bytes, strobe) := strobe.prf count false
  (bytes, ⟨strobe⟩)

/-- A transcript with a label. -/
def new (label : List Nat) : Transcript :=
  appendMessage ⟨Strobe.new (bytesOfText "Merlin v1.0")⟩ (bytesOfText "dom-sep") label

/-- The transcript as 203 numbers. -/
def toNumbers (transcript : Transcript) : List Nat :=
  transcript.strobe.state.toList.map (·.toNat) ++
    [transcript.strobe.position, transcript.strobe.begun, transcript.strobe.flags]

/-- A transcript from numbers: the first 200 are the state's bytes (each modulo 256, zero when
missing), then the position (modulo the rate), the start of the operation and its flags (each
modulo 256). -/
def ofNumbers (numbers : List Nat) : Transcript :=
  let state := ByteArray.mk ((Array.range 200).map fun index => (numbers.getD index 0).toUInt8)
  ⟨{ state, position := numbers.getD 200 0 % rate, begun := numbers.getD 201 0 % 256
     flags := numbers.getD 202 0 % 256 }⟩

end Transcript

end Zkc.Core.Merlin
