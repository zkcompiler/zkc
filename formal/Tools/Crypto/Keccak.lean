import Lean

/-! Executable Keccak-256 reference for finite oracle differential tests.
The lane equations follow the Keccak team specification (1600-bit state,
24 rounds, 1088-bit rate, original Keccak delimiter 0x01). This is a separate,
slow reference implementation, not a cryptographic security theorem or native
provider. See https://keccak.team/keccak_specs_summary.html.
-/
set_option autoImplicit false
namespace Tools.Crypto.Keccak

private def rotate (x : UInt64) (n : Nat) : UInt64 :=
  if n == 0 then x else (x <<< n.toUInt64) ||| (x >>> (64-n).toUInt64)

private def offsets : Array Nat :=
  #[0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39,
    41, 45, 15, 21, 8, 18, 2, 61, 56, 14]
private def constants : Array UInt64 :=
  #[0x0000000000000001, 0x0000000000008082, 0x800000000000808a,
    0x8000000080008000, 0x000000000000808b, 0x0000000080000001,
    0x8000000080008081, 0x8000000000008009, 0x000000000000008a,
    0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
    0x000000008000808b, 0x800000000000008b, 0x8000000000008089,
    0x8000000000008003, 0x8000000000008002, 0x8000000000000080,
    0x000000000000800a, 0x800000008000000a, 0x8000000080008081,
    0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

private def round (state : Array UInt64) (rc : UInt64) : Array UInt64 := Id.run do
  let mut columns : Array UInt64 := Array.replicate 5 0
  for x in [:5] do
    let c := (List.range 5).foldl (fun s y => s ^^^ state[x+5*y]!) 0
    columns := columns.set! x c
  let mut b : Array UInt64 := Array.replicate 25 0
  for x in [:5] do
    let d := columns[(x+4)%5]! ^^^ rotate columns[(x+1)%5]! 1
    for y in [:5] do
      b := b.set! (y+5*((2*x+3*y)%5)) (rotate (state[x+5*y]! ^^^ d) offsets[x+5*y]!)
  let mut out : Array UInt64 := Array.replicate 25 0
  for x in [:5] do
    for y in [:5] do
      out := out.set! (x+5*y) (b[x+5*y]! ^^^ ((~~~b[(x+1)%5+5*y]!) &&& b[(x+2)%5+5*y]!))
  return out.set! 0 (out[0]! ^^^ rc)

private def permutation (state : Array UInt64) : Array UInt64 := constants.foldl round state

/-- Original Keccak-256, not FIPS SHA3-256 (which uses a different delimiter). -/
def hash (input : ByteArray) : ByteArray := Id.run do
  let paddedSize := (input.size / 136 + 1) * 136
  let mut padded := input.push 1
  for _ in [:paddedSize-padded.size] do padded := padded.push 0
  padded := padded.set! (paddedSize-1) (padded[paddedSize-1]! ||| 128)
  let mut state : Array UInt64 := Array.replicate 25 0
  for block in [:paddedSize/136] do
    for lane in [:17] do
      let mut word : UInt64 := 0
      for byte in [:8] do
        word := word ||| (padded[block*136+lane*8+byte]!.toUInt64 <<< (8*byte).toUInt64)
      state := state.set! lane (state[lane]! ^^^ word)
    state := permutation state
  let mut output := ByteArray.empty
  for byte in [:32] do
    output := output.push ((state[byte/8]! >>> (8*(byte%8)).toUInt64).toUInt8)
  return output
end Tools.Crypto.Keccak
