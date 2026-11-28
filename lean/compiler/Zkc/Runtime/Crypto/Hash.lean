module

public import Zkc.Runtime.Crypto.Fields

@[expose] public section
set_option autoImplicit false

/-!
Cryptographic hash functions, XOFs, and algebraic permutations for `ZkcRuntime`:
- SHA-256 (FIPS 180-4)
- Unified Keccak-f[1600] supporting 24 rounds (Keccak-256, SHAKE128, SHAKE256, STROBE-128)
  and 12 rounds (TurboSHAKE128, `draft-irtf-cfrg-fiat-shamir-04`)
- Poseidon2 over KoalaBear (`t = 16`, rate `8`, capacity `8`, S-box `x^3`, `R_F = 8`, `R_P = 20`)
-/

namespace Zkc.Runtime.Crypto

/-! ## SHA-256 (FIPS 180-4) -/

namespace Sha256

def roundConstants : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

def initialState : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

def rotateRight (word count : UInt32) : UInt32 :=
  (word >>> count) ||| (word <<< (32 - count))

def padded (message : ByteArray) : ByteArray := Id.run do
  let mut out := message.push 0x80
  while out.size % 64 != 56 do
    out := out.push 0
  let bits := message.size * 8
  for index in [0:8] do
    out := out.push (UInt8.ofNat ((bits >>> (8 * (7 - index))) % 256))
  return out

def compress (state : Array UInt32) (block : ByteArray) (offset : Nat) : Array UInt32 := Id.run do
  let mut schedule : Array UInt32 := Array.replicate 64 0
  for index in [0:16] do
    let word := (block[offset + 4 * index]!.toUInt32 <<< 24) |||
      (block[offset + 4 * index + 1]!.toUInt32 <<< 16) |||
      (block[offset + 4 * index + 2]!.toUInt32 <<< 8) |||
      block[offset + 4 * index + 3]!.toUInt32
    schedule := schedule.set! index word
  for index in [16:64] do
    let early := schedule[index - 15]!
    let late := schedule[index - 2]!
    let small := rotateRight early 7 ^^^ rotateRight early 18 ^^^ (early >>> 3)
    let large := rotateRight late 17 ^^^ rotateRight late 19 ^^^ (late >>> 10)
    schedule := schedule.set! index (schedule[index - 16]! + small + schedule[index - 7]! + large)
  let mut a := state[0]!
  let mut b := state[1]!
  let mut c := state[2]!
  let mut d := state[3]!
  let mut e := state[4]!
  let mut f := state[5]!
  let mut g := state[6]!
  let mut h := state[7]!
  for index in [0:64] do
    let sum1 := rotateRight e 6 ^^^ rotateRight e 11 ^^^ rotateRight e 25
    let choice := (e &&& f) ^^^ ((~~~e) &&& g)
    let first := h + sum1 + choice + roundConstants[index]! + schedule[index]!
    let sum0 := rotateRight a 2 ^^^ rotateRight a 13 ^^^ rotateRight a 22
    let majority := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let second := sum0 + majority
    h := g; g := f; f := e; e := d + first
    d := c; c := b; b := a; a := first + second
  return #[state[0]! + a, state[1]! + b, state[2]! + c, state[3]! + d,
           state[4]! + e, state[5]! + f, state[6]! + g, state[7]! + h]

def digest (message : ByteArray) : ByteArray := Id.run do
  let block := padded message
  let mut state := initialState
  for index in [0:block.size / 64] do
    state := compress state block (64 * index)
  let mut out := ByteArray.emptyWithCapacity 32
  for word in state do
    out := out.push (word >>> 24).toUInt8
    out := out.push (word >>> 16).toUInt8
    out := out.push (word >>> 8).toUInt8
    out := out.push word.toUInt8
  return out

end Sha256

/-- SHA-256 returning 32 canonical byte naturals (`< 256`). -/
def sha256Bytes (msg : List Nat) : List Nat :=
  let raw := ofByteArray (Sha256.digest (toByteArray msg))
  (List.range 32).map fun i => raw.getD i 0 % 256

/-! ## Unified Keccak-f[1600] (24-round and 12-round) -/

namespace Keccak

def roundConstants : Array UInt64 := #[
  0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
  0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
  0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

def rotations : Array UInt64 := #[
  0,  1, 62, 28, 27,
  36, 44,  6, 55, 20,
  3, 10, 43, 25, 39,
  41, 45, 15, 21,  8,
  18,  2, 61, 56, 14]

def rotateLeft (value count : UInt64) : UInt64 :=
  if count == 0 then value else (value <<< count) ||| (value >>> (64 - count))

/-- Keccak-p[1600, rounds] on 25 64-bit lanes (using the last `rounds` round constants). -/
def keccakP (lanes : Array UInt64) (rounds : Nat := 24) : Array UInt64 := Id.run do
  let mut a := lanes
  let startRound := 24 - min rounds 24
  for round in [startRound:24] do
    -- θ
    let mut c : Array UInt64 := Array.replicate 5 0
    for x in [0:5] do
      c := c.set! x (a[x]! ^^^ a[x + 5]! ^^^ a[x + 10]! ^^^ a[x + 15]! ^^^ a[x + 20]!)
    let mut d : Array UInt64 := Array.replicate 5 0
    for x in [0:5] do
      d := d.set! x (c[(x + 4) % 5]! ^^^ rotateLeft c[(x + 1) % 5]! 1)
    for i in [0:25] do
      a := a.set! i (a[i]! ^^^ d[i % 5]!)
    -- ρ and π
    let mut b : Array UInt64 := Array.replicate 25 0
    for x in [0:5] do
      for y in [0:5] do
        b := b.set! (y + 5 * ((2 * x + 3 * y) % 5))
          (rotateLeft a[x + 5 * y]! rotations[x + 5 * y]!)
    -- χ
    for i in [0:25] do
      let x := i % 5
      let y := i / 5
      a := a.set! i (b[i]! ^^^ ((~~~ b[(x + 1) % 5 + 5 * y]!) &&& b[(x + 2) % 5 + 5 * y]!))
    -- ι
    a := a.set! 0 (a[0]! ^^^ roundConstants[round]!)
  return a

/-- Keccak-p[1600, rounds] on a 200-byte state. -/
def permute (state : ByteArray) (rounds : Nat := 24) : ByteArray := Id.run do
  let mut lanes : Array UInt64 := Array.replicate 25 0
  for index in [0:25] do
    let mut lane : UInt64 := 0
    for offset in [0:8] do
      lane := lane ||| ((state.get! (8 * index + offset)).toUInt64 <<< (8 * offset).toUInt64)
    lanes := lanes.set! index lane
  let outLanes := keccakP lanes rounds
  let mut out := ByteArray.emptyWithCapacity 200
  for index in [0:25] do
    let lane := outLanes[index]!
    for offset in [0:8] do
      out := out.push (lane >>> (8 * offset).toUInt64).toUInt8
  return out

/-- Sponge construction over Keccak-p[1600, rounds] with given `rate` and domain-separation `suffix`. -/
def sponge (rate : Nat) (suffix : UInt8) (rounds : Nat) (message : ByteArray) (outLen : Nat) :
    ByteArray := Id.run do
  let rate := if rate == 0 then 168 else rate
  let mut padded := message.push suffix
  let rem := padded.size % rate
  let zeros := if rem == 0 then 0 else rate - rem
  for _ in [0:zeros] do
    padded := padded.push 0
  let last := padded.size - 1
  padded := padded.set! last (padded.get! last ^^^ 0x80)
  let mut state := ByteArray.mk (Array.replicate 200 0)
  let blocks := padded.size / rate
  for blk in [0:blocks] do
    let base := blk * rate
    for j in [0:rate] do
      state := state.set! j (state.get! j ^^^ padded.get! (base + j))
    state := permute state rounds
  let mut out := ByteArray.emptyWithCapacity outLen
  let mut emitted := 0
  while emitted < outLen do
    let take := min rate (outLen - emitted)
    for j in [0:take] do
      out := out.push (state.get! j)
    emitted := emitted + take
    if emitted < outLen then
      state := permute state rounds
  return out

end Keccak

/-- Keccak-256 (Ethereum / original Keccak padding `0x01`, rate 136, 24 rounds, 32 bytes). -/
def keccak256 (msg : ByteArray) : ByteArray :=
  Keccak.sponge 136 0x01 24 msg 32

/-- SHAKE128 (FIPS 202 padding `0x1F`, rate 168, 24 rounds). -/
def shake128 (msg : ByteArray) (outLen : Nat) : ByteArray :=
  Keccak.sponge 168 0x1F 24 msg outLen

/-- SHAKE256 (FIPS 202 padding `0x1F`, rate 136, 24 rounds). -/
def shake256 (msg : ByteArray) (outLen : Nat) : ByteArray :=
  Keccak.sponge 136 0x1F 24 msg outLen

/-- TurboSHAKE128 (`draft-irtf-cfrg-fiat-shamir-04`: padding `0x1F`, rate 168, 12 rounds). -/
def turboShake128 (msg : ByteArray) (outLen : Nat) : ByteArray :=
  Keccak.sponge 168 0x1F 12 msg outLen

/-- Byte-list wrapper for Keccak-256 (always length 32, every entry `< 256`). -/
def keccak256Bytes (msg : List Nat) : List Nat :=
  let raw := ofByteArray (keccak256 (toByteArray msg))
  (List.range 32).map fun i => raw.getD i 0 % 256

/-- Byte-list wrapper for SHAKE128 (always length `count`, every entry `< 256`). -/
def shake128Bytes (msg : List Nat) (count : Nat) : List Nat :=
  let raw := ofByteArray (shake128 (toByteArray msg) count)
  (List.range count).map fun i => raw.getD i 0 % 256

/-- Byte-list wrapper for SHAKE256 (always length `count`, every entry `< 256`). -/
def shake256Bytes (msg : List Nat) (count : Nat) : List Nat :=
  let raw := ofByteArray (shake256 (toByteArray msg) count)
  (List.range count).map fun i => raw.getD i 0 % 256

/-- Byte-list wrapper for TurboSHAKE128 (always length `count`, every entry `< 256`). -/
def turboShake128Bytes (msg : List Nat) (count : Nat) : List Nat :=
  let raw := ofByteArray (turboShake128 (toByteArray msg) count)
  (List.range count).map fun i => raw.getD i 0 % 256

theorem sha256Bytes_len_and_bytes (msg : List Nat) :
    (sha256Bytes msg).length = 32 ∧ ∀ b ∈ sha256Bytes msg, b < 256 := by
  refine ⟨by simp [sha256Bytes], ?_⟩
  intro b hb
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hb
  omega

theorem keccak256Bytes_len_and_bytes (msg : List Nat) :
    (keccak256Bytes msg).length = 32 ∧ ∀ b ∈ keccak256Bytes msg, b < 256 := by
  refine ⟨by simp [keccak256Bytes], ?_⟩
  intro b hb
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hb
  omega

theorem shake128Bytes_len_and_bytes (msg : List Nat) (n : Nat) :
    (shake128Bytes msg n).length = n ∧ ∀ b ∈ shake128Bytes msg n, b < 256 := by
  refine ⟨by simp [shake128Bytes], ?_⟩
  intro b hb
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hb
  omega

theorem shake256Bytes_len_and_bytes (msg : List Nat) (n : Nat) :
    (shake256Bytes msg n).length = n ∧ ∀ b ∈ shake256Bytes msg n, b < 256 := by
  refine ⟨by simp [shake256Bytes], ?_⟩
  intro b hb
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hb
  omega

/-! ## Poseidon2 over KoalaBear (width 16, rate 8, capacity 8, S-box `x^3`) -/

namespace Poseidon2KoalaBear

def width : Nat := 16
def rate : Nat := 8
def fullHalf : Nat := 4
def partialRounds : Nat := 20

/-- S-box `x ↦ x^3 mod p` (bijective over KoalaBear since `gcd(3, p - 1) = 1`). -/
def sbox (x : Nat) : Nat :=
  let p := koalaBearOrder
  let x := x % p
  let x2 := (x * x) % p
  (x2 * x) % p

/-- External linear layer: Poseidon2 4x4 circulant matrix `M4` per 4-lane chunk plus cross-chunk sum. -/
def externalLinear (state : Array Nat) : Array Nat := Id.run do
  let p := koalaBearOrder
  let mut st := state
  for chunk in [0:4] do
    let base := 4 * chunk
    let x0 := st[base]! % p; let x1 := st[base + 1]! % p
    let x2 := st[base + 2]! % p; let x3 := st[base + 3]! % p
    let t01 := (x0 + x1) % p
    let t23 := (x2 + x3) % p
    let t0123 := (t01 + t23) % p
    let t01123 := (t0123 + x1) % p
    let t01233 := (t0123 + x3) % p
    let y3 := (t01233 + 2 * x0) % p
    let y1 := (t01123 + 2 * x2) % p
    let y0 := (t01123 + t01) % p
    let y2 := (t01233 + t23) % p
    st := st.set! base y0 |>.set! (base + 1) y1 |>.set! (base + 2) y2 |>.set! (base + 3) y3
  let mut sums : Array Nat := Array.replicate 4 0
  for j in [0:4] do
    let s := (st[j]! + st[j + 4]! + st[j + 8]! + st[j + 12]!) % p
    sums := sums.set! j s
  for i in [0:16] do
    st := st.set! i ((st[i]! + sums[i % 4]!) % p)
  return st

/-- Diagonal entries `diag[i]` for the internal linear layer `x_i ↦ diag[i] * x_i + ∑ x_j`. -/
def internalDiag : Array Nat :=
  #[koalaBearOrder - 2, 1, 2, 1065353217, 3, 4, koalaBearOrder - 1065353217, koalaBearOrder - 3,
    koalaBearOrder - 4, 8, 16, 32, 64, 128, 256, 512]

/-- Internal linear layer: `state[i] ← (internalDiag[i] * state[i] + sum) mod p`. -/
def internalLinear (state : Array Nat) : Array Nat := Id.run do
  let p := koalaBearOrder
  let mut total := 0
  for i in [0:16] do
    total := (total + state[i]!) % p
  let mut st := state
  for i in [0:16] do
    st := st.set! i ((internalDiag[i]! * st[i]! + total) % p)
  return st

/-- Deterministic round constants derived once from SHAKE128 over domain
`"zkc.poseidon2.koala-bear.w16.r8.p20/0"`. -/
def roundConstants : Array Nat := Id.run do
  let total := 2 * fullHalf * width + partialRounds
  let raw := shake128 "zkc.poseidon2.koala-bear.w16.r8.p20/0".toUTF8 (total * 8)
  let mut out : Array Nat := Array.emptyWithCapacity total
  for i in [0:total] do
    let mut v := 0
    for b in [0:8] do
      v := v + (raw.get! (8 * i + b)).toNat * (256 ^ b)
    out := out.push (v % koalaBearOrder)
  return out

/-- Full Poseidon2-KoalaBear width-16 permutation. -/
def permute (input : Array Nat) : Array Nat := Id.run do
  let p := koalaBearOrder
  let mut st : Array Nat := (Array.range width).map fun i => input.getD i 0 % p
  st := externalLinear st
  let mut rcIdx := 0
  -- First R_F / 2 external rounds
  for _ in [0:fullHalf] do
    for i in [0:width] do
      st := st.set! i (sbox ((st[i]! + roundConstants[rcIdx + i]!) % p))
    rcIdx := rcIdx + width
    st := externalLinear st
  -- R_P internal rounds
  for _ in [0:partialRounds] do
    st := st.set! 0 (sbox ((st[0]! + roundConstants[rcIdx]!) % p))
    rcIdx := rcIdx + 1
    st := internalLinear st
  -- Second R_F / 2 external rounds
  for _ in [0:fullHalf] do
    for i in [0:width] do
      st := st.set! i (sbox ((st[i]! + roundConstants[rcIdx + i]!) % p))
    rcIdx := rcIdx + width
    st := externalLinear st
  return st

end Poseidon2KoalaBear

end Zkc.Runtime.Crypto
