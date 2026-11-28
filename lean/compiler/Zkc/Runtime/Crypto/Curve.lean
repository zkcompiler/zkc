module

public import Zkc.Runtime.Crypto.Fields

@[expose] public section
set_option autoImplicit false

/-!
Concrete BLS12-381 `G1` elliptic-curve arithmetic (`y^2 = x^3 + 4` over `Fq`) with:
- Fast Jacobian projective doubling, addition, and scalar multiplication (`g1Scale`)
- Affine point addition, negation, subtraction, on-curve test, and prime-order subgroup check (`g1InGroup`)
- ZCash 48-byte compressed serialization (`compressG1` / `decompressG1`,
  `draft-irtf-cfrg-pairing-friendly-curves-11`, Appendix C)
- Deterministic subgroup sampling from random bytes (`g1OfScalar`)
-/

namespace Zkc.Runtime.Crypto

/-- Affine point of BLS12-381 `G1`; `none` is the point at infinity `O`. -/
abbrev G1Point := Option (Nat × Nat)

/-- Canonical generator `G` of BLS12-381 `G1`. -/
def g1Generator : G1Point :=
  some (0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb,
        0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1)

/-- Whether a point lies on the curve `y^2 = x^3 + 4` over `Fq`. -/
def g1OnCurve : G1Point → Bool
  | none => true
  | some (x, y) =>
      let q := bls12381FqOrder
      x < q && y < q && (y * y) % q == (x * x % q * x + 4) % q

/-- Negation of a `G1` point. -/
def g1Neg : G1Point → G1Point
  | none => none
  | some (x, y) => some (x % bls12381FqOrder, negMod y bls12381FqOrder)

/-! ## Jacobian coordinates `(X, Y, Z)` for fast scalar multiplication -/

/-- Jacobian point `(X, Y, Z)` with `Z = 0` representing infinity. -/
abbrev G1Jac := Nat × Nat × Nat

def g1JacInfinity : G1Jac := (0, 1, 0)

def g1ToJac : G1Point → G1Jac
  | none => g1JacInfinity
  | some (x, y) => (x % bls12381FqOrder, y % bls12381FqOrder, 1)

def g1OfJac : G1Jac → G1Point
  | (x, y, z) =>
      let q := bls12381FqOrder
      if z % q == 0 then none
      else
        let zInv := modInv z q
        let zInv2 := (zInv * zInv) % q
        let zInv3 := (zInv2 * zInv) % q
        some ((x * zInv2) % q, (y * zInv3) % q)

/-- Jacobian doubling for `a = 0` (`y^2 = x^3 + 4`, EFD `dbl-2009-l`). -/
def g1JacDouble : G1Jac → G1Jac
  | (x1, y1, z1) =>
      let q := bls12381FqOrder
      if z1 == 0 || y1 == 0 then g1JacInfinity
      else
        let a := (x1 * x1) % q
        let b := (y1 * y1) % q
        let c := (b * b) % q
        let xb := (x1 + b) % q
        let d := (2 * subMod (subMod ((xb * xb) % q) a q) c q) % q
        let e := (3 * a) % q
        let f := (e * e) % q
        let x3 := subMod f ((2 * d) % q) q
        let y3 := subMod ((e * subMod d x3 q) % q) ((8 * c) % q) q
        let z3 := (2 * y1 % q * z1) % q
        (x3, y3, z3)

/-- Jacobian addition (EFD `add-2007-bl`). -/
def g1JacAdd (p1 p2 : G1Jac) : G1Jac :=
  let (x1, y1, z1) := p1
  let (x2, y2, z2) := p2
  let q := bls12381FqOrder
  if z1 == 0 then p2
  else if z2 == 0 then p1
  else
    let z1z1 := (z1 * z1) % q
    let z2z2 := (z2 * z2) % q
    let u1 := (x1 * z2z2) % q
    let u2 := (x2 * z1z1) % q
    let s1 := (y1 * z2 % q * z2z2) % q
    let s2 := (y2 * z1 % q * z1z1) % q
    if u1 == u2 then
      if s1 == s2 then g1JacDouble p1 else g1JacInfinity
    else
      let h := subMod u2 u1 q
      let twoH := (2 * h) % q
      let i := (twoH * twoH) % q
      let j := (h * i) % q
      let r := (2 * subMod s2 s1 q) % q
      let v := (u1 * i) % q
      let x3 := subMod (subMod ((r * r) % q) j q) ((2 * v) % q) q
      let y3 := subMod ((r * subMod v x3 q) % q) ((2 * s1 % q * j) % q) q
      let zz := (z1 + z2) % q
      let z3 := (subMod (subMod ((zz * zz) % q) z1z1 q) z2z2 q * h) % q
      (x3, y3, z3)

/-- Scalar multiplication in Jacobian coordinates (binary double-and-add). -/
def g1JacScale (p : G1Jac) (scalar : Nat) : G1Jac :=
  if scalar == 0 then g1JacInfinity
  else go (scalar.log2 + 1) p scalar g1JacInfinity
where
  go : Nat → G1Jac → Nat → G1Jac → G1Jac
    | 0, _, _, acc => acc
    | steps + 1, cur, rem, acc =>
        let acc' := if rem % 2 == 1 then g1JacAdd acc cur else acc
        go steps (g1JacDouble cur) (rem / 2) acc'

/-- Affine addition on BLS12-381 `G1`. -/
def g1Add : G1Point → G1Point → G1Point
  | none, q => q
  | p, none => p
  | some (x1, y1), some (x2, y2) =>
      let q := bls12381FqOrder
      if x1 == x2 && (y1 + y2) % q == 0 then none
      else
        let slope :=
          if x1 == x2 then (3 * x1 % q * x1 % q * modInv ((2 * y1) % q) q) % q
          else (subMod y2 y1 q * modInv (subMod x2 x1 q) q) % q
        let x3 := subMod (subMod ((slope * slope) % q) x1 q) x2 q
        let y3 := subMod ((slope * subMod x1 x3 q) % q) y1 q
        some (x3, y3)

/-- Affine subtraction on BLS12-381 `G1`. -/
def g1Sub (p q : G1Point) : G1Point := g1Add p (g1Neg q)

/-- Scalar multiplication on BLS12-381 `G1` via Jacobian coordinates (1 inversion total). -/
def g1Scale (p : G1Point) (scalar : Nat) : G1Point :=
  let s := scalar % bls12381FrOrder
  if s == 0 then none else g1OfJac (g1JacScale (g1ToJac p) s)

/-- Prime-order subgroup membership test: on `y^2 = x^3 + 4` and `[r]P = O`. -/
def g1InGroup (p : G1Point) : Bool :=
  g1OnCurve p && (g1JacScale (g1ToJac p) bls12381FrOrder).2.2 == 0

/-- Multiply the canonical `G1` generator by `scalar mod r`. -/
def g1OfScalar (scalar : Nat) : G1Point :=
  g1Scale g1Generator scalar

/-! ## ZCash 48-byte compressed serialization (`G1`) -/

/-- Compress a `G1` point into 48 bytes (ZCash format: big-endian `x` with flags `0x80` compressed,
`0x40` infinity, `0x20` lexicographically larger `y`). -/
def compressG1 : G1Point → List Nat
  | none => 0xc0 :: List.replicate 47 0
  | some (x, y) =>
      let digits := beBytes 48 (x % bls12381FqOrder)
      let flags := 0x80 + (if y % bls12381FqOrder > (bls12381FqOrder - 1) / 2 then 0x20 else 0)
      ((digits.headD 0) + flags) % 256 :: digits.tail

theorem compressG1_length : ∀ p, (compressG1 p).length = 48
  | none => rfl
  | some (x, _) => by
      simp only [compressG1, List.length_cons, List.length_tail, beBytes_length]

theorem compressG1_bytes : ∀ p b, b ∈ compressG1 p → b < 256
  | none, b, hb => by
      rcases List.mem_cons.mp hb with rfl | hm
      · decide
      · rw [List.mem_replicate] at hm; omega
  | some (x, y), b, hb => by
      rcases List.mem_cons.mp hb with rfl | hm
      · omega
      · exact beBytes_bytes 48 (x % bls12381FqOrder) b (List.mem_of_mem_tail hm)

/-- Candidate point decoded from 48 compressed bytes (square root via `q ≡ 3 (mod 4)`). -/
def decompressG1Candidate (bs : List Nat) : Option G1Point :=
  if bs.length != 48 || !bs.all (· < 256) then none
  else
    let first := bs.headD 0
    if first &&& 0x80 == 0 then none
    else if first &&& 0x40 != 0 then
      if first == 0xc0 && bs.tail.all (· == 0) then some none else none
    else
      let q := bls12381FqOrder
      let x := fromBeBytes ((first &&& 0x1f) :: bs.tail)
      if x ≥ q then none
      else
        let rhs := (x * x % q * x + 4) % q
        let root := modPow rhs ((q + 1) / 4) q
        if (root * root) % q == rhs then
          let wantLarge := first &&& 0x20 != 0
          let isLarge := root > (q - 1) / 2
          let y := if isLarge == wantLarge then root else negMod root q
          some (some (x, y))
        else none

/-- Canonical ZCash 48-byte `G1` decompression: verifies canonical encoding and prime-order subgroup
membership (`g1InGroup`). -/
def decompressG1 (bs : List Nat) : Option G1Point :=
  match decompressG1Candidate bs with
  | some p => if compressG1 p == bs && g1InGroup p then some p else none
  | none => none

theorem decompressG1_canonical {bs : List Nat} {p : G1Point}
    (h : decompressG1 bs = some p) : g1InGroup p = true ∧ compressG1 p = bs := by
  unfold decompressG1 at h
  cases hc : decompressG1Candidate bs with
  | none => simp [hc] at h
  | some cand =>
      simp only [hc] at h
      split at h
      · next hok =>
          cases h
          simp only [Bool.and_eq_true, beq_iff_eq] at hok
          exact ⟨hok.2, hok.1⟩
      · cases h

end Zkc.Runtime.Crypto
