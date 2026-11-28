module

public import Zkc.Vocabulary.Keys

@[expose] public section
set_option autoImplicit false

/-!
Concrete finite-field arithmetic and byte-encoding utilities for `ZkcRuntime`:
- KoalaBear (`p = 2^31 - 2^24 + 1 = 2130706433`, 2-adic generator `1791270792`)
- KoalaBear4 (`F_p[x] / (x^4 - 3)`, fast quadratic-tower inversion, 2-adic generator of order `2^26`)
- BLS12-381 scalar field `Fr` (`twoAdicity = 32`) and base field `Fq`
- Fixed-width little-endian / big-endian byte conversions and hex helpers
-/

namespace Zkc.Runtime.Crypto

/-! ## Field parameters -/

/-- Prime modulus of KoalaBear: `2^31 - 2^24 + 1 = 2130706433`. -/
def koalaBearOrder : Nat := 2130706433

/-- Primitive `2^24`-th root of unity in KoalaBear (`3^127 mod p`). -/
def koalaBearTwoAdicGen : Nat := 1791270792

/-- Quartic binomial nonresidue for `KoalaBear4 = F_p[x] / (x^4 - 3)`. -/
def koalaBear4Nonresidue : Nat := 3

/-- Prime order of the BLS12-381 scalar field `Fr` and curve subgroups `G1`, `G2`, `Gt`. -/
def bls12381FrOrder : Nat :=
  0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

/-- Primitive `2^32`-th root of unity in BLS12-381 `Fr` (`7^((r - 1) / 2^32) mod r`). -/
def bls12381FrTwoAdicGen : Nat :=
  0x16a2a19edfe81f20d09b681922c813b4b63683508c2280b93829971f439f0d2b

/-- Prime characteristic of the BLS12-381 base field `Fq`. -/
def bls12381FqOrder : Nat :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

/-! ## Prime-field modular arithmetic -/

/-- Modular exponentiation `base ^ exponent mod m` by binary squaring. -/
def modPow (base exponent m : Nat) : Nat :=
  if m ≤ 1 then 0
  else go (exponent.log2 + 1) (base % m) exponent (1 % m)
where
  go : Nat → Nat → Nat → Nat → Nat
    | 0, _, _, acc => acc
    | steps + 1, sq, rem, acc =>
        let acc' := if rem % 2 == 1 then (acc * sq) % m else acc
        go steps ((sq * sq) % m) (rem / 2) acc'

private theorem modPow_go_lt (m : Nat) (hm : 0 < m) :
    ∀ steps sq rem acc, acc < m → modPow.go m steps sq rem acc < m
  | 0, _, _, _, hacc => hacc
  | steps + 1, sq, rem, acc, hacc => by
      dsimp only [modPow.go]
      apply modPow_go_lt m hm
      split
      · exact Nat.mod_lt _ hm
      · exact hacc

theorem modPow_lt (base exponent m : Nat) (hm : 0 < m) : modPow base exponent m < m := by
  unfold modPow
  split
  · exact hm
  · exact modPow_go_lt m hm _ _ _ _ (Nat.mod_lt _ hm)

/-- Modular inverse in a prime field `F_m` via Fermat's little theorem; returns `0` for `0`. -/
def modInv (a m : Nat) : Nat :=
  if a % m == 0 || m ≤ 1 then 0 else modPow a (m - 2) m

theorem modInv_lt (a m : Nat) (hm : 0 < m) : modInv a m < m := by
  unfold modInv
  split
  · exact hm
  · exact modPow_lt a (m - 2) m hm

def addMod (a b m : Nat) : Nat := (a + b) % m
def negMod (a m : Nat) : Nat := (m - a % m) % m
def subMod (a b m : Nat) : Nat := (a + (m - b % m)) % m
def mulMod (a b m : Nat) : Nat := (a * b) % m

/-- Primitive `2^k`-th root of unity in a prime field given its `2^twoAdicity`-th generator. -/
def primeTwoAdicRoot (gen twoAdicity m k : Nat) : Nat :=
  let shift := if k ≤ twoAdicity then twoAdicity - k else 0
  modPow gen (2 ^ shift) m

/-! ## Quartic extension `KoalaBear4 = F_p[x] / (x^4 - 3)` -/

/-- Valid predicate for a `KoalaBear4` element represented as 4 base-field coefficients. -/
def Ext4Valid (xs : List Nat) : Prop :=
  xs.length = 4 ∧ ∀ c ∈ xs, c < koalaBearOrder

/-- Normalize any coefficient list into a 4-element valid `KoalaBear4` element. -/
def ext4Norm (xs : List Nat) : List Nat :=
  [xs.getD 0 0 % koalaBearOrder,
   xs.getD 1 0 % koalaBearOrder,
   xs.getD 2 0 % koalaBearOrder,
   xs.getD 3 0 % koalaBearOrder]

theorem ext4Norm_valid (xs : List Nat) : Ext4Valid (ext4Norm xs) := by
  refine ⟨rfl, ?_⟩
  intro c hc
  simp only [ext4Norm, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> exact Nat.mod_lt _ (by decide)

def ext4Zero : List Nat := [0, 0, 0, 0]
def ext4One : List Nat := [1, 0, 0, 0]

def ext4OfNat (n : Nat) : List Nat := [n % koalaBearOrder, 0, 0, 0]

def ext4Embed (a : Nat) : List Nat := [a % koalaBearOrder, 0, 0, 0]

def ext4IsNonzero (a : List Nat) : Bool :=
  let a := ext4Norm a
  a.any (· != 0)

def ext4Add (a b : List Nat) : List Nat :=
  let p := koalaBearOrder
  [(a.getD 0 0 + b.getD 0 0) % p,
   (a.getD 1 0 + b.getD 1 0) % p,
   (a.getD 2 0 + b.getD 2 0) % p,
   (a.getD 3 0 + b.getD 3 0) % p]

def ext4Neg (a : List Nat) : List Nat :=
  let p := koalaBearOrder
  [negMod (a.getD 0 0) p, negMod (a.getD 1 0) p, negMod (a.getD 2 0) p, negMod (a.getD 3 0) p]

def ext4Sub (a b : List Nat) : List Nat :=
  let p := koalaBearOrder
  [subMod (a.getD 0 0) (b.getD 0 0) p,
   subMod (a.getD 1 0) (b.getD 1 0) p,
   subMod (a.getD 2 0) (b.getD 2 0) p,
   subMod (a.getD 3 0) (b.getD 3 0) p]

/-- Multiplication in `F_p[x] / (x^4 - 3)`. -/
def ext4Mul (a b : List Nat) : List Nat :=
  let p := koalaBearOrder
  let a0 := a.getD 0 0 % p; let a1 := a.getD 1 0 % p
  let a2 := a.getD 2 0 % p; let a3 := a.getD 3 0 % p
  let b0 := b.getD 0 0 % p; let b1 := b.getD 1 0 % p
  let b2 := b.getD 2 0 % p; let b3 := b.getD 3 0 % p
  let c0 := (a0 * b0 + 3 * (a1 * b3 + a2 * b2 + a3 * b1)) % p
  let c1 := (a0 * b1 + a1 * b0 + 3 * (a2 * b3 + a3 * b2)) % p
  let c2 := (a0 * b2 + a1 * b1 + a2 * b0 + 3 * (a3 * b3)) % p
  let c3 := (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0) % p
  [c0, c1, c2, c3]

/-- Exponentiation in `KoalaBear4` by binary squaring. -/
def ext4Pow (base : List Nat) (exponent : Nat) : List Nat :=
  go (exponent.log2 + 1) (ext4Norm base) exponent ext4One
where
  go : Nat → List Nat → Nat → List Nat → List Nat
    | 0, _, _, acc => acc
    | steps + 1, sq, rem, acc =>
        let acc' := if rem % 2 == 1 then ext4Mul acc sq else acc
        go steps (ext4Mul sq sq) (rem / 2) acc'

/-- Fast exact inverse in `F_p[x] / (x^4 - 3)` via the quadratic tower `F_p ⊂ F_p[y]/(y^2-3) ⊂ F_p[x]/(x^2-y)`.
Requires only a single base-field inversion; returns `[0, 0, 0, 0]` on zero. -/
def ext4Inv (a : List Nat) : List Nat :=
  let p := koalaBearOrder
  let a0 := a.getD 0 0 % p; let a1 := a.getD 1 0 % p
  let a2 := a.getD 2 0 % p; let a3 := a.getD 3 0 % p
  let c0 := subMod ((a0 * a0 + 3 * (a2 * a2)) % p) ((6 * a1 * a3) % p) p
  let c1 := subMod ((2 * a0 * a2) % p) ((a1 * a1 + 3 * (a3 * a3)) % p) p
  let denom := subMod ((c0 * c0) % p) ((3 * (c1 * c1)) % p) p
  if denom == 0 then ext4Zero
  else
    let invD := modInv denom p
    let invC0 := (c0 * invD) % p
    let invC1 := (negMod c1 p * invD) % p
    let r0 := (a0 * invC0 + 3 * (a2 * invC1)) % p
    let r2 := (a0 * invC1 + a2 * invC0) % p
    let r1 := negMod ((a1 * invC0 + 3 * (a3 * invC1)) % p) p
    let r3 := negMod ((a1 * invC1 + a3 * invC0) % p) p
    [r0, r1, r2, r3]

/-- Primitive `2^26`-th root of unity in `KoalaBear4`: `x^127 = (3^31 mod p) * x^3`, since
`(x^127)^4 = 3^127 = 1791270792` has exact order `2^24` in `KoalaBear`. -/
def koalaBear4TwoAdicGen : List Nat :=
  [0, 0, 0, modPow 3 31 koalaBearOrder]

/-- Primitive `2^k`-th root of unity in `KoalaBear4` for `k ≤ 26`. -/
def ext4TwoAdicRoot (k : Nat) : List Nat :=
  let shift := if k ≤ 26 then 26 - k else 0
  ext4Pow koalaBear4TwoAdicGen (2 ^ shift)

private theorem four_mod_valid (c0 c1 c2 c3 : Nat) :
    Ext4Valid [c0 % koalaBearOrder, c1 % koalaBearOrder, c2 % koalaBearOrder, c3 % koalaBearOrder] := by
  refine ⟨rfl, ?_⟩
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> exact Nat.mod_lt _ (by decide)

theorem ext4Zero_valid : Ext4Valid ext4Zero := by
  refine ⟨rfl, ?_⟩
  intro c hc
  simp only [ext4Zero, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> decide

theorem ext4One_valid : Ext4Valid ext4One := by
  refine ⟨rfl, ?_⟩
  intro c hc
  simp only [ext4One, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> decide

theorem ext4OfNat_valid (n : Nat) : Ext4Valid (ext4OfNat n) := by
  refine ⟨rfl, ?_⟩
  intro c hc
  simp only [ext4OfNat, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact Nat.mod_lt _ (by decide)
  · decide
  · decide
  · decide

theorem ext4Add_valid (a b : List Nat) : Ext4Valid (ext4Add a b) := four_mod_valid ..
theorem ext4Neg_valid (a : List Nat) : Ext4Valid (ext4Neg a) := four_mod_valid ..
theorem ext4Sub_valid (a b : List Nat) : Ext4Valid (ext4Sub a b) := four_mod_valid ..
theorem ext4Mul_valid (a b : List Nat) : Ext4Valid (ext4Mul a b) := four_mod_valid ..

private theorem ext4Pow_go_valid :
    ∀ steps sq rem acc, Ext4Valid acc → Ext4Valid (ext4Pow.go steps sq rem acc)
  | 0, _, _, _, hacc => hacc
  | steps + 1, sq, rem, acc, hacc => by
      dsimp only [ext4Pow.go]
      apply ext4Pow_go_valid
      split
      · exact ext4Mul_valid ..
      · exact hacc

theorem ext4Pow_valid (base : List Nat) (exp : Nat) : Ext4Valid (ext4Pow base exp) :=
  ext4Pow_go_valid _ _ _ _ ext4One_valid

theorem ext4Inv_valid (a : List Nat) : Ext4Valid (ext4Inv a) := by
  unfold ext4Inv
  dsimp only
  split
  · exact ext4Zero_valid
  · exact four_mod_valid ..

theorem ext4TwoAdicRoot_valid (k : Nat) : Ext4Valid (ext4TwoAdicRoot k) :=
  ext4Pow_valid ..

/-! ## Byte-sequence and hexadecimal conversions -/

/-- Little-endian encoding of `value` in `width` bytes (`< 256`). -/
def leBytes : Nat → Nat → List Nat
  | 0, _ => []
  | w + 1, v => (v % 256) :: leBytes w (v / 256)

theorem leBytes_length : ∀ w v, (leBytes w v).length = w
  | 0, _ => rfl
  | w + 1, v => congrArg Nat.succ (leBytes_length w (v / 256))

theorem leBytes_bytes : ∀ w v b, b ∈ leBytes w v → b < 256
  | 0, _, _, h => nomatch h
  | w + 1, v, b, h => by
      rcases List.mem_cons.mp h with rfl | hm
      · omega
      · exact leBytes_bytes w (v / 256) b hm

/-- Decode little-endian bytes into a natural number. -/
def fromLeBytes (bs : List Nat) : Nat :=
  bs.foldr (fun b acc => b + 256 * acc) 0

/-- Big-endian encoding of `value` in `width` bytes (`< 256`). -/
def beBytes (width value : Nat) : List Nat :=
  (leBytes width value).reverse

theorem beBytes_length (w v : Nat) : (beBytes w v).length = w := by
  simp [beBytes, leBytes_length]

theorem beBytes_bytes (w v b : Nat) (h : b ∈ beBytes w v) : b < 256 :=
  leBytes_bytes w v b (List.mem_reverse.mp h)

/-- Decode big-endian bytes into a natural number. -/
def fromBeBytes (bs : List Nat) : Nat :=
  bs.foldl (fun acc b => acc * 256 + b) 0

/-- Convert a list of byte naturals to a `ByteArray`. -/
def toByteArray (bs : List Nat) : ByteArray :=
  ⟨(bs.map UInt8.ofNat).toArray⟩

/-- Convert a `ByteArray` to a list of byte naturals (`< 256`). -/
def ofByteArray (ba : ByteArray) : List Nat :=
  ba.toList.map UInt8.toNat

theorem ofByteArray_bytes (ba : ByteArray) : ∀ b ∈ ofByteArray ba, b < 256 := by
  intro b hb
  obtain ⟨u, _, rfl⟩ := List.mem_map.mp hb
  exact u.toNat_lt

/-- UTF-8 bytes of a string as `List Nat`. -/
def utf8Bytes (s : String) : List Nat :=
  ofByteArray s.toUTF8

/-- Lowercase hexadecimal string for a list of bytes. -/
def hexOfBytes (bs : List Nat) : String :=
  let digits : Array Char := #['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f']
  String.ofList (bs.flatMap fun b =>
    [digits.getD ((b % 256) / 16) '0', digits.getD (b % 16) '0'])

/-- Parse a lowercase or uppercase hexadecimal string into bytes. -/
def bytesOfHex? (s : String) : Option (List Nat) :=
  let nibble (c : Char) : Option Nat :=
    if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
    else if 'A' ≤ c ∧ c ≤ 'F' then some (10 + c.toNat - 'A'.toNat)
    else none
  let rec go : List Char → Option (List Nat)
    | [] => some []
    | [_] => none
    | hi :: lo :: rest => do
        let h ← nibble hi
        let l ← nibble lo
        let tail ← go rest
        some ((h * 16 + l) :: tail)
  go s.toList

end Zkc.Runtime.Crypto
