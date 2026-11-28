module

public import Zkc.Runtime.Model

@[expose] public section
set_option autoImplicit false

/-!
Canonical byte-format helpers and verified field codecs for `ZkcRuntime`.

Provides `formatPrimeField`, `formatPrimeField_lawful`, `formatExt4`, `formatExt4_lawful`, and
convenient round-trip / canonical-encoding wrappers over `writeCanonicalVal` and `readCanonicalVal`.
-/

namespace Zkc.Runtime

open Zkc.Core
open Zkc.Vocabulary
open Zkc.Vocabulary.Project
open Zkc.Runtime.Crypto

/-- Canonical little-endian fixed-width format for a prime field of order `order` in `width` bytes. -/
def formatPrimeField (order width : Nat) : Format Nat where
  write v := writeFixed width v
  read bs :=
    match readFixed width bs with
    | some (v, rest) => if v < order then some (v, rest) else none
    | none => none

theorem formatPrimeField_lawful (order width : Nat) (hfit : order ≤ 256 ^ width) :
    (formatPrimeField order width).Lawful (· < order) where
  bytes a _ b hb := writeFixed_bytes width a b hb
  reads a rest ha := by
    have hlt : a < 256 ^ width := Nat.lt_of_lt_of_le ha hfit
    simp only [formatPrimeField, readFixed_writeFixed width a rest hlt, ha, ↓reduceIte]
  written bs a rest h := by
    simp only [formatPrimeField] at h
    cases hr : readFixed width bs with
    | none => simp [hr] at h
    | some p =>
        simp only [hr] at h
        split at h
        · next hlt =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨hlt, (readFixed_written width bs p.1 p.2 hr).2⟩
        · cases h

/-- Canonical format for `KoalaBear` (4 little-endian bytes, rejecting `≥ 2130706433`). -/
def formatKoalaBear : Format Nat := formatPrimeField koalaBearOrder 4

theorem formatKoalaBear_lawful : formatKoalaBear.Lawful (· < koalaBearOrder) :=
  formatPrimeField_lawful koalaBearOrder 4 (by decide)

/-- Canonical format for `BLS12-381 Fr` (32 little-endian bytes, rejecting `≥ r`). -/
def formatBls12381Fr : Format Nat := formatPrimeField bls12381FrOrder 32

theorem formatBls12381Fr_lawful : formatBls12381Fr.Lawful (· < bls12381FrOrder) :=
  formatPrimeField_lawful bls12381FrOrder 32 (by decide)

/-- Canonical format for `KoalaBear4` (4 consecutive `KoalaBear` elements = 16 bytes). -/
def formatKoalaBear4 : Format (List Nat) := formatSeqSized formatKoalaBear 4

theorem formatKoalaBear4_lawful : formatKoalaBear4.Lawful Ext4Valid := by
  have h := formatSeqSized_lawful formatKoalaBear_lawful 4
  exact {
    bytes := fun xs hv => h.bytes xs ⟨hv.2, hv.1⟩
    reads := fun xs rest hv => h.reads xs rest ⟨hv.2, hv.1⟩
    written := fun bs xs rest hr =>
      let ⟨⟨hvs, hlen⟩, hbs⟩ := h.written bs xs rest hr
      ⟨⟨hlen, hvs⟩, hbs⟩
  }

/-- Encode an entire `HList` of linked runtime values canonically. -/
def writeLinkedHList (b : Bindings) : {ts : List LinkedType} →
    HList (Ty.Val (linkedCarriers b)) ts → List Nat
  | [], .nil => []
  | τ :: _, .cons v vs => writeCanonicalVal b τ v ++ writeLinkedHList b vs

/-- Decode an entire `HList` of linked runtime values canonically, requiring no trailing bytes. -/
def readLinkedHListExact (b : Bindings) (ts : List LinkedType) (bs : List Nat) :
    Option (HList (Ty.Val (linkedCarriers b)) ts) :=
  let rec go : (ts : List LinkedType) → List Nat → Option (HList (Ty.Val (linkedCarriers b)) ts × List Nat)
    | [], rem => some (.nil, rem)
    | τ :: rest, rem => do
        let (v, mid) ← readCanonicalVal b τ rem
        let (vs, tail) ← go rest mid
        some (.cons v vs, tail)
  match go ts bs with
  | some (vs, []) => some vs
  | _ => none

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def parseHexNibble (c : Char) : Option Nat :=
  let n := c.toNat
  if 48 ≤ n && n ≤ 57 then some (n - 48)
  else if 97 ≤ n && n ≤ 102 then some (n - 87)
  else if 65 ≤ n && n ≤ 70 then some (n - 55)
  else none

/-- Render a list of bytes (`Nat` values mod 256) as lowercase hexadecimal. -/
def bytesToHex (bs : List Nat) : String :=
  String.ofList (bs.flatMap fun b => [hexDigit ((b % 256) / 16), hexDigit (b % 16)])

/-- Parse an even-length hexadecimal string into a list of byte values (`< 256`). -/
def hexToBytes (s : String) : Option (List Nat) :=
  let rec go : List Char → Option (List Nat)
    | [] => some []
    | a :: b :: rest => do
        let hi ← parseHexNibble a
        let lo ← parseHexNibble b
        let tail ← go rest
        some ((hi * 16 + lo) :: tail)
    | _ => none
  go s.toList

end Zkc.Runtime
