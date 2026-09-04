/-!
# The constitutional datum

`docs-next/foundation/executable-foundations.md` Section 2.1 fixes the
`MetaValueV0` algebra as exactly ten tagged structural forms: unit, the two
Booleans, natural, signed integer, bytes, symbol, sequence, record, and
variant. `evaluation/k1-executable-foundations/reference_model.py` carries the
same algebra as nine Python constructors (`Unit`, `bool`, `Nat`, `IntValue`,
`BytesValue`, `Symbol`, `DatumSeq`, `DatumRecord`, `DatumVariant`), with the
host `bool` standing for the two Boolean forms. This file transcribes the
algebra as one inductive type. The two Boolean forms are one constructor over
`Bool`, exactly as the Foundation page's total `MetaBooleanDatum` notation and
the Python model's host Boolean do.

Octets are modelled as natural numbers below `256`. The encoder establishes
that bound for every octet it emits (`M0.Encode`), and the well-formedness
predicate below requires it for octet strings carried inside a datum.

Nothing in this file is normative. It is a transcription whose only claim is
agreement with the Python goldens compared by the package runner.
-/

namespace M0

/-- One octet, modelled as a natural number below 256. -/
abbrev Octet := Nat

/-- The constitutional datum (`MetaValueV0`, Foundation Section 2.1). -/
inductive Datum where
  /-- Tag `0x00`. -/
  | unit
  /-- Tags `0x01` (false) and `0x02` (true). -/
  | bool (b : Bool)
  /-- Tag `0x03`: a natural number, framed as a minimal magnitude. -/
  | nat (n : Nat)
  /-- Tag `0x04`: a signed integer, a sign octet then a minimal magnitude. -/
  | int (i : Int)
  /-- Tag `0x05`: an octet string. -/
  | bytes (bs : List Octet)
  /-- Tag `0x06`: a nonempty printable-ASCII symbol, carried as its octets. -/
  | symbol (s : List Octet)
  /-- Tag `0x07`: an ordered sequence of child data. -/
  | seq (xs : List Datum)
  /-- Tag `0x08`: a record of `(ordinal, value)` fields in strictly increasing
  ordinal order. -/
  | record (fs : List (Nat × Datum))
  /-- Tag `0x09`: a variant case with one payload. -/
  | variant (c : Nat) (p : Datum)
  deriving Repr, Inhabited

/-- Lengths, counts, ordinals, and cases fit an unsigned 64-bit integer
(Foundation Section 2.1). -/
def fitsU64 (n : Nat) : Bool := n < 2 ^ 64

/-- A symbol octet is printable ASCII in `0x21..0x7e`. -/
def symbolOctet (c : Octet) : Bool := 0x21 ≤ c && c ≤ 0x7e

/-- Record ordinals are strictly increasing. -/
def ordinalsIncreasing : List (Nat × Datum) → Bool
  | [] => true
  | [_] => true
  | (o₁, _) :: (o₂, x) :: rest => o₁ < o₂ && ordinalsIncreasing ((o₂, x) :: rest)

mutual
  /-- Structural well-formedness: the conditions under which the Foundation
  page assigns a canonical encoding at all, independent of the four
  constitutional data limits (which `M0.Encode.withinLimits` checks). The
  Python encoder refuses exactly these conditions with `CanonicalError`. -/
  def wellFormed : Datum → Bool
    | .unit => true
    | .bool _ => true
    | .nat _ => true
    | .int _ => true
    | .bytes bs => bs.all (· < 256) && fitsU64 bs.length
    | .symbol s => !s.isEmpty && s.all symbolOctet && fitsU64 s.length
    | .seq xs => fitsU64 xs.length && wellFormedSeq xs
    | .record fs => fitsU64 fs.length && ordinalsIncreasing fs && wellFormedFields fs
    | .variant c p => fitsU64 c && wellFormed p
  def wellFormedSeq : List Datum → Bool
    | [] => true
    | x :: xs => wellFormed x && wellFormedSeq xs
  def wellFormedFields : List (Nat × Datum) → Bool
    | [] => true
    | (o, x) :: fs => fitsU64 o && wellFormed x && wellFormedFields fs
end

mutual
  /-- Root-zero depth (Foundation Section 2.1: "maximum root-zero depth"). -/
  def depth : Datum → Nat
    | .seq xs => depthSeq xs
    | .record fs => depthFields fs
    | .variant _ p => depth p + 1
    | _ => 0
  /-- One more than the largest child depth; zero for an empty aggregate. -/
  def depthSeq : List Datum → Nat
    | [] => 0
    | x :: xs => max (depth x + 1) (depthSeq xs)
  def depthFields : List (Nat × Datum) → Nat
    | [] => 0
    | (_, x) :: fs => max (depth x + 1) (depthFields fs)
end

mutual
  /-- Value constructors, counted once each (a "MetaValue node"). -/
  def nodes : Datum → Nat
    | .seq xs => 1 + nodesSeq xs
    | .record fs => 1 + nodesFields fs
    | .variant _ p => 1 + nodes p
    | _ => 1
  def nodesSeq : List Datum → Nat
    | [] => 0
    | x :: xs => nodes x + nodesSeq xs
  def nodesFields : List (Nat × Datum) → Nat
    | [] => 0
    | (_, x) :: fs => nodes x + nodesFields fs
end

mutual
  /-- Aggregate child edges: one per sequence item, record field value, or
  variant payload. -/
  def edges : Datum → Nat
    | .seq xs => xs.length + edgesSeq xs
    | .record fs => fs.length + edgesFields fs
    | .variant _ p => 1 + edges p
    | _ => 0
  def edgesSeq : List Datum → Nat
    | [] => 0
    | x :: xs => edges x + edgesSeq xs
  def edgesFields : List (Nat × Datum) → Nat
    | [] => 0
    | (_, x) :: fs => edges x + edgesFields fs
end

mutual
  /-- Structural equality as a Boolean test. The `deriving` handler for
  `DecidableEq` does not apply to nested inductive types in the pinned
  toolchain, so the test is written by hand. The runner never relies on it
  for a golden verdict: the encoding theorems in `M0.Theorems` make byte
  equality of encodings the decisive comparison. -/
  def beq : Datum → Datum → Bool
    | .unit, .unit => true
    | .bool a, .bool b => a == b
    | .nat a, .nat b => a == b
    | .int a, .int b => a == b
    | .bytes a, .bytes b => a == b
    | .symbol a, .symbol b => a == b
    | .seq xs, .seq ys => beqSeq xs ys
    | .record fs, .record gs => beqFields fs gs
    | .variant c p, .variant d q => c == d && beq p q
    | _, _ => false
  def beqSeq : List Datum → List Datum → Bool
    | [], [] => true
    | x :: xs, y :: ys => beq x y && beqSeq xs ys
    | _, _ => false
  def beqFields : List (Nat × Datum) → List (Nat × Datum) → Bool
    | [], [] => true
    | (o, x) :: fs, (p, y) :: gs => o == p && beq x y && beqFields fs gs
    | _, _ => false
end

instance : BEq Datum := ⟨beq⟩

end M0
