module

public import Zkc.Core.Facts.Knowledge.Known

@[expose] public section

namespace Zkc.Core.BodyAnalysis

open FactCheck (Known factDepth)

/-- Range updates in front of the ordinary indexed facts. A scan costs at most one
trie depth in comparisons. Materializing the buffer replays updates oldest first. -/
structure BufferedFacts where
  base : Known
  pending : List (Nat × Range)
  remaining : Nat

namespace BufferedFacts

def ofKnown (k : Known) : BufferedFacts := ⟨k, [], factDepth⟩
instance : Coe Known BufferedFacts := ⟨ofKnown⟩
def empty := ofKnown Known.empty

def flush (base : FactCheck.FactBuckets (Nat × Range)) : List (Nat × Range) → FactCheck.FactBuckets (Nat × Range)
  | [] => base
  | p :: ps => (flush base ps).insert p.1 p

def toKnown (k : BufferedFacts) : Known :=
  { k.base with ranges := flush k.base.ranges k.pending }

def readRanges (id : Nat) (tail : Option Range) : List (Nat × Range) → Option Range
  | [] => tail
  | (key,r) :: ps =>
    if key = id then Range.meet (some r) (readRanges id tail ps) else readRanges id tail ps

def rangeOf (k : BufferedFacts) (id : Nat) := readRanges id (k.base.rangeOf id) k.pending

def pointOf (k : BufferedFacts) (id : Nat) : Option Nat :=
  match k.rangeOf id with
  | some ⟨lo, some hi⟩ => if lo = hi then some lo else none
  | _ => none

def addRange (k : BufferedFacts) (id : Nat) (r : Range) : BufferedFacts :=
  match k.remaining with
  | 0 => ⟨k.toKnown, [(id,r)], factDepth - 1⟩
  | n+1 => ⟨k.base, (id,r) :: k.pending, n⟩

def addRange? (k : BufferedFacts) (id : Nat) : Option Range → BufferedFacts
  | none => k
  | some r => k.addRange id r

def dead (k : BufferedFacts) := k.base.dead
def kill (k : BufferedFacts) : BufferedFacts := { k with base := k.base.kill }
def truths (k : BufferedFacts) := k.base.truths
def orders (k : BufferedFacts) := k.base.orders
def hasTruth (k : BufferedFacts) := k.base.hasTruth
def hasOrder (k : BufferedFacts) := k.base.hasOrder
def addTruth (k : BufferedFacts) (id : Nat) (b : Bool) : BufferedFacts :=
  { k with base := k.base.addTruth id b }
def addOrder (k : BufferedFacts) (a b : Nat) (strict : Bool) (byLoop := false) : BufferedFacts :=
  { k with base := k.base.addOrder a b strict byLoop }

/-- What is known after `first < second`: the order; and a range of one side only when the
other side's range is one number. -/
def pushLess (k : BufferedFacts) (first second : Nat) : BufferedFacts :=
  let pf := k.pointOf first
  let ps := k.pointOf second
  let k := k.addOrder first second true
  let k := k.addRange? first (ps.map fun p => Range.below (Range.point p))
  k.addRange? second (pf.map fun p => ⟨p + 1, none⟩)

/-- What is known after `first ≤ second`: the order; and a range of one side only when the
other side's range is one number. -/
def pushLe (k : BufferedFacts) (first second : Nat) : BufferedFacts :=
  let pf := k.pointOf first
  let ps := k.pointOf second
  let k := k.addOrder first second false
  let k := k.addRange? first (ps.map fun p => ⟨0, some p⟩)
  k.addRange? second (pf.map fun p => ⟨p, none⟩)

/-- What is known after `first = second`: both orders; and the number of one side as the
other's only when it is one number. -/
def pushEqual (k : BufferedFacts) (first second : Nat) : BufferedFacts :=
  let pf := k.pointOf first
  let ps := k.pointOf second
  let k := (k.addOrder first second false).addOrder second first false
  let k := k.addRange? first (ps.map Range.point)
  k.addRange? second (pf.map Range.point)

/-- What is known after `first ≠ second`: when one is zero, the other is at least one. Both
ranges are read before either is learned, as in the other rules, so the two orders of the
operands teach the same. -/
def pushDifferent (k : BufferedFacts) (first second : Nat) : BufferedFacts :=
  let learned :=
    if k.rangeOf second = some (Range.point 0) then k.addRange first ⟨1, none⟩ else k
  if k.rangeOf first = some (Range.point 0) then learned.addRange second ⟨1, none⟩ else learned

end BufferedFacts
end Zkc.Core.BodyAnalysis
