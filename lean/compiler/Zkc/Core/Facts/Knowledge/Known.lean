module

public import Zkc.Core.Facts.Range
public import Zkc.Core.Program.BitTree
public import Zkc.Core.Program.Context

@[expose] public section

namespace Zkc.Core.FactCheck

/-- Sparse low-bit buckets for facts. The numeric trie stops when the residue is exhausted.
Every bucket retains the original insertion order, including collisions. -/
structure FactBuckets (α : Type) where
  map : NatMap (List α)

namespace FactBuckets
variable {α : Type}

def empty : FactBuckets α := ⟨.leaf⟩

def find (t : FactBuckets α) (key : Nat) : List α :=
  (t.map.find (key % 2^factDepth)).getD []

def insert (t : FactBuckets α) (key : Nat) (x : α) : FactBuckets α :=
  ⟨t.map.insert (key % 2^factDepth) (x :: t.find key)⟩

theorem find_insert (t : FactBuckets α) (p q : Nat) (x : α) :
    (t.insert p x).find q =
      if q % 2^factDepth = p % 2^factDepth then x :: t.find q else t.find q := by
  simp only [find, insert, NatMap.find_insert]
  split <;> simp [*]

instance : Membership α (FactBuckets α) := ⟨fun t x => ∃ q, x ∈ t.find q⟩

theorem mem_of_find (t : FactBuckets α) (key : Nat) (x : α) (h : x ∈ t.find key) : x ∈ t :=
  ⟨key, h⟩

theorem mem_insert (t : FactBuckets α) (key : Nat) (x y : α) (h : y ∈ t.insert key x) :
    y ∈ t ∨ y = x := by
  obtain ⟨q, found⟩ := h
  rw [find_insert] at found
  split at found
  · rcases List.mem_cons.mp found with same | previous
    · exact Or.inr same
    · exact Or.inl ⟨q, previous⟩
  · exact Or.inl ⟨q, found⟩

theorem not_mem_empty (x : α) : x ∉ (empty : FactBuckets α) :=
  fun ⟨_, found⟩ => nomatch found

end FactBuckets

/-- An order `first < second` (strict) or `first ≤ second`, and whether a loop made it: the
order of its index below its count. -/
structure OrderFact where
  first : Nat
  second : Nat
  strict : Bool
  byLoop : Bool

/-- What is known at a place, each part placed by an identifier. -/
structure Known where
  /-- Ranges of naturals, by the identifier; several of one identifier are intersected. -/
  ranges : FactBuckets (Nat × Range)
  /-- Orders, by the first. -/
  orders : FactBuckets OrderFact
  /-- Truth values, by the identifier. -/
  truths : FactBuckets (Nat × Bool)
  /-- The region never runs. -/
  dead : Bool

/-- Nothing is known. -/
def Known.empty : Known := ⟨.empty, .empty, .empty, false⟩

/-- What the ranges say of an identifier, intersected. -/
def rangeIn (id : Nat) : List (Nat × Range) → Option Range
  | [] => none
  | fact :: rest =>
      if fact.1 = id then Range.meet (some fact.2) (rangeIn id rest) else rangeIn id rest

namespace Known

/-- The range of an identifier. -/
def rangeOf (k : Known) (id : Nat) : Option Range := rangeIn id (k.ranges.find id)

/-- A range of an identifier learned. Ranges of an identifier that have no number in common
leave it the empty range: they never make the region dead. -/
def addRange (k : Known) (id : Nat) (r : Range) : Known :=
  { k with ranges := k.ranges.insert id (id, r) }

/-- A range learned when there is one. -/
def addRange? (k : Known) (id : Nat) : Option Range → Known
  | some r => k.addRange id r
  | none => k

/-- Whether `first < second` (strict) or `first ≤ second` is an order that is known, whoever
made it. -/
def hasOrder (k : Known) (first second : Nat) (strict : Bool) : Bool :=
  (k.orders.find first).any fun fact =>
    fact.first == first && fact.second == second && (fact.strict || !strict)

/-- An order learned; `byLoop` when a loop made it for its index. -/
def addOrder (k : Known) (first second : Nat) (strict : Bool) (byLoop : Bool := false) : Known :=
  { k with orders := k.orders.insert first ⟨first, second, strict, byLoop⟩ }

/-- Whether the identifier is known to have the truth value. -/
def hasTruth (k : Known) (id : Nat) (value : Bool) : Bool :=
  (k.truths.find id).any fun fact => fact.1 == id && fact.2 == value

def addTruth (k : Known) (id : Nat) (value : Bool) : Known :=
  { k with truths := k.truths.insert id (id, value) }

def kill (k : Known) : Known := { k with dead := true }

/-- The one number of an identifier, when its range is one number. -/
def pointOf (k : Known) (id : Nat) : Option Nat :=
  match k.rangeOf id with
  | some ⟨lo, some hi⟩ => if lo = hi then some lo else none
  | _ => none

/-- What is known after `first < second`: the order; and a range of one side only when the
other side's range is one number. -/
def pushLess (k : Known) (first second : Nat) : Known :=
  let pf := k.pointOf first
  let ps := k.pointOf second
  let k := k.addOrder first second true
  let k := k.addRange? first (ps.map fun p => Range.below (Range.point p))
  k.addRange? second (pf.map fun p => ⟨p + 1, none⟩)

/-- What is known after `first ≤ second`: the order; and a range of one side only when the
other side's range is one number. -/
def pushLe (k : Known) (first second : Nat) : Known :=
  let pf := k.pointOf first
  let ps := k.pointOf second
  let k := k.addOrder first second false
  let k := k.addRange? first (ps.map fun p => ⟨0, some p⟩)
  k.addRange? second (pf.map fun p => ⟨p, none⟩)

/-- What is known after `first = second`: both orders; and the number of one side as the
other's only when it is one number. -/
def pushEqual (k : Known) (first second : Nat) : Known :=
  let pf := k.pointOf first
  let ps := k.pointOf second
  let k := (k.addOrder first second false).addOrder second first false
  let k := k.addRange? first (ps.map Range.point)
  k.addRange? second (pf.map Range.point)

/-- What is known after `first ≠ second`: when one is zero, the other is at least one. Both
ranges are read before either is learned, as in the other rules, so the two orders of the
operands teach the same. -/
def pushDifferent (k : Known) (first second : Nat) : Known :=
  let learned :=
    if k.rangeOf second = some (Range.point 0) then k.addRange first ⟨1, none⟩ else k
  if k.rangeOf first = some (Range.point 0) then learned.addRange second ⟨1, none⟩ else learned

end Known

/-- Whether the ranges say that the first is at most (below, with `strict`) the second. -/
def rangesOrder (first second : Option Range) (strict : Bool) : Bool :=
  match first, second with
  | some a, some b =>
      match a.hi with
      | some h => if strict then decide (h < b.lo) else decide (h ≤ b.lo)
      | none => false
  | _, _ => false

end Zkc.Core.FactCheck
