module

public import Zkc.Core.Facts.OpFacts
public import Zkc.Core.Program.BitTree
public import Zkc.Core.Program.Refusal

@[expose] public section

/-!
The state of the check of facts, and the rules that decide what is known.

Inside the walk a value has an identifier that is never reused. An application of a written
operation to operand identifiers has the result identifiers that the table gives it: those of
the first application of the same operation to the same identifiers, in their order, or new
ones. The table is never scoped: an entry says what a result is, not that it was computed.
What is known (ranges, orders, truths, the two shapes of a choice, whether the region runs at
all) is scoped: what is learned in a region is dropped at its exit.

The walk reads the table and what is known through the functions here (a lookup in the table and
an entry made in it, the entry of an identifier and how it reads, the range of an identifier,
whether an order or a truth is known) and through whether a region is dead; how what is known
enters a region and the range of a carried natural after a loop are in `Walk.lean`. Each of the
functions here reads the leaf of a tree placed by an identifier, or for an application by a
number computed from the number that the dialect gives for its written operation and from its
operands' identifiers (`Program/BitTree.lean`): a list, read as a list; nothing else depends on
that. The arithmetic of the ranges that this file defines is
proved beside it.
-/

namespace Zkc.Core

/-! ## Ranges -/

namespace Range

/-- The numbers in both ranges. -/
def inter (a b : Range) : Range :=
  ⟨max a.lo b.lo, match a.hi, b.hi with
    | some x, some y => some (min x y)
    | some x, none => some x
    | none, y => y⟩

/-- The numbers between the two ranges, both included. -/
def hull (a b : Range) : Range :=
  ⟨min a.lo b.lo, match a.hi, b.hi with
    | some x, some y => some (max x y)
    | _, _ => none⟩

/-- The range of one number. -/
def point (n : Nat) : Range := ⟨n, some n⟩

/-- The range of no number. -/
def nothing : Range := ⟨1, some 0⟩

/-- The numbers below a number of the range: from zero to its upper end less one; no number
when the upper end is zero, every natural when it has none. -/
def below (r : Range) : Range :=
  match r.hi with
  | some 0 => Range.nothing
  | some (h + 1) => ⟨0, some h⟩
  | none => ⟨0, none⟩

end Range

/-- What two pieces of knowledge of one natural say together; nothing known is the absence. -/
def Range.meet : Option Range → Option Range → Option Range
  | some a, some b => some (a.inter b)
  | some a, none => some a
  | none, b => b

namespace Range

theorem Has.inter {a b : Range} {n : Nat} (ha : a.Has n) (hb : b.Has n) : (a.inter b).Has n := by
  obtain ⟨la, ua⟩ := ha
  obtain ⟨lb, ub⟩ := hb
  refine ⟨Nat.max_le.mpr ⟨la, lb⟩, fun h e => ?_⟩
  rcases a with ⟨alo, _ | ahi⟩ <;> rcases b with ⟨blo, _ | bhi⟩ <;>
    simp only [Range.inter, Option.some.injEq, reduceCtorEq] at e
  · subst e; exact ub _ rfl
  · subst e; exact ua _ rfl
  · subst e; exact Nat.le_min.mpr ⟨ua _ rfl, ub _ rfl⟩

theorem Has.hull_left {a b : Range} {n : Nat} (ha : a.Has n) : (a.hull b).Has n := by
  obtain ⟨la, ua⟩ := ha
  refine ⟨Nat.le_trans (Nat.min_le_left _ _) la, fun h e => ?_⟩
  rcases a with ⟨alo, _ | ahi⟩ <;> rcases b with ⟨blo, _ | bhi⟩ <;>
    simp only [Range.hull, Option.some.injEq, reduceCtorEq] at e
  subst e
  exact Nat.le_trans (ua _ rfl) (Nat.le_max_left _ _)

theorem Has.hull_right {a b : Range} {n : Nat} (hb : b.Has n) : (a.hull b).Has n := by
  obtain ⟨lb, ub⟩ := hb
  refine ⟨Nat.le_trans (Nat.min_le_right _ _) lb, fun h e => ?_⟩
  rcases a with ⟨alo, _ | ahi⟩ <;> rcases b with ⟨blo, _ | bhi⟩ <;>
    simp only [Range.hull, Option.some.injEq, reduceCtorEq] at e
  subst e
  exact Nat.le_trans (ub _ rfl) (Nat.le_max_right _ _)

theorem has_point {n m : Nat} : (Range.point n).Has m ↔ m = n :=
  ⟨fun ⟨l, u⟩ => Nat.le_antisymm (u n rfl) l,
    fun e => by subst e; exact ⟨Nat.le_refl _, fun h e => by cases e; exact Nat.le_refl _⟩⟩

/-- Below a natural in the range, a natural is in the range below it. -/
theorem Has.below {r : Range} {c i : Nat} (h : r.Has c) (lt : i < c) : r.below.Has i := by
  rcases r with ⟨lo, _ | _ | hi⟩
  · exact ⟨Nat.zero_le _, fun _ e => nomatch e⟩
  · have := h.2 0 rfl
    exfalso
    omega
  · have := h.2 (hi + 1) rfl
    exact ⟨Nat.zero_le _, fun h' e => by cases e; omega⟩

end Range

theorem Range.meet_has {a b : Option Range} {r : Range} {n : Nat} (h : Range.meet a b = some r)
    (ha : ∀ r, a = some r → r.Has n) (hb : ∀ r, b = some r → r.Has n) : r.Has n := by
  cases a with
  | none =>
      simp only [Range.meet] at h
      exact hb r h
  | some a =>
      cases b with
      | none =>
          simp only [Range.meet, Option.some.injEq] at h
          subst h
          exact ha a rfl
      | some b =>
          simp only [Range.meet, Option.some.injEq] at h
          subst h
          exact (ha a rfl).inter (hb b rfl)

namespace FactCheck

/-! ## The table -/

/-- An entry of the table: a written operation applied to operand identifiers, in their order,
and the identifiers of its results, `lo` to `lo + count - 1`. -/
structure Entry (Raw : Type) where
  written : Raw
  args : List Nat
  lo : Nat
  count : Nat

/-- The depth of the trees of what the check knows: identifiers that agree on these low bits share
a leaf. -/
abbrev factDepth : Nat := 12

section
variable {Raw : Type}

/-- A number computed from naturals in order, from a number to start with, each multiplying
what came before by Knuth's multiplicative constant. -/
def mixNumbers (start : Nat) (ns : List Nat) : Nat :=
  ns.foldl (fun key n => key * 2654435761 + n + 1) start

/-- Where the table places an application, to find it: a number computed from the number that
the dialect gives for its written operation and from all of its operands' identifiers, in order,
so that applications that share their operands, or have none, fall in different leaves when
their written operations differ. -/
def applicationKey (written : Nat) (args : List Nat) : Nat := mixNumbers written args

/-- Places an entry at each of the identifiers. -/
def placeAll (e : Entry Raw) : List Nat → BitTree (Entry Raw) → BitTree (Entry Raw)
  | [], t => t
  | id :: ids, t => placeAll e ids (t.insert factDepth id e)

theorem mem_placeAll (e : Entry Raw) : ∀ (ids : List Nat) (t : BitTree (Entry Raw)) (x : Entry Raw),
    x ∈ placeAll e ids t → x ∈ t ∨ x = e
  | [], _, _, m => Or.inl m
  | id :: ids, t, x, m => by
      rcases mem_placeAll e ids _ x m with m | same
      · exact BitTree.mem_insert _ _ _ _ x m
      · exact Or.inr same

end

/-- The table: its entries, the latest first, and the same entries placed by the number that
`place` gives for their written operation and by their operands' identifiers
(`applicationKey`), to find an application, and by each of their results' identifiers, to find
what gives an identifier. The walk reads only the placed entries; every placed entry is an
entry. -/
structure Table (Raw : Type) where
  place : Raw → Nat
  entries : List (Entry Raw)
  byApplication : BitTree (Entry Raw)
  byResult : BitTree (Entry Raw)
  applications : ∀ e, e ∈ byApplication → e ∈ entries
  results : ∀ e, e ∈ byResult → e ∈ entries

instance {Raw : Type} : Membership (Entry Raw) (Table Raw) := ⟨fun t e => e ∈ t.entries⟩

section
variable {Raw : Type}

/-- The table without entries, which places applications by the number that `place` gives for
their written operation. -/
def Table.empty (place : Raw → Nat) : Table Raw :=
  ⟨place, [], .leaf [], .leaf [], fun e m => (BitTree.not_mem_empty e m).elim,
    fun e m => (BitTree.not_mem_empty e m).elim⟩

/-- The table with an entry made. -/
def Table.add (e : Entry Raw) (tbl : Table Raw) : Table Raw where
  place := tbl.place
  entries := e :: tbl.entries
  byApplication :=
    tbl.byApplication.insert factDepth (applicationKey (tbl.place e.written) e.args) e
  byResult := placeAll e (List.range' e.lo e.count) tbl.byResult
  applications x m := by
    rcases BitTree.mem_insert _ _ _ _ x m with m | same
    · exact List.mem_cons_of_mem _ (tbl.applications x m)
    · rw [same]; exact List.mem_cons_self
  results x m := by
    rcases mem_placeAll e _ _ x m with m | same
    · exact List.mem_cons_of_mem _ (tbl.results x m)
    · rw [same]; exact List.mem_cons_self

/-- The first result of the entry, among entries, of the written operation applied to the
operands, with the number of results: compared by its operands first. -/
def findIn [DecidableEq Raw] (written : Raw) (args : List Nat) (count : Nat) :
    List (Entry Raw) → Option Nat
  | [] => none
  | e :: es =>
      if e.args = args ∧ e.count = count ∧ e.written = written then some e.lo
      else findIn written args count es

/-- The first result of the entry of the written operation applied to the operands, with the
number of results: among the entries placed where the operands are. -/
def Table.find [DecidableEq Raw] (written : Raw) (args : List Nat) (count : Nat)
    (tbl : Table Raw) : Option Nat :=
  findIn written args count
    (tbl.byApplication.find factDepth (applicationKey (tbl.place written) args))

/-- The entry, among entries, that gives an identifier. -/
def entryIn (id : Nat) : List (Entry Raw) → Option (Entry Raw)
  | [] => none
  | e :: es => if e.lo ≤ id ∧ id < e.lo + e.count then some e else entryIn id es

/-- The entry that gives an identifier: among the entries placed at it. -/
def Table.entryOf (id : Nat) (tbl : Table Raw) : Option (Entry Raw) :=
  entryIn id (tbl.byResult.find factDepth id)

/-- How an identifier reads, when it is the first result of an entry whose operation has a
form: the form and the operands. -/
def Table.formOf (ops : OpFacts Raw) (tbl : Table Raw) (id : Nat) :
    Option (ResultForm × List Nat) :=
  match tbl.entryOf id with
  | some e => if e.lo = id then (ops.form e.written).map fun form => (form, e.args) else none
  | none => none

end

/-! ## What is known -/

/-- The result of a choice whose other region returns a written truth value: `condition and
other` (the second region returns `false`) or `condition or other` (the first returns
`true`). -/
structure ChoiceFact where
  result : Nat
  conjunction : Bool
  condition : Nat
  other : Nat
deriving DecidableEq

/-- An order `first < second` (strict) or `first ≤ second`, and whether a loop made it: the
order of its index below its count. -/
structure OrderFact where
  first : Nat
  second : Nat
  strict : Bool
  byLoop : Bool
deriving DecidableEq

/-- What is known at a place, each part placed by an identifier. -/
structure Known where
  /-- Ranges of naturals, by the identifier; several of one identifier are intersected. -/
  ranges : BitTree (Nat × Range)
  /-- Orders, by the first. -/
  orders : BitTree OrderFact
  /-- Truth values, by the identifier. -/
  truths : BitTree (Nat × Bool)
  /-- The shapes of choices, by the result. -/
  choices : BitTree ChoiceFact
  /-- The region never runs. -/
  dead : Bool

/-- Nothing is known. -/
def Known.empty : Known := ⟨.leaf [], .leaf [], .leaf [], .leaf [], false⟩

/-- What the ranges say of an identifier, intersected. -/
def rangeIn (id : Nat) : List (Nat × Range) → Option Range
  | [] => none
  | fact :: rest =>
      if fact.1 = id then Range.meet (some fact.2) (rangeIn id rest) else rangeIn id rest

namespace Known

/-- The range of an identifier. -/
def rangeOf (k : Known) (id : Nat) : Option Range := rangeIn id (k.ranges.find factDepth id)

/-- A range of an identifier learned. Ranges of an identifier that have no number in common
leave it the empty range: they never make the region dead. -/
def addRange (k : Known) (id : Nat) (r : Range) : Known :=
  { k with ranges := k.ranges.insert factDepth id (id, r) }

/-- A range learned when there is one. -/
def addRange? (k : Known) (id : Nat) : Option Range → Known
  | some r => k.addRange id r
  | none => k

/-- Ranges of identifiers, in order. -/
def addRanges (k : Known) : List Nat → List (Option Range) → Known
  | id :: ids, r :: rs => (k.addRange? id r).addRanges ids rs
  | _, _ => k

/-- Whether `first < second` (strict) or `first ≤ second` is an order that is known, whoever
made it. -/
def hasOrder (k : Known) (first second : Nat) (strict : Bool) : Bool :=
  (k.orders.find factDepth first).any fun fact =>
    fact.first == first && fact.second == second && (fact.strict || !strict)

/-- An order learned; `byLoop` when a loop made it for its index. -/
def addOrder (k : Known) (first second : Nat) (strict : Bool) (byLoop : Bool := false) : Known :=
  { k with orders := k.orders.insert factDepth first ⟨first, second, strict, byLoop⟩ }

/-- Whether the identifier is known to have the truth value. -/
def hasTruth (k : Known) (id : Nat) (value : Bool) : Bool :=
  (k.truths.find factDepth id).any fun fact => fact.1 == id && fact.2 == value

def addTruth (k : Known) (id : Nat) (value : Bool) : Known :=
  { k with truths := k.truths.insert factDepth id (id, value) }

def addChoice (k : Known) (choice : ChoiceFact) : Known :=
  { k with choices := k.choices.insert factDepth choice.result choice }

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

/-- What is known after `first ≠ second`: when one is zero, the other is at least one. -/
def pushDifferent (k : Known) (first second : Nat) : Known :=
  let k := if k.rangeOf second = some (Range.point 0) then k.addRange first ⟨1, none⟩ else k
  if k.rangeOf first = some (Range.point 0) then k.addRange second ⟨1, none⟩ else k

end Known

section
variable {Raw : Type} (ops : OpFacts Raw) (tbl : Table Raw)

/-- What is learned from the truth value of an identifier, by what it is in the table and by
the choices it is the result of. The fuel is the number of identifiers: each step goes to an
identifier made before. A truth value learned both ways never makes the region dead. -/
def assume : Nat → Known → Nat → Bool → Known
  | 0, k, id, value => k.addTruth id value
  | fuel + 1, k, id, value =>
      if k.hasTruth id value then k
      else
        let k₁ := k.addTruth id value
        let k₂ :=
          match tbl.formOf ops id with
          | some (.less, [first, second]) =>
              if value then k₁.pushLess first second else k₁.pushLe second first
          | some (.equal, [first, second]) =>
              if value then k₁.pushEqual first second else k₁.pushDifferent first second
          | some (.negation, [operand]) => assume fuel k₁ operand (!value)
          | some (.conjunction, [first, second]) =>
              if value then assume fuel (assume fuel k₁ first true) second true else k₁
          | some (.disjunction, [first, second]) =>
              if value then k₁ else assume fuel (assume fuel k₁ first false) second false
          | _ => k₁
        (k.choices.find factDepth id).foldl (fun known choice =>
          if choice.result = id ∧ choice.conjunction = value then
            assume fuel (assume fuel known choice.condition value) choice.other value
          else known) k₂

end

/-! ## Deciding a requirement -/

section
variable {Raw : Type} (ops : OpFacts Raw) (tbl : Table Raw) (k : Known)

/-- The lower end of what is known of an identifier. -/
def Known.low (id : Nat) : Nat := ((k.rangeOf id).map (·.lo)).getD 0

/-- `first + u` or `u + first` is `second`; with `strict`, the lower end of `u` is at least
one. -/
def sumAbove (first second : Nat) (strict : Bool) : Bool :=
  match tbl.formOf ops second with
  | some (.sum, [x, y]) =>
      (x == first && (!strict || decide (1 ≤ k.low y))) ||
        (y == first && (!strict || decide (1 ≤ k.low x)))
  | _ => false

/-- `first` is `second - u`; with `strict`, the lower end of `u` is at least one. -/
def differenceBelow (first second : Nat) (strict : Bool) : Bool :=
  match tbl.formOf ops first with
  | some (.difference, [x, u]) => x == second && (!strict || decide (1 ≤ k.low u))
  | _ => false

/-- The index of a range that does not start at zero: `first` is the sum of `x` and `t`, its
operands in either order, and `t < second - x` is the order that a loop made for its index `t`. -/
def offsetBelow (first second : Nat) : Bool :=
  match tbl.formOf ops first with
  | some (.sum, [x, y]) =>
      ((k.orders.find factDepth y).any fun fact =>
        fact.first == y && fact.strict && fact.byLoop &&
          (match tbl.formOf ops fact.second with
            | some (.difference, [r, x']) => r == second && x' == x
            | _ => false)) ||
      ((k.orders.find factDepth x).any fun fact =>
        fact.first == x && fact.strict && fact.byLoop &&
          (match tbl.formOf ops fact.second with
            | some (.difference, [r, y']) => r == second && y' == y
            | _ => false))
  | _ => false

/-- Whether the ranges say that the first is at most (below, with `strict`) the second. -/
def rangesOrder (first second : Option Range) (strict : Bool) : Bool :=
  match first, second with
  | some a, some b =>
      match a.hi with
      | some h => if strict then decide (h < b.lo) else decide (h ≤ b.lo)
      | none => false
  | _, _ => false

/-- Whether `first ≤ second` is known, with the ranges given of each. -/
def knownLe (first second : Nat) (rf rs : Option Range) : Bool :=
  rangesOrder rf rs false || first == second || k.hasOrder first second false ||
    sumAbove ops tbl k first second false || differenceBelow ops tbl k first second false

/-- Whether `first < second` is known, with the ranges given of each. -/
def knownLt (first second : Nat) (rf rs : Option Range) : Bool :=
  rangesOrder rf rs true || k.hasOrder first second true ||
    sumAbove ops tbl k first second true || differenceBelow ops tbl k first second true ||
    offsetBelow ops tbl k first second

/-- Whether the second less the first is the number: both are points, or the second is the sum
of the first and a value whose range is the point, its operands in either order. -/
def knownDifference (second first : Nat) (rs rf : Option Range) (number : Nat) : Bool :=
  (match rs, rf with
    | some ⟨p, some p'⟩, some ⟨q, some q'⟩ =>
        decide (p = p' ∧ q = q' ∧ q ≤ p ∧ p - q = number)
    | _, _ => false) ||
  (match tbl.formOf ops second with
    | some (.sum, [x, y]) =>
        (x == first && decide (k.rangeOf y = some (Range.point number))) ||
          (y == first && decide (k.rangeOf x = some (Range.point number)))
    | _ => false)

end

/-- For a sum `x + t` (by its operands' identifiers), where `t < r - x` is the order that a loop
made for its index `t`: that `r`, below which the sum is. -/
def offsetBound {Raw : Type} (ops : OpFacts Raw) (tbl : Table Raw) (k : Known) (x t : Nat) :
    Option Nat :=
  (k.orders.find factDepth t).findSome? fun fact =>
    if fact.first == t && fact.strict && fact.byLoop then
      match tbl.formOf ops fact.second with
      | some (.difference, [r, x']) => if x' == x then some r else none
      | _ => none
    else none

/-- What is known of the first result of an application of a written operation to operands
beyond what the operation's ranges say: for a sum of `x` and `t` below `r` (`offsetBound`), its
operands in either order (`x, t` tried first, then `t, x`), what is below the range of `r`
(TY10). -/
def offsetRange {Raw : Type} (ops : OpFacts Raw) (tbl : Table Raw) (k : Known) (written : Raw)
    (args : List Nat) : Option Range :=
  match ops.form written, args with
  | some .sum, [x, t] =>
      match offsetBound ops tbl k x t with
      | some r => (k.rangeOf r).map Range.below
      | none =>
          match offsetBound ops tbl k t x with
          | some r => (k.rangeOf r).map Range.below
          | none => none
  | _, _ => none

/-- What is known after an application of a written operation to operands, whose results are
the identifiers given: with what `offsetRange` says of its first result, read against what was
known before. -/
def Known.addOffset {Raw : Type} (k₁ : Known) (ops : OpFacts Raw) (tbl : Table Raw) (k : Known)
    (written : Raw) (args : List Nat) : List Nat → Known
  | first :: _ => k₁.addRange? first (offsetRange ops tbl k written args)
  | [] => k₁

/-! ## The state of the walk -/

/-- What the walk carries through every region: the table, the next identifier, the refusals
and the bounds of loops found so far (the latest first). -/
structure St (T Raw : Type) where
  table : Table Raw
  next : Nat
  refusals : List (Refusal T Raw)
  bounds : List (Place × Nat)

section
variable {T Raw : Type}

/-- New identifiers. -/
def fresh (count : Nat) (st : St T Raw) : List Nat × St T Raw :=
  (List.range' st.next count, { st with next := st.next + count })

/-- The results of the written operation applied to the operands: those of the first such
application, or new ones with an entry. -/
def share [DecidableEq Raw] (written : Raw) (args : List Nat) (count : Nat) (st : St T Raw) :
    List Nat × St T Raw :=
  match st.table.find written args count with
  | some lo => (List.range' lo count, st)
  | none =>
      (List.range' st.next count,
        { st with table := st.table.add ⟨written, args, st.next, count⟩,
                  next := st.next + count })

/-- The items at the positions, when every one is there. -/
def atPositions {α : Type} (xs : List α) : List Nat → Option (List α)
  | [] => some []
  | p :: ps =>
      match xs[p]?, atPositions xs ps with
      | some x, some rest => some (x :: rest)
      | _, _ => none

theorem atPositions_length {α : Type} {xs : List α} :
    ∀ {ps : List Nat} {ys : List α}, atPositions xs ps = some ys → ys.length = ps.length
  | [], ys, h => by simp only [atPositions, Option.some.injEq] at h; subst h; rfl
  | p :: ps, ys, h => by
      simp only [atPositions] at h
      split at h
      · next x rest e1 e2 =>
          cases h
          simp [atPositions_length e2]
      · cases h

theorem atPositions_mem {α : Type} {xs : List α} :
    ∀ {ps : List Nat} {ys : List α}, atPositions xs ps = some ys → ∀ y, y ∈ ys → y ∈ xs
  | [], ys, h, y, m => by simp only [atPositions, Option.some.injEq] at h; subst h; cases m
  | p :: ps, ys, h, y, m => by
      simp only [atPositions] at h
      split at h
      · next x rest e1 e2 =>
          cases h
          rcases List.mem_cons.mp m with rfl | m
          · exact List.mem_of_getElem? e1
          · exact atPositions_mem e2 y m
      · cases h

theorem atPositions_getElem {α : Type} {xs : List α} :
    ∀ {ps : List Nat} {ys : List α}, atPositions xs ps = some ys →
      ∀ (i p : Nat), ps[i]? = some p → ys[i]? = xs[p]?
  | [], ys, h, i, p, e => by simp at e
  | q :: ps, ys, h, i, p, e => by
      simp only [atPositions] at h
      split at h
      · next x rest e1 e2 =>
          cases h
          cases i with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at e
              subst e
              simpa using e1.symm
          | succ i =>
              simp only [List.getElem?_cons_succ] at e ⊢
              exact atPositions_getElem e2 i p e
      · cases h

theorem atPositions_append {α : Type} (xs : List α) :
    ∀ (ps qs : List Nat), atPositions xs (ps ++ qs) =
      (atPositions xs ps).bind fun as => (atPositions xs qs).map fun bs => as ++ bs
  | [], qs => by simp [atPositions]
  | p :: ps, qs => by
      simp only [List.cons_append, atPositions, atPositions_append xs ps qs]
      cases xs[p]? <;> cases atPositions xs ps <;> simp
      cases atPositions xs qs <;> simp

theorem atPositions_range {α : Type} (xs : List α) :
    ∀ n, n ≤ xs.length → atPositions xs (List.range n) = some (xs.take n)
  | 0, _ => by simp [atPositions]
  | n + 1, le => by
      rw [List.range_succ, atPositions_append, atPositions_range xs n (by omega)]
      simp only [atPositions, List.getElem?_eq_getElem (by omega : n < xs.length),
        Option.bind_some, Option.map_some, Option.some.injEq]
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega : n < xs.length)]
      rfl

/-- The identifier of a value that a requirement speaks of: an operand by its position, or the
first result of a written operation applied to operands, found in the table or entered. -/
def operandId [DecidableEq Raw] (argIds : List Nat) (st : St T Raw) :
    Operand Raw → Option Nat × St T Raw
  | .arg position => (argIds[position]?, st)
  | .apply written positions =>
      match atPositions argIds positions with
      | some args => let made := share written args 1 st; (made.1.head?, made.2)
      | none => (none, st)

/-- What is known of the value that an operand of a requirement names: the range of its
identifier and, for an operation applied to operands, the range that the operation gives. -/
def operandRange (ops : OpFacts Raw) (k : Known) (argIds : List Nat) :
    Operand Raw → Option Nat → Option Range
  | _, none => none
  | .arg _, some id => k.rangeOf id
  | .apply written positions, some id =>
      Range.meet (k.rangeOf id)
        ((ops.ranges written (positions.map fun p => (argIds[p]?).bind k.rangeOf)).head?.join)

/-- Whether a requirement is known, from the identifiers and ranges of its values. -/
def decideRequirement (ops : OpFacts Raw) (tbl : Table Raw) (k : Known) :
    Requirement Raw → List (Option Nat) → List (Option Range) → Bool
  | .le .., [some a, some b], [ra, rb] => knownLe ops tbl k a b ra rb
  | .lt .., [some a, some b], [ra, rb] => knownLt ops tbl k a b ra rb
  | .atLeast _ n, [some _], [ra] => match ra with | some r => decide (n ≤ r.lo) | none => false
  | .below _ n, [some _], [ra] =>
      match ra with
      | some ⟨_, some h⟩ => decide (h < n)
      | _ => false
  | .exactly _ n, [some _], [ra] =>
      match ra with
      | some ⟨lo, some h⟩ => decide (n ≤ lo ∧ h ≤ n)
      | _ => false
  | .difference _ _ n, [some b, some a], [rb, ra] => knownDifference ops tbl k b a rb ra n
  | .holds _, [some a], _ => k.hasTruth a true
  | .bounded _, [some _], [ra] => match ra with | some ⟨_, some _⟩ => true | _ => false
  | _, _, _ => false

/-- The identifiers of the values of a requirement, entering applications in the table. -/
def operandIds [DecidableEq Raw] (argIds : List Nat) :
    List (Operand Raw) → St T Raw → List (Option Nat) × St T Raw
  | [], st => ([], st)
  | operand :: rest, st =>
      let first := operandId argIds st operand
      let others := operandIds argIds rest first.2
      (first.1 :: others.1, others.2)

/-- Check the requirements of an application at a place, in order: each that is not known is
refused, and the walk goes on as if it were known. -/
def checkRequirements [DecidableEq Raw] (ops : OpFacts Raw) (k : Known) (place : Place)
    (written : Raw) (argIds : List Nat) : List (Requirement Raw) → St T Raw → St T Raw
  | [], st => st
  | requirement :: rest, st =>
      let operands := requirement.operands
      let resolved := operandIds argIds operands st
      let ranges := List.zipWith (operandRange ops k argIds) operands resolved.1
      let st₁ := resolved.2
      let st₂ :=
        if k.dead || decideRequirement ops st₁.table k requirement resolved.1 ranges then st₁
        else { st₁ with refusals :=
          ⟨.domain, place, .unjustified written requirement ranges⟩ :: st₁.refusals }
      checkRequirements ops k place written argIds rest st₂

end

end FactCheck

end Zkc.Core
