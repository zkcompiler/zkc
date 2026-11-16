module

public import Zkc.Core.Facts.OpFacts
public import Zkc.Core.Facts.Range
public import Zkc.Core.Program.BitTree
public import Zkc.Core.Program.Refusal
public import Zkc.Core.Value.Table

@[expose] public section

/-!
What the analysis knows, the rules that decide what is known, and the check of the
requirements of an application.

The analysis walks a term over the table of applications and its state (`Value/Table.lean`;
the walk is `Analysis.walk`, `Facts/Walk.lean`). Beside them it keeps what is known (ranges,
orders, truths, the two shapes of a choice, whether the region runs at all), which this file
defines with what is learned from a truth value (`assume`), and which is scoped: what is learned
in a region is dropped at its exit. How an identifier reads, when it is the first result of an
entry whose operation has a form, is what the dialect tells the analysis of the entry's
operation (`Table.formOf`).

The walk reads what is known through the functions here (how an identifier reads, the range of an
identifier, whether an order or a truth is known) and through whether a region is dead; how what
is known enters a region and the range of a carried natural after a loop are in `Walk.lean`.
Each part of what is known is placed by an identifier (`Program/BitTree.lean`): a list, read as a
list; nothing else depends on that. A requirement of an application is decided from the
identifiers and the ranges of the values that it names, an application among them found in the
table or entered; each that is not known is refused at its place (`checkRequirements`). The
arithmetic of ranges, with its lemmas, is in `Facts/Range.lean`.
-/

namespace Zkc.Core

namespace FactCheck

/-! ## How an identifier reads -/

section
variable {Raw : Type}

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

/-- What is known after `first ≠ second`: when one is zero, the other is at least one. Both
ranges are read before either is learned, as in the other rules, so the two orders of the
operands teach the same. -/
def pushDifferent (k : Known) (first second : Nat) : Known :=
  let learned :=
    if k.rangeOf second = some (Range.point 0) then k.addRange first ⟨1, none⟩ else k
  if k.rangeOf first = some (Range.point 0) then learned.addRange second ⟨1, none⟩ else learned

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

/-! ## The requirements of an application -/

section
variable {T Raw : Type}

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
