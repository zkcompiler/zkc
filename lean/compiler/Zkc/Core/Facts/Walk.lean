module

public import Zkc.Core.Facts.State

@[expose] public section

/-!
The check of facts: one walk over a term of any dialect, with what the dialect tells it of its
operations.

At an operation that computes, every requirement of its written form is decided from what is
known there; each that is not known is refused at the place, and the walk goes on as if it were
known. The results are then those of the table, and what the operation's ranges say of them is
learned. A guard learns its condition; a choice learns its condition in one region and its
negation in the other; what a choice, a case analysis or a block returns has the hull of the
ranges that its regions that run give it, and the result of a choice whose other region returns
a written truth value is remembered as a conjunction or a disjunction. A loop's index has the
range below its count, a loop of a counted value the order below the count and its bound; a
carried natural that the body returns as itself plus a term has, after the loop, the range of
the sum.
-/

namespace Zkc.Core

namespace FactCheck

/-- The exit of a region: the state, what is known there, the identifiers it returns. -/
structure Exit (T Raw : Type) where
  st : St T Raw
  known : Known
  rets : List Nat

/-- The identifiers of variables. -/
def idsOf {α : Type} {Γ : List α} (ids : List Nat) : {items : List α} → HList (Var Γ) items →
    List Nat
  | [], .nil => []
  | _ :: _, .cons x rest => ids.getD x.index 0 :: idsOf ids rest

/-- What a region that runs knows of the value it returns at a position; nothing from a region
that never runs. -/
def Exit.rangeAt {T Raw : Type} (e : Exit T Raw) (position : Nat) : Option (Option Range) :=
  if e.known.dead then none else some (e.known.rangeOf (e.rets.getD position 0))

/-- What the regions that run say of a returned value, together. -/
def hullOf : Option (Option Range) → Option (Option Range) → Option (Option Range)
  | none, r => r
  | r, none => r
  | some (some a), some (some b) => some (some (a.hull b))
  | some _, some _ => some none

/-- What is known after regions, of the values that they return: the hull of their ranges and
what the types say; nothing runs after when no region runs. -/
def afterRegions {D : Dialect} {Raw : Type} (rules : FactRules D Raw)
    (exits : List (Exit D.Ty Raw)) : Known → List Nat → List D.Ty → Nat → Known
  | k, m :: ms, τ :: τs, position =>
      let joined := exits.foldl (fun acc e => hullOf acc (e.rangeAt position)) none
      afterRegions rules exits ((k.addRange? m (joined.getD none)).addRange? m (rules.range τ))
        ms τs (position + 1)
  | k, _, _, _ => if exits.all (·.known.dead) then k.kill else k

/-- The shapes of a choice: a result whose second region returns `false` is the condition and
what the first returns; one whose first region returns `true`, the condition or what the second
returns. -/
def choiceFacts {T Raw : Type} (ops : OpFacts Raw) (tbl : Table Raw) (condition : Nat)
    (first second : Exit T Raw) : List Nat → Nat → List ChoiceFact
  | [], _ => []
  | m :: ms, position =>
      let conjunction :=
        match tbl.formOf ops (second.rets.getD position 0) with
        | some (.truth false, _) => [⟨m, true, condition, first.rets.getD position 0⟩]
        | _ => []
      let disjunction :=
        match tbl.formOf ops (first.rets.getD position 0) with
        | some (.truth true, _) => [⟨m, false, condition, second.rets.getD position 0⟩]
        | _ => []
      conjunction ++ disjunction ++ choiceFacts ops tbl condition first second ms (position + 1)

/-- What is known after a choice: what its regions say of the values they return, and the
shapes of its results. -/
def afterChoice {D : Dialect} {Raw : Type} (rules : FactRules D Raw) (k : Known)
    (condition : Nat) (first second : Exit D.Ty Raw) (made : List Nat) (mid : List D.Ty) :
    Known :=
  (choiceFacts rules.ops second.st.table condition first second made 0).foldl Known.addChoice
    (afterRegions rules [first, second] k made mid 0)

/-- What the index of a loop's body is known to be: below its count, which is written or a
value; dead when the count is zero. -/
def indexRange {D : Dialect} {w : D.Who} {Γ : List D.Ty} (k : Known) (ids : List Nat) :
    Times D w Γ → Range
  | .fixed n => Range.below (Range.point n)
  | .value count _ => (k.rangeOf (ids.getD count.index 0)).elim ⟨0, none⟩ Range.below

/-- What is known in a loop's body: what is known around it, the range of its index, the order
below the count, and what the types of the index and the carried values say. -/
def bodyKnown {D : Dialect} {Raw : Type} (rules : FactRules D Raw) {w : D.Who} {Γ : List D.Ty}
    (k : Known) (ids : List Nat) (times : Times D w Γ) (index : Nat) (carriedIds : List Nat)
    (carried : List D.Ty) : Known :=
  let k₁ := (k.addRange index (indexRange k ids times)).addRange? index (rules.range (D.index w))
  let k₂ := match times with
    | .fixed _ => k₁
    | .value count _ => k₁.addOrder index (ids.getD count.index 0) true
  k₂.addRanges carriedIds (carried.map rules.range)

/-- How many times a loop runs: at least and at most. -/
def timesBounds {D : Dialect} {w : D.Who} {Γ : List D.Ty} (k : Known) (ids : List Nat) :
    Times D w Γ → Nat × Option Nat
  | .fixed n => (n, some n)
  | .value count _ => (0, (k.rangeOf (ids.getD count.index 0)).bind (·.hi))

/-- The term that the body of a loop adds to a carried natural, when it returns it as itself
plus a term. -/
def carriedTerm {T Raw : Type} (ops : OpFacts Raw) (body : Exit T Raw) (carriedId returned : Nat) :
    Option Nat :=
  match body.st.table.formOf ops returned with
  | some (.sum, [x, y]) => if x = carriedId then some y else if y = carriedId then some x else none
  | _ => none

/-- The range of a natural from an initial range, after at least `low` and at most `high`
iterations that each add a term of a range. -/
def Range.afterSums (initial term : Range) (low : Nat) (high : Option Nat) : Range :=
  ⟨initial.lo + low * term.lo,
    match initial.hi, high, term.hi with
    | some h₀, some n, some ht => some (h₀ + n * ht)
    | _, _, _ => none⟩

/-- The range of a carried natural after a loop: the range of the sum, when the body returns
it as itself plus a term; the initial range when no iteration can end. -/
def carriedRange {T Raw : Type} (ops : OpFacts Raw) (body : Exit T Raw) (initial : Option Range)
    (carriedId returned : Nat) (iterations : Nat × Option Nat) : Option Range :=
  if body.known.dead || iterations.2 = some 0 then initial
  else
    match carriedTerm ops body carriedId returned, initial with
    | some t, some r₀ =>
        (body.known.rangeOf t).map fun rt => Range.afterSums r₀ rt iterations.1 iterations.2
    | _, _ => none

/-- What is known after a loop of what it gives: the carried values, from what was known of
their initial values, then the collected ones. -/
def afterLoop {D : Dialect} {Raw : Type} (rules : FactRules D Raw) (body : Exit D.Ty Raw)
    (k : Known) (iterations : Nat × Option Nat) :
    List Nat → List (Option Range) → List Nat → List Nat → List D.Ty → Known
  | m :: ms, initial :: initials, carriedId :: carriedIds, returned :: returns, τ :: τs =>
      let r := carriedRange rules.ops body initial carriedId returned iterations
      afterLoop rules body ((k.addRange? m r).addRange? m (rules.range τ)) iterations ms initials
        carriedIds returns τs
  | ms, _, _, _, τs => k.addRanges ms (τs.map rules.range)

/-- The state after a loop's body, with the loop's bound when the loop runs as often as a count
whose range has an upper end. -/
def recordBound {D : Dialect} {Raw : Type} {w : D.Who} {Γ : List D.Ty} (place : Place)
    (k : Known) (ids : List Nat) (st : St D.Ty Raw) : Times D w Γ → St D.Ty Raw
  | .value count _ =>
      match (k.rangeOf (ids.getD count.index 0)).bind (·.hi) with
      | some bound => { st with bounds := (place, bound) :: st.bounds }
      | none => st
  | .fixed _ => st

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (rules : FactRules D Raw)
  (definition : Key) (role : Option Role)

/-- An operation: its requirements decided, its results from the table, what its ranges and the
types say of them learned. An operation that does not compute gives new values. -/
def opStep (place : Place) {ins res : List D.Ty} (o : D.Op ins res) (argIds : List Nat)
    (k : Known) (st : St D.Ty Raw) : List Nat × Known × St D.Ty Raw :=
  match rules.written o with
  | none =>
      let made := fresh res.length st
      (made.1, k.addRanges made.1 (res.map rules.range), made.2)
  | some written =>
      let st₁ := checkRequirements rules.ops k place written argIds
        (rules.ops.requires written) st
      let made := share written argIds res.length st₁
      let k₁ := k.addRanges made.1 (rules.ops.ranges written (argIds.map k.rangeOf))
      (made.1, k₁.addRanges made.1 (res.map rules.range), made.2)

mutual
  /-- The walk of a term, from the identifiers of its context, what is known and the state. -/
  def walk (blocks : List (Key × Nat)) :
      {Γ outs : List D.Ty} → Term D Γ outs → List Nat → Known → St D.Ty Raw → Exit D.Ty Raw
    | _, _, .ret xs, ids, k, st => ⟨st, k, idsOf ids xs⟩
    | _, _, .op key o args rest, ids, k, st =>
        let step := opStep rules ⟨definition, blocks, some key, role⟩ o (idsOf ids args) k st
        walk blocks rest (step.1 ++ ids) step.2.1 step.2.2
    | _, _, .guard _ _ c _ _ rest, ids, k, st =>
        walk blocks rest ids (assume rules.ops st.table st.next k (ids.getD c.index 0) true) st
    | _, _, .choose (mid := mid) _ _ c _ _ onTrue onFalse rest, ids, k, st =>
        let condition := ids.getD c.index 0
        let first := walk blocks onTrue ids
          (assume rules.ops st.table st.next k condition true) st
        let second := walk blocks onFalse ids
          (assume rules.ops first.st.table first.st.next k condition false) first.st
        let made := fresh mid.length second.st
        walk blocks rest (made.1 ++ ids) (afterChoice rules k condition first second made.1 mid)
          made.2
    | _, _, .cases (mid := mid) _ _ _ _ _ arms rest, ids, k, st =>
        let regions := walkArms blocks arms ids k st
        let made := fresh mid.length regions.2
        walk blocks rest (made.1 ++ ids) (afterRegions rules regions.1 k made.1 mid 0) made.2
    | _, _, .loop (carried := carried) (each := each) key _ times _ init body rest, ids, k,
        st =>
        let inBody := fresh (carried.length + 1) st
        let e := walk blocks body (inBody.1 ++ ids)
          (bodyKnown rules k ids times (inBody.1.headD 0) inBody.1.tail carried) inBody.2
        let made := fresh (carried.length + each.length)
          (recordBound ⟨definition, blocks, some key, role⟩ k ids e.st times)
        let k₁ := afterLoop rules e k (timesBounds k ids times) made.1
          ((idsOf ids init).map k.rangeOf) inBody.1.tail e.rets
          (carried ++ each.map (D.collected times.size))
        walk blocks rest (made.1 ++ ids) k₁ made.2
    | _, _, .block (mid := mid) key number body rest, ids, k, st =>
        let e := walk (blocks ++ [(key, number)]) body ids k st
        let made := fresh mid.length e.st
        walk blocks rest (made.1 ++ ids) (afterRegions rules [e] k made.1 mid 0) made.2
    | _, _, .attempt (mid := mid) _ w _ body rest, ids, k, st =>
        let inBody := fresh 1 st
        let e := walk blocks body (inBody.1 ++ ids)
          (k.addRanges inBody.1 [rules.range (D.index w)]) inBody.2
        let made := fresh mid.length e.st
        walk blocks rest (made.1 ++ ids) (afterRegions rules [e] k made.1 mid 0) made.2
  /-- The walk of the arms of a case analysis: each with a new value for its payload. -/
  def walkArms (blocks : List (Key × Nat)) :
      {Γ mid payloads : List D.Ty} → Arms D Γ mid payloads → List Nat → Known → St D.Ty Raw →
        List (Exit D.Ty Raw) × St D.Ty Raw
    | _, _, _, .nil, _, _, st => ([], st)
    | _, _, _, .cons (payload := payload) arm rest, ids, k, st =>
        let made := fresh 1 st
        let e := walk blocks arm (made.1 ++ ids) (k.addRanges made.1 [rules.range payload])
          made.2
        let others := walkArms blocks rest ids k e.st
        (e :: others.1, others.2)
end

end

end FactCheck

open FactCheck in
/-- The check of facts of a body: every application that is not known to be inside its
operation's domain, refused at its place; or, when there is none, the bound of each loop as
often as a count whose count has an upper bound. -/
def checkFacts {D : Dialect} {Raw : Type} (rules : FactRules D Raw) [DecidableEq Raw]
    (definition : Key) (role : Option Role) {Γ outs : List D.Ty} (body : Term D Γ outs) :
    Except (List (Refusal D.Ty Raw)) (List (Place × Nat)) :=
  let ids := List.range Γ.length
  let e := walk rules definition role [] body ids
    (Known.empty.addRanges ids (Γ.map rules.range)) ⟨[], Γ.length, [], []⟩
  match e.st.refusals with
  | [] => .ok e.st.bounds.reverse
  | refusals => .error refusals.reverse

end Zkc.Core
