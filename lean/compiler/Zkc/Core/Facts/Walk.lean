module

public import Zkc.Core.Facts.State

@[expose] public section

/-!
The check of facts: one walk over a term of any dialect, with what the dialect tells it of its
operations.

Inside the walk a value has an identifier that is never reused. The walk carries the identifier
of each name in scope, a map from names to identifiers (`Ctx Nat`): where the term binds names to
its context, the walk binds the same names to the new identifiers, a later name hiding an earlier
one as in the context (`bindIds`).

At an operation that computes, every requirement of its written form is decided from what is
known there; each that is not known is refused at the place, and the walk goes on as if it were
known. The results are then those of the table, and what the operation's ranges say of them is
learned. A guard learns its condition; a choice learns its condition in one region and its
negation in the other; what a choice, a case analysis or a block returns has the hull of the
ranges that its regions that run give it, and the result of a choice whose other region returns
a written truth value is remembered as a conjunction or a disjunction. A loop's index has the
range below its count, a loop of a counted value the order below the count and its bound, and
a sum `x + t` of its index `t`, counted below `r - x`, the range below that of `r`; a carried
natural that the body returns as itself plus a term has, after the loop, the lower end of its
initial range and the upper end of the sum.

A region is dead, and nothing in it is refused, exactly when what is written says that it never
runs: the body of a loop of the written count zero; a region where a value of a type that has no
value comes into scope (an input, the payload of an alternative, a carried value, an index, what
an operation or a region gives); and what comes after a choice, a case analysis or a block all of
whose regions are dead. What is known never makes a region dead: ranges of an identifier that
have no number in common leave it the empty range, and a truth value may be learned both ways.
-/

namespace Zkc.Core

namespace FactCheck

/-- The exit of a region: the state, what is known there, the identifiers it returns. -/
structure Exit (T Raw : Type) where
  st : St T Raw
  known : Known
  rets : List Nat

/-- The identifier of a name in scope. In the walk every name in scope has one (`InScope` in
`Growth.lean`), so the `0` of a name without one is never read. -/
def idOf (ids : Ctx Nat) (name : Name) : Nat := (ids.find? name).getD 0

/-- The identifiers of variables. -/
def idsOf {α : Type} {Γ : Ctx α} (ids : Ctx Nat) : {items : List α} → HList (Var Γ) items →
    List Nat
  | [], .nil => []
  | _ :: _, .cons x rest => idOf ids x.name :: idsOf ids rest

/-- The identifiers of the names in scope with the names of a binding bound to identifiers, in
order, as `Ctx.extend` binds them to their types: a later name hides an earlier one. The walk
gives as many identifiers as names (`opStep_grows`, `fresh`); names left without one would stay
as they were. -/
def bindIds {α : Type} (ids : Ctx Nat) : {types : List α} → Names types → List Nat → Ctx Nat
  | [], .nil, _ => ids
  | _ :: _, .cons name rest, i :: is => bindIds (ids.insert name i) rest is
  | _ :: _, .cons _ _, [] => ids

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

/-- What is known when values of the types come into scope: the region is dead when one of the
types has no value. -/
def Known.enter {D : Dialect} {Raw : Type} (rules : FactRules D Raw) (k : Known)
    (τs : List D.Ty) : Known :=
  if τs.any rules.noValue then k.kill else k

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
value. -/
def indexRange {D : Dialect} {w : D.Who} {Γ : Ctx D.Ty} (k : Known) (ids : Ctx Nat) :
    Times D w Γ → Range
  | .fixed n => Range.below (Range.point n)
  | .value count _ => (k.rangeOf (idOf ids count.name)).elim ⟨0, none⟩ Range.below

/-- What is known in a loop's body: what is known around it, the range of its index, the order
below the count, and what the types of the index and the carried values say; dead when the count
is written and zero. -/
def bodyKnown {D : Dialect} {Raw : Type} (rules : FactRules D Raw) {w : D.Who} {Γ : Ctx D.Ty}
    (k : Known) (ids : Ctx Nat) (times : Times D w Γ) (index : Nat) (carriedIds : List Nat)
    (carried : List D.Ty) : Known :=
  let k₁ := (k.addRange index (indexRange k ids times)).addRange? index (rules.range (D.index w))
  let k₂ := match times with
    | .fixed _ => k₁
    | .value count _ => k₁.addOrder index (idOf ids count.name) true (byLoop := true)
  let k₃ := (k₂.addRanges carriedIds (carried.map rules.range)).enter rules (D.index w :: carried)
  match times with
  | .fixed 0 => k₃.kill
  | _ => k₃

/-- How many times a loop runs at most. -/
def timesBound {D : Dialect} {w : D.Who} {Γ : Ctx D.Ty} (k : Known) (ids : Ctx Nat) :
    Times D w Γ → Option Nat
  | .fixed n => some n
  | .value count _ => (k.rangeOf (idOf ids count.name)).bind (·.hi)

/-- The term that the body of a loop adds to a carried natural, when it returns it as itself
plus a term. -/
def carriedTerm {T Raw : Type} (ops : OpFacts Raw) (body : Exit T Raw) (carriedId returned : Nat) :
    Option Nat :=
  match body.st.table.formOf ops returned with
  | some (.sum, [x, y]) => if x = carriedId then some y else if y = carriedId then some x else none
  | _ => none

/-- The range of a natural from an initial range, after at most `high` iterations that each add
a term of a range: it starts where the initial range starts (TY8). -/
def Range.afterSums (initial term : Range) (high : Option Nat) : Range :=
  ⟨initial.lo,
    match initial.hi, high, term.hi with
    | some h₀, some n, some ht => some (h₀ + n * ht)
    | _, _, _ => none⟩

namespace Range

theorem afterSums_zero {r₀ rt : Range} {n : Nat} (h : r₀.Has n) :
    (Range.afterSums r₀ rt (some 0)).Has n := by
  obtain ⟨lo, hi⟩ := h
  refine ⟨lo, fun h e => ?_⟩
  simp only [Range.afterSums] at e
  rcases r₀ with ⟨l₀, _ | h₀⟩ <;> rcases rt with ⟨lt, _ | ht⟩ <;> simp at e
  have := hi h₀ rfl
  omega

theorem afterSums_step {r₀ rt : Range} {i n t : Nat}
    (h : (Range.afterSums r₀ rt (some i)).Has n) (ht : rt.Has t) :
    (Range.afterSums r₀ rt (some (i + 1))).Has (n + t) := by
  obtain ⟨lo, hi⟩ := h
  obtain ⟨tlo, thi⟩ := ht
  simp only [Range.afterSums] at lo hi ⊢
  refine ⟨Nat.le_trans lo (Nat.le_add_right _ _), fun h e => ?_⟩
  rcases r₀ with ⟨l₀, _ | h₀⟩ <;> rcases rt with ⟨lt, _ | ht'⟩ <;> simp at e hi thi
  subst e
  have := hi
  have := thi
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem afterSums_widen {r₀ rt : Range} {N n : Nat} {high : Option Nat}
    (h : (Range.afterSums r₀ rt (some N)).Has n)
    (hhigh : ∀ m, high = some m → N ≤ m) : (Range.afterSums r₀ rt high).Has n := by
  obtain ⟨lo, hi⟩ := h
  simp only [Range.afterSums] at lo hi ⊢
  refine ⟨lo, fun h e => ?_⟩
  rcases r₀ with ⟨l₀, _ | h₀⟩ <;> rcases high with _ | m <;> rcases rt with ⟨lt, _ | ht⟩ <;>
    simp at e hi
  subst e
  have := hhigh m rfl
  exact Nat.le_trans hi (Nat.add_le_add_left (Nat.mul_le_mul_right _ this) _)

end Range

/-- The range of a carried natural after a loop: the range of the sum, when the body returns
it as itself plus a term; the initial range when no iteration can end. -/
def carriedRange {T Raw : Type} (ops : OpFacts Raw) (body : Exit T Raw) (initial : Option Range)
    (carriedId returned : Nat) (iterations : Option Nat) : Option Range :=
  if body.known.dead || iterations = some 0 then initial
  else
    match carriedTerm ops body carriedId returned, initial with
    | some t, some r₀ =>
        (body.known.rangeOf t).map fun rt => Range.afterSums r₀ rt iterations
    | _, _ => none

/-- What is known after a loop of what it gives: the carried values, from what was known of
their initial values, then the collected ones. -/
def afterLoop {D : Dialect} {Raw : Type} (rules : FactRules D Raw) (body : Exit D.Ty Raw)
    (k : Known) (iterations : Option Nat) :
    List Nat → List (Option Range) → List Nat → List Nat → List D.Ty → Known
  | m :: ms, initial :: initials, carriedId :: carriedIds, returned :: returns, τ :: τs =>
      let r := carriedRange rules.ops body initial carriedId returned iterations
      afterLoop rules body ((k.addRange? m r).addRange? m (rules.range τ)) iterations ms initials
        carriedIds returns τs
  | ms, _, _, _, τs => k.addRanges ms (τs.map rules.range)

/-- The state after a loop's body, with the loop's bound when the loop runs as often as a count
whose range has an upper end. -/
def recordBound {D : Dialect} {Raw : Type} {w : D.Who} {Γ : Ctx D.Ty} (place : Place)
    (k : Known) (ids : Ctx Nat) (st : St D.Ty Raw) : Times D w Γ → St D.Ty Raw
  | .value count _ =>
      match (k.rangeOf (idOf ids count.name)).bind (·.hi) with
      | some bound => { st with bounds := (place, bound) :: st.bounds }
      | none => st
  | .fixed _ => st

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (rules : FactRules D Raw)
  (definition : Key) (role : Option Role)

/-- An operation: its requirements decided, its results from the table, what its ranges and the
types say of them learned; and, for `x + t` below `r` by the order that a loop made for its
index `t`, the range below that of `r` (TY10). An operation that does not compute gives new
values. -/
def opStep (place : Place) {ins res : List D.Ty} (o : D.Op ins res) (argIds : List Nat)
    (k : Known) (st : St D.Ty Raw) : List Nat × Known × St D.Ty Raw :=
  match rules.written o with
  | none =>
      let made := fresh res.length st
      (made.1, (k.addRanges made.1 (res.map rules.range)).enter rules res, made.2)
  | some written =>
      let st₁ := checkRequirements rules.ops k place written argIds
        (rules.ops.requires written) st
      let made := share written argIds res.length st₁
      let k₁ := k.addRanges made.1 (rules.ops.ranges written (argIds.map k.rangeOf))
      let k₂ := k₁.addOffset rules.ops made.2.table k written argIds made.1
      (made.1, (k₂.addRanges made.1 (res.map rules.range)).enter rules res, made.2)

mutual
  /-- The walk of a term, from the identifiers of the names in its context, what is known and the
  state. -/
  def walk (blocks : List (Key × Nat)) :
      {Γ : Ctx D.Ty} → {outs : List D.Ty} → Term D Γ outs → Ctx Nat → Known → St D.Ty Raw →
        Exit D.Ty Raw
    | _, _, .ret xs, ids, k, st => ⟨st, k, idsOf ids xs⟩
    | _, _, .op key o args results rest, ids, k, st =>
        let step := opStep rules ⟨definition, blocks, some key, role⟩ o (idsOf ids args) k st
        walk blocks rest (bindIds ids results step.1) step.2.1 step.2.2
    | _, _, .guard _ _ c _ _ rest, ids, k, st =>
        walk blocks rest ids (assume rules.ops st.table st.next k (idOf ids c.name) true) st
    | _, _, .choose (mid := mid) _ _ c _ _ onTrue onFalse results rest, ids, k, st =>
        let condition := idOf ids c.name
        let first := walk blocks onTrue ids
          (assume rules.ops st.table st.next k condition true) st
        let second := walk blocks onFalse ids
          (assume rules.ops first.st.table first.st.next k condition false) first.st
        let made := fresh mid.length second.st
        walk blocks rest (bindIds ids results made.1)
          ((afterChoice rules k condition first second made.1 mid).enter rules mid) made.2
    | _, _, .cases (mid := mid) _ _ _ _ _ arms results rest, ids, k, st =>
        let regions := walkArms blocks arms ids k st
        let made := fresh mid.length regions.2
        walk blocks rest (bindIds ids results made.1)
          ((afterRegions rules regions.1 k made.1 mid 0).enter rules mid) made.2
    | _, _, .loop (carried := carried) (each := each) key _ times _ init inputs body results rest,
        ids, k, st =>
        let inBody := fresh (carried.length + 1) st
        let e := walk blocks body (bindIds ids inputs inBody.1)
          (bodyKnown rules k ids times (inBody.1.headD 0) inBody.1.tail carried) inBody.2
        let made := fresh (carried.length + each.length)
          (recordBound ⟨definition, blocks, some key, role⟩ k ids e.st times)
        let k₁ := afterLoop rules e k (timesBound k ids times) made.1
          ((idsOf ids init).map k.rangeOf) inBody.1.tail e.rets
          (carried ++ each.map (D.collected times.size))
        walk blocks rest (bindIds ids results made.1)
          (k₁.enter rules (carried ++ each.map (D.collected times.size))) made.2
    | _, _, .block (mid := mid) key number body results rest, ids, k, st =>
        let e := walk (blocks ++ [(key, number)]) body ids k st
        let made := fresh mid.length e.st
        walk blocks rest (bindIds ids results made.1)
          ((afterRegions rules [e] k made.1 mid 0).enter rules mid) made.2
    | _, _, .attempt (mid := mid) _ w _ inputs body results rest, ids, k, st =>
        let inBody := fresh 1 st
        let e := walk blocks body (bindIds ids inputs inBody.1)
          ((k.addRanges inBody.1 [rules.range (D.index w)]).enter rules [D.index w]) inBody.2
        let made := fresh mid.length e.st
        walk blocks rest (bindIds ids results made.1)
          ((afterRegions rules [e] k made.1 mid 0).enter rules mid) made.2
  /-- The walk of the arms of a case analysis: each with a new value for its payload, bound to
  the name of the arm's input. -/
  def walkArms (blocks : List (Key × Nat)) :
      {Γ : Ctx D.Ty} → {mid payloads : List D.Ty} → Arms D Γ mid payloads → Ctx Nat → Known →
        St D.Ty Raw → List (Exit D.Ty Raw) × St D.Ty Raw
    | _, _, _, .nil, _, _, st => ([], st)
    | _, _, _, .cons (payload := payload) inputs arm rest, ids, k, st =>
        let made := fresh 1 st
        let e := walk blocks arm (bindIds ids inputs made.1)
          ((k.addRanges made.1 [rules.range payload]).enter rules [payload]) made.2
        let others := walkArms blocks rest ids k e.st
        (e :: others.1, others.2)
end

end

end FactCheck

open FactCheck in
/-- The check of facts of a body in the context of its inputs, which have the first
identifiers: every application that is not known to be inside its operation's domain, refused at
its place; or, when there is none, the bound of each loop as often as a count whose count has an
upper bound. -/
def checkFacts {D : Dialect} {Raw : Type} (rules : FactRules D Raw) [DecidableEq Raw]
    (definition : Key) (role : Option Role) {types outs : List D.Ty} (inputs : Names types)
    (body : Term D (Ctx.empty.extend inputs) outs) :
    Except (List (Refusal D.Ty Raw)) (List (Place × Nat)) :=
  let first := List.range types.length
  let e := walk rules definition role [] body (bindIds Ctx.empty inputs first)
    ((Known.empty.addRanges first (types.map rules.range)).enter rules types)
    ⟨Table.empty rules.place, types.length, [], []⟩
  match e.st.refusals with
  | [] => .ok e.st.bounds.reverse
  | refusals => .error refusals.reverse

end Zkc.Core
