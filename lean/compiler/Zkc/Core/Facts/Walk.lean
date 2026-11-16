module

public import Zkc.Core.Facts.State

@[expose] public section

/-!
The analysis: one walk over a term of any dialect, with what the dialect tells it of its
operations (`FactRules`).

Inside the walk a value has an identifier that is never reused. The walk carries the identifier
of each name in scope, a map from names to identifiers (`Ctx Nat`): where the term binds names to
its context, the walk binds the same names to the new identifiers, a later name hiding an earlier
one as in the context (`bindIds`, `Value/Table.lean`).

At an operation, shared or kept in order, every requirement of its written form is decided first,
from what is known where it is applied; each that is not known is refused at the place, and the
walk goes on as if it were known. Then a shared operation, a value, has the results of the table,
with the operands of an operation that commutes in one order (`ValueRules.order`), and what the
operation's ranges say of them is learned (`valueStep`); an operation that is kept in order gets
new identifiers, the leaves of its entry in the skeleton. A
guard learns its condition; a choice learns its condition in one region and its negation in the
other; what a choice, a case analysis or a block returns has the hull of the ranges that its
regions that run give it, and the result of a choice whose other region returns a written truth
value is remembered as a conjunction or a disjunction. A loop's index has the range below its
count, a loop of a counted value the order below the count and its bound, and a sum `x + t` of
its index `t`, counted below `r - x`, the range below that of `r`; a carried natural that the
body returns as itself plus a term has, after the loop, the lower end of its initial range and
the upper end of the sum. The bound of each loop as often as a count whose range has an upper end
is recorded.

A region is dead, and nothing in it is refused, exactly when what is written says that it never
runs: the body of a loop of the written count zero; a region where a value of a type that has no
value comes into scope (an input, the payload of an alternative, a carried value, an index, what
an operation or a region gives); and what comes after a choice, a case analysis or a block all of
whose regions are dead. What is known never makes a region dead: ranges of an identifier that
have no number in common leave it the empty range, and a truth value may be learned both ways.

The walk gives the skeleton of the term (`Value/Skeleton.lean`): what it keeps in order, on
identifiers of the table. With a skeleton to follow, the same walk follows it instead: every
instruction that the term keeps in order must be the skeleton's next entry and takes the entry's
leaves; where it is not, the place is recorded and the walk goes on without a skeleton. The
analysis of a definition (`Analysis.analyse`) starts from the empty table; a second definition
follows the analysis of a first from the first's table (`Analysis.follow`). The check of facts
is the refusals of the analysis, or the bounds that it recorded (`checkFacts`).
-/

namespace Zkc.Core

namespace FactCheck

/-- The exit of a region: the state, what is known there, the identifiers it returns. -/
structure Exit (T Raw : Type) where
  st : St T Raw
  known : Known
  rets : List Nat

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

end FactCheck

namespace Analysis

open FactCheck

section
variable {D : Dialect} {Raw : Type}

/-! ## The state and the exit of a region -/

/-- What the walk carries through every region: the state of the table with the refusals and the
bounds, and the places where the term differs from the skeleton that it follows (the latest
first). -/
structure State (T Raw : Type) where
  st : St T Raw
  differs : List Place

/-- The exit of a region: the state, what is known there, the identifiers that it returns, and
its skeleton: the one that it follows, or the region's own. -/
structure Exit (D : Dialect) (Raw : Type) (outs : List D.Ty) where
  state : State D.Ty Raw
  known : Known
  rets : List Nat
  skel : Skel D outs

/-- The exit of a region as the helpers of the check of facts read it. -/
def Exit.region {outs : List D.Ty} (e : Exit D Raw outs) : FactCheck.Exit D.Ty Raw :=
  ⟨e.state.st, e.known, e.rets⟩

/-- The exits of the arms of a case analysis, the state after them, and their skeletons. -/
structure ArmsExit (D : Dialect) (Raw : Type) (mid payloads : List D.Ty) where
  exits : List (FactCheck.Exit D.Ty Raw)
  state : State D.Ty Raw
  skel : SkelArms D mid payloads

/-- The leaves of an entry: those of the entry that is followed, from its first identifier, or
new identifiers. -/
def leaves {T : Type} (followed : Option Nat) (count : Nat) (s : State T Raw) :
    List Nat × State T Raw :=
  match followed with
  | some lo => (List.range' lo count, s)
  | none => ((fresh count s.st).1, { s with st := (fresh count s.st).2 })

/-- The state with a place where the term is not the next entry of the skeleton that it follows:
nothing is added when no skeleton is followed or the entry was found. -/
def miss {T : Type} (place : Place) (following found : Bool) (s : State T Raw) : State T Raw :=
  if following && !found then { s with differs := place :: s.differs } else s

/-- The skeleton of a region: the one that it follows, or the one built. -/
def kept {outs : List D.Ty} (followed : Option (Skel D outs)) (built : Skel D outs) : Skel D outs :=
  followed.getD built

/-! ## The next entry of a skeleton that is followed -/

section
variable (checks : SkelRules D)

/-- Whether a followed skeleton is an exit on the identifiers. -/
def retEntry {outs : List D.Ty} (exit : List Nat) : Skel D outs → Bool
  | .ret exit' => decide (exit = exit')
  | _ => false

/-- The entry of an operation kept in order: the leaf of its results and what comes after it. -/
def effectEntry {outs ins res : List D.Ty} (key : Key) (o : D.Op ins res) (operands : List Nat) :
    Option (Skel D outs) → Option (Nat × Skel D outs)
  | some (.effect (ins := ins') (res := res') key' o' operands' results' rest') =>
      match checks.sameTys ins ins', checks.sameTys res res' with
      | isTrue sameIns, isTrue sameRes =>
          if checks.sameOp o
                (cast (show D.Op ins' res' = D.Op ins res by rw [sameIns, sameRes]) o') = true ∧
              key = key' ∧ operands = operands' then
            some (results', rest')
          else none
      | _, _ => none
  | _ => none

/-- The entry of a guard: what comes after it. -/
def guardEntry {outs : List D.Ty} {t : D.Ty} (key : Key) (w : D.Who) (condition : Nat)
    (why : Reason) : Option (Skel D outs) → Option (Skel D outs)
  | some (.guard (t := t') key' w' condition' _ why' rest') =>
      match checks.sameWho w w', checks.sameTy t t' with
      | isTrue _, isTrue _ =>
          if key = key' ∧ why = why' ∧ condition = condition' then some rest' else none
      | _, _ => none
  | _ => none

/-- The entry of a choice: its two regions, the leaf of its results, what comes after it. -/
def chooseEntry {outs mid : List D.Ty} {t : D.Ty} (key : Key) (w : D.Who) (condition : Nat) :
    Option (Skel D outs) → Option (Skel D mid × Skel D mid × Nat × Skel D outs)
  | some (.choose (mid := mid') (t := t') key' w' condition' _ onTrue' onFalse' results' rest') =>
      match checks.sameWho w w', checks.sameTy t t', checks.sameTys mid mid' with
      | isTrue _, isTrue _, isTrue sameMid =>
          if key = key' ∧ condition = condition' then
            some (cast (congrArg (Skel D) sameMid.symm) onTrue',
              cast (congrArg (Skel D) sameMid.symm) onFalse', results', rest')
          else none
      | _, _, _ => none
  | _ => none

/-- The entry of a case analysis: its arms, the leaf of its results, what comes after it. -/
def casesEntry {outs mid payloads : List D.Ty} {t : D.Ty} (key : Key) (w : D.Who)
    (subject : Nat) :
    Option (Skel D outs) → Option (SkelArms D mid payloads × Nat × Skel D outs)
  | some (.cases (mid := mid') (t := t') (payloads := payloads') key' w' subject' _ arms'
      results' rest') =>
      match checks.sameWho w w', checks.sameTy t t', checks.sameTys mid mid',
        checks.sameTys payloads payloads' with
      | isTrue _, isTrue _, isTrue sameMid, isTrue samePayloads =>
          if key = key' ∧ subject = subject' then
            some (cast (by rw [sameMid, samePayloads]) arms', results', rest')
          else none
      | _, _, _, _ => none
  | _ => none

/-- The entry of a loop: the leaf of the inputs of its body, its body, the leaf of its results,
what comes after it. -/
def loopEntry {outs carried each : List D.Ty} (key : Key) (w : D.Who)
    (sameTimes : Count D w → Bool) (initial : List Nat) :
    Option (Skel D outs) → Option (Nat × Skel D (carried ++ each) × Nat × Skel D outs)
  | some (.loop (carried := carried') (each := each') key' w' times' initial' inputs' body'
      results' rest') =>
      match checks.sameWho w w', checks.sameTys carried carried', checks.sameTys each each' with
      | isTrue sameWho, isTrue sameCarried, isTrue sameEach =>
          if key = key' ∧ sameTimes (cast (congrArg (Count D) sameWho.symm) times') = true ∧
              initial = initial' then
            some (inputs', cast (by rw [sameCarried, sameEach]) body', results', rest')
          else none
      | _, _, _ => none
  | _ => none

/-- The entry of a block: its body, the leaf of its results, what comes after it. -/
def blockEntry {outs mid : List D.Ty} (key : Key) (number : Nat) :
    Option (Skel D outs) → Option (Skel D mid × Nat × Skel D outs)
  | some (.block (mid := mid') key' number' body' results' rest') =>
      match checks.sameTys mid mid' with
      | isTrue sameMid =>
          if key = key' ∧ number = number' then
            some (cast (congrArg (Skel D) sameMid.symm) body', results', rest')
          else none
      | isFalse _ => none
  | _ => none

/-- The entry of an attempt: the leaf of its number, its body, the leaf of its results, what
comes after it. -/
def attemptEntry {outs mid : List D.Ty} (key : Key) (w : D.Who) :
    Option (Skel D outs) → Option (Nat × Skel D mid × Nat × Skel D outs)
  | some (.attempt (mid := mid') key' w' input' body' results' rest') =>
      match checks.sameWho w w', checks.sameTys mid mid' with
      | isTrue _, isTrue sameMid =>
          if key = key' then
            some (input', cast (congrArg (Skel D) sameMid.symm) body', results', rest')
          else none
      | _, _ => none
  | _ => none

end

/-- The first of the arms that are followed: the leaf of its payload, its skeleton, the arms
after it. -/
def armEntry {mid payloads : List D.Ty} {payload : D.Ty} :
    Option (SkelArms D mid (payload :: payloads)) →
      Option (Nat × Skel D mid × SkelArms D mid payloads)
  | some (.cons input arm rest) => some (input, arm, rest)
  | none => none

/-! ## The walk -/

section
variable [DecidableEq Raw] (rules : FactRules D Raw) (checks : SkelRules D) (definition : Key)
  (role : Option Role)

/-- A value, once its requirements are decided: its results from the table with its operands in
the table's order, and what its ranges and the types say of them learned. -/
def valueStep (written : Raw) (res : List D.Ty) (argIds : List Nat) (k : Known)
    (st : St D.Ty Raw) : List Nat × Known × St D.Ty Raw :=
  let made := share written (rules.values.order written argIds) res.length st
  let k₁ := k.addRanges made.1 (rules.ops.ranges written (argIds.map k.rangeOf))
  let k₂ := k₁.addOffset rules.ops made.2.table k written argIds made.1
  (made.1, (k₂.addRanges made.1 (res.map rules.range)).enter rules res, made.2)

mutual
  /-- The walk of a term, from a skeleton to follow or none, the identifiers of the names in its
  context, what is known and the state. -/
  def walk (blocks : List (Key × Nat)) :
      {Γ : Ctx D.Ty} → {outs : List D.Ty} → Term D Γ outs → Option (Skel D outs) → Ctx Nat →
        Known → State D.Ty Raw → Exit D Raw outs
    | _, _, .ret xs, followed, ids, k, s =>
        let exit := idsOf ids xs
        ⟨miss ⟨definition, blocks, none, role⟩ followed.isSome
            ((followed.map (retEntry exit)).getD false) s,
          k, exit, kept followed (.ret exit)⟩
    | _, _, .op (res := res) key o args results rest, followed, ids, k, s =>
        let place : Place := ⟨definition, blocks, some key, role⟩
        let argIds := idsOf ids args
        let checked := checkRequirements rules.ops k place (rules.written o) argIds
          (rules.ops.requires (rules.written o)) s.st
        match rules.shared o with
        | true =>
            let step := valueStep rules (rules.written o) res argIds k checked
            walk blocks rest followed (bindIds ids results step.1) step.2.1
              { s with st := step.2.2 }
        | false =>
            let hit := effectEntry checks key o argIds followed
            let s₁ := miss place followed.isSome hit.isSome { s with st := checked }
            let made := leaves (hit.map (·.1)) res.length s₁
            let after := walk blocks rest (hit.map (·.2)) (bindIds ids results made.1)
              ((k.addRanges made.1 (res.map rules.range)).enter rules res) made.2
            { after with skel := kept followed (.effect key o argIds s₁.st.next after.skel) }
    | _, _, .guard (t := t) key w c ok why rest, followed, ids, k, s =>
        let condition := idOf ids c.name
        let hit := guardEntry checks (t := t) key w condition why followed
        let after := walk blocks rest hit ids
          (assume rules.ops s.st.table s.st.next k condition true)
          (miss ⟨definition, blocks, some key, role⟩ followed.isSome hit.isSome s)
        { after with skel := kept followed (.guard key w condition ok why after.skel) }
    | _, _, .choose (mid := mid) (t := t) key w c ok _ onTrue onFalse results rest, followed, ids, k,
        s =>
        let condition := idOf ids c.name
        let hit := chooseEntry checks (mid := mid) (t := t) key w condition followed
        let s₁ := miss ⟨definition, blocks, some key, role⟩ followed.isSome hit.isSome s
        let first := walk blocks onTrue (hit.map (·.1)) ids
          (assume rules.ops s₁.st.table s₁.st.next k condition true) s₁
        let second := walk blocks onFalse (hit.map (·.2.1)) ids
          (assume rules.ops first.state.st.table first.state.st.next k condition false)
          first.state
        let made := leaves (hit.map (·.2.2.1)) mid.length second.state
        let after := walk blocks rest (hit.map (·.2.2.2)) (bindIds ids results made.1)
          ((afterChoice rules k condition first.region second.region made.1 mid).enter
            rules mid) made.2
        { after with skel := kept followed (.choose key w condition ok first.skel second.skel
            second.state.st.next after.skel) }
    | _, _, .cases (mid := mid) (t := t) (payloads := payloads) key w x ok _ arms results rest,
        followed, ids, k, s =>
        let subject := idOf ids x.name
        let hit := casesEntry checks (mid := mid) (t := t) (payloads := payloads) key w subject
          followed
        let s₁ := miss ⟨definition, blocks, some key, role⟩ followed.isSome hit.isSome s
        let regions := walkArms blocks arms (hit.map (·.1)) ids k s₁
        let made := leaves (hit.map (·.2.1)) mid.length regions.state
        let after := walk blocks rest (hit.map (·.2.2)) (bindIds ids results made.1)
          ((afterRegions rules regions.exits k made.1 mid 0).enter rules mid) made.2
        { after with skel := kept followed (.cases key w subject ok regions.skel
            regions.state.st.next after.skel) }
    | _, _, .loop (carried := carried) (each := each) key w times _ init inputs body results rest,
        followed, ids, k, s =>
        let place : Place := ⟨definition, blocks, some key, role⟩
        let initial := idsOf ids init
        let hit := loopEntry checks (carried := carried) (each := each) key w
          (fun count => times.follows checks ids count) initial followed
        let s₁ := miss place followed.isSome hit.isSome s
        let inBody := leaves (hit.map (·.1)) (carried.length + 1) s₁
        let e := walk blocks body (hit.map (·.2.1)) (bindIds ids inputs inBody.1)
          (bodyKnown rules k ids times (inBody.1.headD 0) inBody.1.tail carried) inBody.2
        let recorded : State D.Ty Raw :=
          { e.state with st := recordBound place k ids e.state.st times }
        let made := leaves (hit.map (·.2.2.1)) (carried.length + each.length) recorded
        let k₁ := afterLoop rules e.region k (timesBound k ids times) made.1
          (initial.map k.rangeOf) inBody.1.tail e.rets
          (carried ++ each.map (D.collected times.size))
        let after := walk blocks rest (hit.map (·.2.2.2)) (bindIds ids results made.1)
          (k₁.enter rules (carried ++ each.map (D.collected times.size))) made.2
        { after with skel := kept followed (.loop key w (times.count ids) initial s₁.st.next
            e.skel e.state.st.next after.skel) }
    | _, _, .block (mid := mid) key number body results rest, followed, ids, k, s =>
        let hit := blockEntry checks (mid := mid) key number followed
        let s₁ := miss ⟨definition, blocks, some key, role⟩ followed.isSome hit.isSome s
        let e := walk (blocks ++ [(key, number)]) body (hit.map (·.1)) ids k s₁
        let made := leaves (hit.map (·.2.1)) mid.length e.state
        let after := walk blocks rest (hit.map (·.2.2)) (bindIds ids results made.1)
          ((afterRegions rules [e.region] k made.1 mid 0).enter rules mid) made.2
        { after with skel := kept followed (.block key number e.skel e.state.st.next after.skel) }
    | _, _, .attempt (mid := mid) key w _ inputs body results rest, followed, ids, k, s =>
        let hit := attemptEntry checks (mid := mid) key w followed
        let s₁ := miss ⟨definition, blocks, some key, role⟩ followed.isSome hit.isSome s
        let inBody := leaves (hit.map (·.1)) 1 s₁
        let e := walk blocks body (hit.map (·.2.1)) (bindIds ids inputs inBody.1)
          ((k.addRanges inBody.1 [rules.range (D.index w)]).enter rules [D.index w])
          inBody.2
        let made := leaves (hit.map (·.2.2.1)) mid.length e.state
        let after := walk blocks rest (hit.map (·.2.2.2)) (bindIds ids results made.1)
          ((afterRegions rules [e.region] k made.1 mid 0).enter rules mid) made.2
        { after with skel := kept followed (.attempt key w s₁.st.next e.skel e.state.st.next
            after.skel) }
  /-- The walk of the arms of a case analysis, from the arms to follow or none: each with a leaf
  for its payload, bound to the name of the arm's input. -/
  def walkArms (blocks : List (Key × Nat)) :
      {Γ : Ctx D.Ty} → {mid payloads : List D.Ty} → Arms D Γ mid payloads →
        Option (SkelArms D mid payloads) → Ctx Nat → Known → State D.Ty Raw →
        ArmsExit D Raw mid payloads
    | _, _, _, .nil, _, _, _, s => ⟨[], s, .nil⟩
    | _, _, _, .cons (payload := payload) inputs arm rest, followed, ids, k, s =>
        let hit := armEntry followed
        let made := leaves (hit.map (·.1)) 1 s
        let e := walk blocks arm (hit.map (·.2.1)) (bindIds ids inputs made.1)
          ((k.addRanges made.1 [rules.range payload]).enter rules [payload]) made.2
        let others := walkArms blocks rest (hit.map (·.2.2)) ids k e.state
        ⟨e.region :: others.exits, others.state,
          followed.getD (.cons s.st.next e.skel others.skel)⟩
end

/-! ## A definition, and a second definition that follows it -/

/-- What is known of the inputs of a definition, which have the first identifiers. -/
def start (types : List D.Ty) : Known :=
  (Known.empty.addRanges (List.range types.length) (types.map rules.range)).enter rules
    types

/-- The analysis of a body in the context of its inputs, from the empty table: its skeleton, the
table of its values, every application that is not known to be inside its operation's domain,
and the bound of each loop that runs as often as a count with an upper end. -/
def analyse {types outs : List D.Ty} (inputs : Names types)
    (body : Term D (Ctx.empty.extend inputs) outs) : Exit D Raw outs :=
  walk rules checks definition role [] body none
    (bindIds Ctx.empty inputs (List.range types.length)) (start rules types)
    ⟨⟨Table.empty rules.place, types.length, [], []⟩, []⟩

/-- The analysis of a second body that follows the skeleton of a first, from the table of the
first, with the inputs of both on the same identifiers: the table with the second's values, its
refusals and bounds, and the places where it is not the next entry of the skeleton. -/
def follow {types outs : List D.Ty} (first : Exit D Raw outs) (inputs : Names types)
    (body : Term D (Ctx.empty.extend inputs) outs) : Exit D Raw outs :=
  walk rules checks definition role [] body (some first.skel)
    (bindIds Ctx.empty inputs (List.range types.length)) (start rules types)
    ⟨{ first.state.st with refusals := [], bounds := [] }, []⟩

/-- Whether an analysis refuses nothing and differs nowhere. -/
def Exit.accepted {outs : List D.Ty} (e : Exit D Raw outs) : Bool :=
  e.state.st.refusals.isEmpty && e.state.differs.isEmpty

end

end

end Analysis

open Analysis in
/-- The check of facts of a body in the context of its inputs: every application that the
analysis does not know to be inside its operation's domain, refused at its place; or, when
there is none, the bound of each loop that runs as often as a count with an upper end. -/
def checkFacts {D : Dialect} {Raw : Type} [DecidableEq Raw] (rules : FactRules D Raw)
    (checks : SkelRules D) (definition : Key) (role : Option Role) {types outs : List D.Ty}
    (inputs : Names types) (body : Term D (Ctx.empty.extend inputs) outs) :
    Except (List (Refusal D.Ty Raw)) (List (Place × Nat)) :=
  let found := analyse rules checks definition role inputs body
  match found.state.st.refusals with
  | [] => .ok found.state.st.bounds.reverse
  | refusals => .error refusals.reverse

end Zkc.Core
