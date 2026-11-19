module

public import Zkc.Core.Facts.Body.Skeleton
public import Zkc.Core.Facts.Contracts.Elaboration

@[expose] public section

/-!
The seam of the analysis on the term in steps, part 6: the walk.

One walk of a term in steps, in one mode, by mutual structural recursion on `Term`,
`Instr` and `Arms` (`walk`, `walkInstr`, `walkArms`). It is assembled from what a
dialect gives (`Config`: its rules, a domain, the lemmas that stated steps may name, and the key of
the definition and the role, for places) and reads the definition's annotations (`Annotations`),
which are no part of the term.

**The state.** Every region passes on one record (`State`): the values (the table and the next
value), the number of the next leaf, the refusals and the bounds of loops, the latest first. Beside
it the domain's state. The exit of a region (`Exit`) is the state, the domain's state, the
identifiers that it returns and its skeleton; the exit of an instruction (`InstrExit`) has its
entry of the skeleton, or none.

**Assertions.** Entering an assertion (`enterExpr`) shares its applications in the table in the
order that the table places their operands (`Values.apply` with `rules.commutes`, as many results
as `rules.results` says) and tells the domain of each entry, found or made (`transfer`, asking
nobody). A position with no identifier, an operation that an assertion may not apply
(`rules.assertable`), or a result index out of range makes it "could not be entered", and nothing
that it entered is kept. Deciding a list (`decideAll`): each is entered and its truth asked;
`some true` is known, `some false` and `none` are refused, saying which, and the walk goes on;
nothing is refused in a dead state. Learning a list (`learnAll`): each is entered and assumed true;
one that cannot be entered is skipped.

**Annotations.** At the entry of an instruction, before it, the annotations at its key are taken
in the order written (`atEntry`): a stated step decides each premise of its lemma on the
identifiers of the names given and learns the conclusion; a given fact is learned. An annotation
that names a name with no identifier can enter nothing. The invariant of a loop is read by the
loop (`loopEnter`, `loopExit`).

**Instructions** (`walkInstr`), as the design's section 6 says:

- an operation decides its requirements on its operands; a shared one is shared and the domain
  told (`Config.apply`); one kept in order gets new leaves for its results, told to the domain
  with their types, and an entry of the skeleton; then its guarantees are learned on the operands
  followed by the results (`opStep`);
- a guard assumes its condition true; an entry of the skeleton (`guardStep`);
- a choice walks each region from the state before it with its condition assumed, the first's
  state passing to the second (`chooseRegions`); its results are `Values.selectAll`; the domain's
  `after` with each region whose exit is not dead, then `leaves` with the results' types
  (`chooseExit`);
- a case analysis walks each arm with a new leaf for its payload; its results are new leaves;
  `after`, then `leaves` (`walkArms`, `casesExit`);
- a loop decides its invariant on the initial values with the index's first value
  (`rules.indexAt who 0`), makes leaves for the index and the carried values, `enter`s, learns the
  invariant on those leaves, walks its body once, decides the invariant on the index's successor
  (`rules.indexNext`) and what the body returns, records its bound, makes leaves for its results,
  `afterLoop`, `leaves` with the types of all results, and learns the invariant on the count and
  the carried results (`loopEnter`, `loopExit`);
- a block walks its body, whose results are its own; an attempt makes a leaf for its number,
  walks its body, and makes leaves for its results (`attemptExit`).

A region whose entry state is dead is walked like any other, since leaf numbers depend on the
term's structure only (`Term.leafCount`); the refusals made in it are dropped
(`discount`).

**The analysis** (`analyse`, `analyseFrom`): the inputs are the first leaves, told to the domain
with their types; the summary's requirements are learned on them; the body is walked; the
summary's guarantees are decided where it returns, on the inputs followed by what it returns, at
the definition's place. The check of facts is the refusals, or the bounds (`checkFacts`).
**Comparison** (`compareTerms`): the first term walked from the empty table, the second from the
first's final table with the leaf counter reset; the places where the skeletons differ. `follows`
asks also that the second walk refuse nothing. The walk of a prefix (`walkPrefix`) is the walk of
its instructions one after the other.
-/

namespace Zkc.Core.BodyAnalysis

/-! ## Refusals -/

/-- Why an assertion is refused: the domains know it false, they do not know it, or it could not
be entered. -/
inductive Verdict where
  | knownFalse
  | unknown
  | notEntered
deriving DecidableEq, Repr

/-- What a refused assertion is about. -/
inductive Concern (Raw : Type) where
  /-- A requirement of an application of the written operation. -/
  | requirement (written : Raw)
  /-- The invariant of a loop: on the initial values (`kept` false) or on what the body returns
  (`kept` true). -/
  | invariant (site : AnnotationSite) (annotation : Annotation Raw) (kept : Bool)
  /-- A premise of a stated step, or the step itself when its lemma is not in the list. -/
  | premise (site : AnnotationSite) (annotation : Annotation Raw)
  /-- A guarantee of the summary, where the definition returns. -/
  | guarantee

/-! ## What the analysis of a dialect is assembled from -/

/-- What the analysis of a dialect is assembled from: the rules of the dialect, a domain (a
product of domains is one), the lemmas that a stated step may name, and the key of the definition
and the role, by which places are written. -/
structure Config (D : Dialect) (Raw : Type) where
  rules : Rules D Raw
  domain : Domain D.Ty Raw
  assertions : AssertionTypes D.Ty Raw
  lemmas : List (Lemma D.Ty Raw)
  definition : Key
  role : Option Role
  /-- Inspect the values relevant to a failed condition. The resulting ranges serve diagnostics. -/
  explain : Concern Raw → Nat → List (Option Ident) → Values Raw → domain.State → List (Option Range) :=
    fun _ _ _ _ _ => []

section
variable {D : Dialect} {Raw : Type}

/-- The place of an instruction of the definition, inside the blocks given. -/
def Config.place (cfg : Config D Raw) (blocks : List (Key × Nat)) (key : Key) : Place :=
  ⟨cfg.definition, blocks, some key, cfg.role⟩

/-- The place of the definition's exit: no instruction. -/
def Config.exitPlace (cfg : Config D Raw) : Place :=
  ⟨cfg.definition, [], none, cfg.role⟩

end

/-- A refusal: the place, what it is about, the index of the assertion in its list, the assertion
(none for a step whose lemma is not in the list), and why. -/
structure Refusal (Raw : Type) where
  place : Place
  concern : Concern Raw
  index : Nat
  assertion : Option (Expr Raw)
  verdict : Verdict
  ranges : List (Option Range)

/-! ## The state and the exits -/

/-- What passes through every region: the values (the table and the next value), the number of
the next leaf, the refusals and the bounds of loops found so far (the latest first). -/
structure State (Raw : Type) where
  values : Values Raw
  leaves : Nat
  refusals : List (Refusal Raw)
  bounds : List (Place × Nat)

/-- The state with one more refusal. -/
def State.refuse {Raw : Type} (s : State Raw) (refusal : Refusal Raw) : State Raw :=
  { s with refusals := refusal :: s.refusals }

/-- The exit of a region: the state, the domain's state (`S`), the identifiers that it returns, and
its skeleton. -/
structure Exit (D : Dialect) (Raw S : Type) (outs : List D.Ty) where
  state : State Raw
  known : S
  returned : List Ident
  skel : Skel D outs

/-- The exit of an instruction: the state, the domain's state, the identifiers that it returns, and
its entry of the skeleton, none for a shared operation. -/
structure InstrExit (D : Dialect) (Raw S : Type) where
  state : State Raw
  known : S
  returned : List Ident
  entry : Option (Kept D)

/-- The exit of the arms of a case analysis: the state after the last, each arm whose exit is not
dead with nobody's answers, its exit state and what it returns, and their skeletons. -/
structure ArmsExit (D : Dialect) (Raw S : Type) (mid payloads : List D.Ty) where
  state : State Raw
  exits : List (Asks × S × List Ident)
  skel : SkelArms D mid payloads

/-- The exit of a prefix: the identifiers of the names in scope after it, the state, the domain's
state, and the entries of the skeleton with their keys, in order. -/
structure PrefixExit (D : Dialect) (Raw S : Type) where
  ids : Ctx Ident
  state : State Raw
  known : S
  entries : List (Key × Kept D)

/-! ## The identifiers of names -/

/-- The identifier of a name in scope. In the walk every name in scope has one, so the leaf `0`
of a name without one is never read. -/
def idOf (ids : Ctx Ident) (name : Name) : Ident := (ids.find? name).getD (.leaf 0)

/-- The identifiers of variables. -/
def idsOf {α : Type} {Γ : Ctx α} (ids : Ctx Ident) : {items : List α} → HList (Var Γ) items →
    List Ident
  | [], .nil => []
  | _ :: _, .cons x rest => idOf ids x.name :: idsOf ids rest

/-- The identifiers of the names in scope with the names of a binding bound to identifiers, in
order, a later name hiding an earlier one, as `Ctx.extend` binds them. -/
def bindIds {α : Type} (ids : Ctx Ident) : {types : List α} → Names types → List Ident → Ctx Ident
  | [], .nil, _ => ids
  | _ :: _, .cons name rest, i :: is => bindIds (ids.insert name i) rest is
  | _ :: _, .cons _ _, [] => ids

/-- The positions of an annotation: the identifiers of the names that it lists, when each has
one. -/
def namesAt (ids : Ctx Ident) (names : List Name) : Option (List (Option Ident)) :=
  (names.mapM ids.find?).map (·.map some)

/-! ## Sharing, and telling the domain -/

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw]

/-- The values without entries: no value made yet. -/
def Values.empty (place : Raw → Nat) : Values Raw := ⟨Table.empty place, 0⟩

/-- A written operation applied to operands, shared in the table in the order that the table
places them: the identifiers of the entry that sharing returns, the values, and the domain told of
that entry (asking nobody). -/
def Config.apply (cfg : Config D Raw) (written : Raw) (args : List Ident) (count : Nat)
    (v : Values Raw) (k : cfg.domain.State) : List Ident × Values Raw × cfg.domain.State :=
  let made := v.apply cfg.rules.commutes written args count
  (made.1.ids, made.2, cfg.domain.transfer Asks.nobody made.2.table k made.1)

/-- Enter an assertion's one requested result without materializing the other result IDs. -/
def Config.applyPort (cfg : Config D Raw) (written : Raw) (args : List Ident) (count port : Nat)
    (v : Values Raw) (k : cfg.domain.State) : Option (Ident × Values Raw × cfg.domain.State) :=
  let (e, next) := v.apply cfg.rules.commutes written args count
  if port < e.count then
    some (.val (e.lo + port), next, cfg.domain.transfer Asks.nobody next.table k e)
  else none

/-! ## Entering, deciding and learning assertions -/

mutual
  /-- An assertion entered, its positions the identifiers given: its identifier, the values and the
  domain's state after; nothing when it cannot be entered. -/
  def enterExpr (cfg : Config D Raw) (positions : List (Option Ident)) :
      Expr Raw → Values Raw → cfg.domain.State → Option (Ident × Values Raw × cfg.domain.State)
    | .arg position, v, k =>
        match positions[position]? with
        | some (some id) => some (id, v, k)
        | _ => none
    | .apply written operands result, v, k =>
        match cfg.rules.assertionArity written with
        | none => none
        | some count =>
          match enterExprs cfg positions operands v k with
          | some (args, v', k') => cfg.applyPort written args count result v' k'
          | none => none
  /-- Expressions entered in order: their identifiers; nothing when one cannot be entered. -/
  def enterExprs (cfg : Config D Raw) (positions : List (Option Ident)) :
      Exprs Raw → Values Raw → cfg.domain.State →
        Option (List Ident × Values Raw × cfg.domain.State)
    | .nil, v, k => some ([], v, k)
    | .cons first others, v, k =>
        match enterExpr cfg positions first v k with
        | some (id, v', k') =>
            (enterExprs cfg positions others v' k').map fun (ids, v'', k'') => (id :: ids, v'', k'')
        | none => none
end

/-- Inspect a finite-bound demand in the same table and state as the assertion. Any entries
made solely to query the bound are local to that query. -/
def clauseTruth (cfg : Config D Raw) (positions : List (Option Ident)) (bound : Option (Expr Raw))
    (v : Values Raw) (k : cfg.domain.State) (id : Ident) : Option Bool := do
  let value ← cfg.domain.truth Asks.nobody v.table k id
  if value then
    if let some expr := bound then
      let (x, _, known) ← enterExpr cfg positions expr v k
      guard (((cfg.domain.answers known).upperAt x).isSome)
  return value

/-- Assertions decided in order, from the index given: each is entered and its truth asked;
`some true` is known, `some false` and `none` are refused at the place, saying which, and one that
cannot be entered is refused too; the walk goes on. Nothing is refused in a dead state: the place
cannot be reached. -/
def decideWith {A : Type} (project : A → Expr Raw) (bound : A → Option (Expr Raw)) (cfg : Config D Raw) (place : Place) (concern : Concern Raw)
    (positions : List (Option Ident)) :
    Nat → List A → State Raw → cfg.domain.State → State Raw × cfg.domain.State
  | _, [], s, k => (s, k)
  | index, assertion :: rest, s, k =>
      match enterExpr cfg positions (project assertion) s.values k with
      | some (id, v, k') =>
          let entered := { s with values := v }
          let judged :=
            match cfg.domain.dead k', clauseTruth cfg positions (bound assertion) v k' id with
            | true, _ => entered
            | false, some true => entered
            | false, some false =>
                entered.refuse ⟨place, concern, index, some (project assertion), .knownFalse, cfg.explain concern index positions v k'⟩
            | false, none => entered.refuse ⟨place, concern, index, some (project assertion), .unknown, cfg.explain concern index positions v k'⟩
          decideWith project bound cfg place concern positions (index + 1) rest judged k'
      | none =>
          let judged :=
            if cfg.domain.dead k = true then s
            else s.refuse ⟨place, concern, index, some (project assertion), .notEntered, cfg.explain concern index positions s.values k⟩
          decideWith project bound cfg place concern positions (index + 1) rest judged k

abbrev decideAll (cfg : Config D Raw) (place : Place) (concern : Concern Raw) (positions : List (Option Ident)) :=
  decideWith id (fun _ => none) cfg place concern positions

abbrev decideClauses (cfg : Config D Raw) (place : Place) (concern : Concern Raw) (positions : List (Option Ident)) :=
  decideWith ContractClause.assertion ContractClause.staticBound cfg place concern positions

/-- Assertions that hold, learned in order: each is entered and its identifier assumed true; one
that cannot be entered is skipped. -/
def learnAll (cfg : Config D Raw) (positions : List (Option Ident)) :
    List (Expr Raw) → State Raw → cfg.domain.State → State Raw × cfg.domain.State
  | [], s, k => (s, k)
  | assertion :: rest, s, k =>
      match enterExpr cfg positions assertion s.values k with
      | some (id, v, k') =>
          learnAll cfg positions rest { s with values := v }
            (cfg.domain.assume Asks.nobody v.table k' id true)
      | none => learnAll cfg positions rest s k

/-- Assertions that cannot be entered at all, refused in order from the index given (nothing in a
dead state). -/
def refuseAll (place : Place) (concern : Concern Raw) (dead : Bool) :
    Nat → List (Expr Raw) → State Raw → State Raw
  | _, [], s => s
  | index, assertion :: rest, s =>
      refuseAll place concern dead (index + 1) rest
        (if dead = true then s else s.refuse ⟨place, concern, index, some assertion, .notEntered, []⟩)

/-- Assertions of an annotation decided at its positions; each refused as "could not be entered"
when a name it lists has no identifier. -/
def decideAt (cfg : Config D Raw) (place : Place) (concern : Concern Raw)
    (positions : Option (List (Option Ident))) (assertions : List (Expr Raw)) (s : State Raw)
    (k : cfg.domain.State) : State Raw × cfg.domain.State :=
  match positions with
  | some positions => decideAll cfg place concern positions 0 assertions s k
  | none => (refuseAll place concern (cfg.domain.dead k) 0 assertions s, k)

/-- Assertions of an annotation learned at its positions; none when a name it lists has no
identifier. -/
def learnAt (cfg : Config D Raw) (positions : Option (List (Option Ident)))
    (assertions : List (Expr Raw)) (s : State Raw) (k : cfg.domain.State) :
    State Raw × cfg.domain.State :=
  match positions with
  | some positions => learnAll cfg positions assertions s k
  | none => (s, k)

/-! ## Annotations at the entry of an instruction -/

/-- Diagnostic projection of an annotation entry. A block entry includes its own frame. -/
def AnnotationSite.place (site : AnnotationSite) (cfg : Config D Raw) : Place :=
  site.toPlace cfg.definition cfg.role

/-- The annotations at an instruction, in the order written, at its entry: a stated step decides
each premise of its lemma on the identifiers of the names given and learns the conclusion (a step
whose lemma is not in the list is refused); a given fact is learned; an invariant is the loop's. -/
def annotate (cfg : Config D Raw) (site : AnnotationSite) (ids : Ctx Ident) :
    List (Annotation Raw) → State Raw → cfg.domain.State → State Raw × cfg.domain.State
  | [], s, k => (s, k)
  | .invariant _ _ :: rest, s, k => annotate cfg site ids rest s k
  | .step lemma names :: rest, s, k =>
      match cfg.lemmas[lemma]? with
      | some l =>
          let decided := decideAt cfg (site.place cfg) (.premise site (.step lemma names)) (namesAt ids names)
            l.premises s k
          let learned := learnAt cfg (namesAt ids names) [l.conclusion] decided.1 decided.2
          annotate cfg site ids rest learned.1 learned.2
      | none =>
          annotate cfg site ids rest
            (if cfg.domain.dead k = true then s
              else s.refuse ⟨(site.place cfg), .premise site (.step lemma names), 0, none, .notEntered, []⟩) k
  | .fact uses assertion :: rest, s, k =>
      let learned := learnAt cfg (namesAt ids uses) [assertion] s k
      annotate cfg site ids rest learned.1 learned.2

/-- Apply the annotations resolved to this entry, in the incoming environment. -/
def atEntry (cfg : Config D Raw) (notes : Annotations Raw) (site : AnnotationSite)
    (ids : Ctx Ident) (s : State Raw) (k : cfg.domain.State) : State Raw × cfg.domain.State :=
  annotate cfg site ids (notes.at_ site) s k

/-! ## Regions -/

/-- The state after a region: with the refusals of before it when its entry state is dead, so that
what is refused where nothing runs does not count. -/
def discount (cfg : Config D Raw) (entry : cfg.domain.State) (before after : State Raw) :
    State Raw :=
  if cfg.domain.dead entry = true then { after with refusals := before.refusals } else after

/-- A region's exit as `after` is told of it: none when its exit state is dead. -/
def live (cfg : Config D Raw) (known : cfg.domain.State) (returned : List Ident) :
    List (Asks × cfg.domain.State × List Ident) :=
  if cfg.domain.dead known = true then [] else [(Asks.nobody, known, returned)]

/-! ## The kinds of instruction, but for their regions -/

/-- Type the results and transfer any reading certified by the operation. Shared slots and
ordered result leaves use the same domain action. -/
def Config.resultFacts (cfg : Config D Raw) {ins res} (o : D.Op ins res) (table : Table Raw)
    (k : cfg.domain.State) (args made : List Ident) : cfg.domain.State :=
  let typed := cfg.domain.leaves k (made.zip res)
  match cfg.rules.observedOperand o with
  | none => typed
  | some i =>
    match args[i]?, made[0]? with
    | some source, some result => cfg.domain.observe Asks.nobody table typed source result
    | _, _ => typed

/-- Form argument positions only when an operation has requirements to decide. -/
@[inline] def decideRequirements (cfg : Config D Raw) (place : Place) (written : Raw)
    (args : List Ident) (requirements : List (ContractClause Raw)) (s : State Raw)
    (k : cfg.domain.State) : State Raw × cfg.domain.State :=
  match requirements with
  | [] => (s, k)
  | _ :: _ => decideClauses cfg place (.requirement written) (args.map some) 0 requirements s k

theorem decideRequirements_eq (cfg : Config D Raw) (place : Place) (written : Raw)
    (args : List Ident) (requirements : List (ContractClause Raw)) (s : State Raw)
    (k : cfg.domain.State) :
    decideRequirements cfg place written args requirements s k =
      decideClauses cfg place (.requirement written) (args.map some) 0 requirements s k := by
  cases requirements <;> rfl

/-- Build the combined input and result positions only when a clause can read them. -/
@[inline] def learnGuarantees (cfg : Config D Raw) (args results : List Ident)
    (contract : Contract Raw) (s : State Raw) (k : cfg.domain.State) :
    State Raw × cfg.domain.State :=
  match contract.postconditions with
  | [] => (s, k)
  | _ :: _ => learnAll cfg ((args ++ results).map some) contract.ensures s k

theorem learnGuarantees_eq (cfg : Config D Raw) (args results : List Ident)
    (contract : Contract Raw) (s : State Raw) (k : cfg.domain.State) :
    learnGuarantees cfg args results contract s k =
      learnAll cfg ((args ++ results).map some) contract.ensures s k := by
  cases contract with | mk pre post => cases post <;> rfl

/-- An operation, from the state at its entry: its requirements decided on its operands; a shared
one shared and the domain told; one kept in order with new leaves for its results, and its entry of the
skeleton; the results of either told to the domain with their types; then its guarantees learned on its
operands followed by its results. A program's operation has as many results as its type says. -/
def opStep (cfg : Config D Raw) (place : Place) {ins res : List D.Ty} (o : D.Op ins res)
    (args : List Ident) (s : State Raw) (k : cfg.domain.State) :
    InstrExit D Raw cfg.domain.State :=
  let written := cfg.rules.written o
  let contract := cfg.rules.contract written
  let decided := decideRequirements cfg place written args contract.preconditions s k
  if cfg.rules.shared o = true then
    let made := cfg.apply written args res.length decided.1.values decided.2
    let learned := learnGuarantees cfg args made.1 contract
      { decided.1 with values := made.2.1 } (cfg.resultFacts o made.2.1.table made.2.2 args made.1)
    ⟨learned.1, learned.2, made.1, none⟩
  else
    let made := Ident.leaves decided.1.leaves res.length
    let learned := learnGuarantees cfg args made contract
      { decided.1 with leaves := decided.1.leaves + res.length }
      (cfg.resultFacts o decided.1.values.table decided.2 args made)
    ⟨learned.1, learned.2, made, some (.effect o args decided.1.leaves)⟩

/-- A guard, from the state at its entry: its condition assumed true after it; its entry of the
skeleton. -/
def guardStep (cfg : Config D Raw) {t : D.Ty} (w : D.Who) (condition : Ident)
    (ok : D.Condition w t) (why : Reason) (s : State Raw) (k : cfg.domain.State) :
    InstrExit D Raw cfg.domain.State :=
  ⟨s, cfg.domain.assume Asks.nobody s.values.table k condition true, [],
    some (.guard w condition ok why)⟩

/-- What the walk of a choice has after its two regions: the exit of the first, the exit of the
second, and the state after both, from which `chooseExit` goes on. -/
structure ChooseRegions (D : Dialect) (Raw S : Type) (mid : List D.Ty) where
  first : Exit D Raw S mid
  second : Exit D Raw S mid
  state : State Raw

/-- The two regions of a choice, once the first is walked (`first`) from the state at the choice's
entry (`entry`) with its condition assumed true (`trueKnown`): the first's refusals dropped when
`trueKnown` is dead; the second walked (`second`, from its entry state and the domain's state)
from the state after the first, with the condition assumed false in the domain's state at the
choice's entry (`known`); and its refusals dropped when that is dead. -/
def chooseRegions (cfg : Config D Raw) {mid : List D.Ty} (condition : Ident) (entry : State Raw)
    (known trueKnown : cfg.domain.State) (first : Exit D Raw cfg.domain.State mid)
    (second : State Raw → cfg.domain.State → Exit D Raw cfg.domain.State mid) :
    ChooseRegions D Raw cfg.domain.State mid :=
  let afterFirst := discount cfg trueKnown entry first.state
  let falseKnown := cfg.domain.assume Asks.nobody afterFirst.values.table known condition false
  let walked := second afterFirst falseKnown
  ⟨first, walked, discount cfg falseKnown afterFirst walked.state⟩

/-- A choice, once its regions are walked (`s` the state after both): its results the selections
of what the regions return; the domain's `after` with each region whose exit is not dead, then
`leaves` with the results' types; its entry of the skeleton. -/
def chooseExit (cfg : Config D Raw) {mid : List D.Ty} {t : D.Ty} (w : D.Who) (condition : Ident)
    (ok : D.Condition w t) (before : cfg.domain.State)
    (first second : Exit D Raw cfg.domain.State mid) (s : State Raw) :
    InstrExit D Raw cfg.domain.State :=
  let chosen := Values.selectAll condition first.returned second.returned s.values
  let exits := live cfg first.known first.returned ++ live cfg second.known second.returned
  ⟨{ s with values := chosen.2 },
    cfg.domain.leaves (cfg.domain.after chosen.2.table before exits chosen.1) (chosen.1.zip mid),
    chosen.1, some (.choose w condition ok first.skel second.skel)⟩

/-- A case analysis, once its arms are walked: new leaves for its results; the domain's `after`
with each arm whose exit is not dead, then `leaves` with the results' types; its entry of the
skeleton. -/
def casesExit (cfg : Config D Raw) {mid payloads : List D.Ty} {t : D.Ty} (w : D.Who)
    (subject : Ident) (ok : D.Alternatives w t payloads) (before : cfg.domain.State)
    (arms : ArmsExit D Raw cfg.domain.State mid payloads) : InstrExit D Raw cfg.domain.State :=
  let made := Ident.leaves arms.state.leaves mid.length
  ⟨{ arms.state with leaves := arms.state.leaves + mid.length },
    cfg.domain.leaves (cfg.domain.after arms.state.values.table before arms.exits made)
      (made.zip mid),
    made, some (.cases w subject ok arms.skel arms.state.leaves)⟩

/-- An attempt, once its body is walked from `bodyState` and the domain's `bodyKnown`: new leaves
for its results; the domain's `after` with the body's exit if it is not dead, then `leaves` with
the results' types; its entry of the skeleton. -/
def attemptExit (cfg : Config D Raw) {mid : List D.Ty} (w : D.Who) (before : cfg.domain.State)
    (input : Nat) (bodyKnown : cfg.domain.State) (bodyState : State Raw)
    (body : Exit D Raw cfg.domain.State mid) : InstrExit D Raw cfg.domain.State :=
  let ended := discount cfg bodyKnown bodyState body.state
  let made := Ident.leaves ended.leaves mid.length
  ⟨{ ended with leaves := ended.leaves + mid.length },
    cfg.domain.leaves (cfg.domain.after ended.values.table before
      (live cfg body.known body.returned) made) (made.zip mid),
    made, some (.attempt w input body.skel ended.leaves)⟩

/-! ## A loop -/

/-- How often a loop runs, on the identifier of its count. -/
def countOf {w : D.Who} {Γ : Ctx D.Ty} (ids : Ctx Ident) : Times D w Γ → Count D w
  | .fixed n => .fixed n
  | .value count ok => .value (idOf ids count.name) ok

/-- How often a loop runs, as a domain is told of it. -/
def Count.told {w : D.Who} : Count D w → Nat ⊕ Ident
  | .fixed n => .inl n
  | .value id _ => .inr id

/-- Enter the dialect's index expression using ordinary sharing and domain transfer.
A direct argument aliases its existing identifier. -/
def indexValue (cfg : Config D Raw) (expression : Option (Expr Raw)) (args : List Ident)
    (s : State Raw) (k : cfg.domain.State) : Option Ident × State Raw × cfg.domain.State :=
  match expression.bind (fun e => enterExpr cfg (args.map some) e s.values k) with
  | some (id, values, known) => (some id, { s with values }, known)
  | none => (none, s, k)

/-- The invariants at a key: the names that each lists and its assertions. -/
def Annotations.invariantsAt (notes : Annotations Raw) (site : AnnotationSite) :
    List (List Name × List (Expr Raw)) :=
  (notes.at_ site).filterMap fun
    | .invariant uses assertions => some (uses, assertions)
    | _ => none

/-- The positions of an invariant: the identifiers of the names that it lists, then the index
(none where it has no identifier), then the carried values; nothing when a name has no
identifier. -/
def invariantPositions (ids : Ctx Ident) (uses : List Name) (index : Option Ident)
    (carried : List Ident) : Option (List (Option Ident)) :=
  (namesAt ids uses).map fun named => named ++ index :: carried.map some

/-- The invariants decided at the index and carried values given; `kept` says which decision it
is. -/
def decideInvariants (cfg : Config D Raw) (site : AnnotationSite) (kept : Bool) (ids : Ctx Ident)
    (index : Option Ident) (carried : List Ident) :
    List (List Name × List (Expr Raw)) → State Raw → cfg.domain.State →
      State Raw × cfg.domain.State
  | [], s, k => (s, k)
  | (uses, assertions) :: rest, s, k =>
      let decided := decideAt cfg (site.place cfg) (.invariant site (.invariant uses assertions) kept)
        (invariantPositions ids uses index carried) assertions s k
      decideInvariants cfg site kept ids index carried rest decided.1 decided.2

/-- The invariants learned at the index and carried values given. -/
def learnInvariants (cfg : Config D Raw) (ids : Ctx Ident) (index : Option Ident)
    (carried : List Ident) :
    List (List Name × List (Expr Raw)) → State Raw → cfg.domain.State →
      State Raw × cfg.domain.State
  | [], s, k => (s, k)
  | (uses, assertions) :: rest, s, k =>
      let learned := learnAt cfg (invariantPositions ids uses index carried) assertions s k
      learnInvariants cfg ids index carried rest learned.1 learned.2

/-- The state with the bound of a loop as often as a count, when the domains' answer gives an
upper bound of the count's identifier. -/
def recordBound {w : D.Who} (place : Place) (answers : Asks) : Count D w → State Raw → State Raw
  | .value id _, s =>
      match answers.upperAt id with
      | some bound => { s with bounds := (place, bound) :: s.bounds }
      | none => s
  | .fixed _, s => s

/-- A loop as the domain is told of it, its index on the leaf `index` and its carried values on the
leaves after it: how often it runs, the index's type and whether the index reads as the number of
the iteration (the rules say), the initial identifiers, and the types of the carried values. -/
def Loop.told (rules : Rules D Raw) (carried : List D.Ty) {w : D.Who} (count : Count D w)
    (initial : List Ident) (index : Nat) : Loop D.Ty :=
  ⟨count.told, .leaf index, D.index w, rules.numbered w, initial,
    Ident.leaves (index + 1) carried.length, carried⟩

/-- Enter the final index in the post-loop state. Fixed counts construct a typed literal.
A value count supplies the operand of the conversion certified for its count type. -/
def Count.finalIndex (cfg : Config D Raw) {w : D.Who} (count : Count D w) (s : State Raw)
    (k : cfg.domain.State) : Option Ident × State Raw × cfg.domain.State :=
  match count with
  | .fixed n => indexValue cfg (cfg.rules.indexAt w n) [] s k
  | .value id ok => indexValue cfg (cfg.rules.indexFromCount ok) [id] s k

/-- What the walk of a loop has before its body: the state after the invariant is decided on the
initial values, the domain's state there (the state before the loop, for `enter` and
`afterLoop`), the loop as the domain is told of it, and the state and the domain's state at the
body's entry. -/
structure LoopEntry (D : Dialect) (Raw S : Type) where
  decided : State Raw
  before : S
  loop : Loop D.Ty
  body : State Raw
  known : S

/-- A loop before its body, from the state at its entry: its invariant decided on the initial
identifiers with the index's first value (none when the rules give no operation for it); leaves
for the index and the carried values; the domain's `enter`; the invariant learned on those
leaves. -/
def loopEnter (cfg : Config D Raw) (notes : Annotations Raw) (cursor : StaticCursor) (key : Key)
    {Γ : Ctx D.Ty} (carried : List D.Ty) (w : D.Who) (times : Times D w Γ) (initial : List Ident)
    (ids : Ctx Ident) (s : State Raw) (k : cfg.domain.State) : LoopEntry D Raw cfg.domain.State :=
  let invariants := notes.invariantsAt (.instruction cursor key)
  let first := indexValue cfg (cfg.rules.indexAt w 0) [] s k
  let decided := decideInvariants cfg (.instruction cursor key) false ids first.1 initial invariants first.2.1 first.2.2
  let loop := Loop.told cfg.rules carried (countOf ids times) initial decided.1.leaves
  let learned := learnInvariants cfg ids (some loop.index) loop.carried invariants
    { decided.1 with leaves := decided.1.leaves + (carried.length + 1) }
    (cfg.domain.enter Asks.nobody decided.1.values.table decided.2 loop)
  ⟨decided.1, decided.2, loop, learned.1, learned.2⟩

/-- A loop after its body is walked once: the invariant decided on the index's successor (none
when the rules give no operation for it) and the carried part of what the body returns; the
refusals of the body and of that decision dropped when the body's entry state is dead; the bound
recorded from the domains' answer before the loop; leaves for the results; the domain's
`afterLoop` with the carried part of what the body returns and the carried results' leaves, then
`leaves` with the types of all results; the final index entered at the post-loop state; the
invariant learned on that index and the carried results; its entry of the
skeleton. -/
def loopExit (cfg : Config D Raw) (notes : Annotations Raw) (cursor : StaticCursor) (key : Key)
    {Γ : Ctx D.Ty} (carried each : List D.Ty) (w : D.Who) (times : Times D w Γ)
    (initial : List Ident) (ids : Ctx Ident) (entry : LoopEntry D Raw cfg.domain.State)
    (body : Exit D Raw cfg.domain.State (carried ++ each)) : InstrExit D Raw cfg.domain.State :=
  let invariants := notes.invariantsAt (.instruction cursor key)
  let returned := body.returned.take carried.length
  let next := indexValue cfg (cfg.rules.indexNext w) [entry.loop.index] body.state body.known
  let kept := decideInvariants cfg (.instruction cursor key) true ids next.1 returned invariants next.2.1 next.2.2
  let ended := discount cfg entry.known entry.body kept.1
  let recorded := recordBound (cfg.place cursor.blocks key) (cfg.domain.answers entry.before) (countOf ids times) ended
  let made := Ident.leaves recorded.leaves (carried.length + each.length)
  let types := carried ++ each.map (D.collected times.size)
  let after := cfg.domain.leaves
    (cfg.domain.afterLoop Asks.nobody Asks.nobody recorded.values.table entry.before entry.loop
      body.known returned (made.take carried.length))
    (made.zip types)
  let final := (countOf ids times).finalIndex cfg
    { recorded with leaves := recorded.leaves + (carried.length + each.length) } after
  let learned := learnInvariants cfg ids final.1 (made.take carried.length) invariants
    final.2.1 final.2.2
  ⟨learned.1, learned.2, made,
    some (.loop w (countOf ids times) initial entry.decided.leaves body.skel recorded.leaves)⟩

/-! ## The walk -/

mutual
  /-- The walk of a term, from the identifiers of the names in its context, the state and the
  domain's state. -/
  def walk (cfg : Config D Raw) (notes : Annotations Raw) (cursor : StaticCursor) :
      {Γ : Ctx D.Ty} → {outs : List D.Ty} → Term D Γ outs → Ctx Ident → State Raw →
        cfg.domain.State → Exit D Raw cfg.domain.State outs
    | _, _, .ret exit, ids, s, k => ⟨s, k, idsOf ids exit, .ret (idsOf ids exit)⟩
    | _, _, .step key i results rest, ids, s, k =>
        let one := walkInstr cfg notes cursor key i ids s k
        let after := walk cfg notes cursor.next rest (bindIds ids results one.returned) one.state
          one.known
        { after with skel := Skel.stepOf key one.entry after.skel }
  /-- The walk of the instruction at a key, with the annotations at its entry. -/
  def walkInstr (cfg : Config D Raw) (notes : Annotations Raw) (cursor : StaticCursor)
      (key : Key) :
      {Γ : Ctx D.Ty} → {mid : List D.Ty} → Instr D Γ mid → Ctx Ident → State Raw →
        cfg.domain.State → InstrExit D Raw cfg.domain.State
    | _, _, .op o operands, ids, s, k =>
        let entry := atEntry cfg notes (.instruction cursor key) ids s k
        opStep cfg (cfg.place cursor.blocks key) o (idsOf ids operands) entry.1 entry.2
    | _, _, .guard w c ok why, ids, s, k =>
        let entry := atEntry cfg notes (.instruction cursor key) ids s k
        guardStep cfg w (idOf ids c.name) ok why entry.1 entry.2
    | _, _, .choose w c ok _ onTrue onFalse, ids, s, k =>
        let entry := atEntry cfg notes (.instruction cursor key) ids s k
        let condition := idOf ids c.name
        let trueKnown := cfg.domain.assume Asks.nobody entry.1.values.table entry.2 condition true
        let first := walk cfg notes (cursor.region key) onTrue ids entry.1 trueKnown
        let regions := chooseRegions cfg condition entry.1 entry.2 trueKnown first
          (walk cfg notes (cursor.otherwise key) onFalse ids)
        chooseExit cfg w condition ok entry.2 regions.first regions.second regions.state
    | _, _, .cases w x ok _ arms, ids, s, k =>
        let entry := atEntry cfg notes (.instruction cursor key) ids s k
        casesExit cfg w (idOf ids x.name) ok entry.2
          (walkArms cfg notes (cursor.region key) arms ids entry.1 entry.2)
    | _, _, .loop (carried := carried) (each := each) w times _ init inputs body, ids, s, k =>
        let entry := atEntry cfg notes (.instruction cursor key) ids s k
        let entered := loopEnter cfg notes cursor key carried w times
          (idsOf ids init) ids entry.1 entry.2
        let inner := walk cfg notes (cursor.region key) body
          (bindIds ids inputs (entered.loop.index :: entered.loop.carried)) entered.body
          entered.known
        loopExit cfg notes cursor key carried each w times (idsOf ids init) ids
          entered inner
    | _, _, .block number body, ids, s, k =>
        let entry := atEntry cfg notes (.block cursor key number) ids s k
        let inner := walk cfg notes (cursor.block key number) body ids entry.1 entry.2
        ⟨discount cfg entry.2 entry.1 inner.state, inner.known, inner.returned,
          some (.block number inner.skel)⟩
    | _, _, .attempt w _ inputs body, ids, s, k =>
        let entry := atEntry cfg notes (.instruction cursor key) ids s k
        let input := entry.1.leaves
        let bodyKnown := cfg.domain.leaves entry.2 [(.leaf input, D.index w)]
        let bodyState := { entry.1 with leaves := input + 1 }
        let inner := walk cfg notes (cursor.region key) body (bindIds ids inputs [.leaf input]) bodyState
          bodyKnown
        attemptExit cfg w entry.2 input bodyKnown bodyState inner
  /-- The walk of the arms of a case analysis: each from the state after the one before, with a
  new leaf for its payload, told to the domain with its type. -/
  def walkArms (cfg : Config D Raw) (notes : Annotations Raw) (cursor : StaticCursor) :
      {Γ : Ctx D.Ty} → {mid payloads : List D.Ty} → Arms D Γ mid payloads → Ctx Ident →
        State Raw → cfg.domain.State → ArmsExit D Raw cfg.domain.State mid payloads
    | _, _, _, .nil, _, s, _ => ⟨s, [], .nil⟩
    | _, _, _, .cons (payload := payload) inputs arm rest, ids, s, k =>
        let input := s.leaves
        let armKnown := cfg.domain.leaves k [(.leaf input, payload)]
        let armState := { s with leaves := input + 1 }
        let inner := walk cfg notes cursor.arm arm (bindIds ids inputs [.leaf input]) armState armKnown
        let others := walkArms cfg notes cursor.next rest ids (discount cfg armKnown armState inner.state)
          k
        ⟨others.state, live cfg inner.known inner.returned ++ others.exits,
          .cons input inner.skel others.skel⟩
end

/-- Static location of the continuation after all instructions of a prefix. -/
def Prefix.afterCursor {Γ Δ : Ctx D.Ty} (p : Prefix D Γ Δ) (cursor : StaticCursor) : StaticCursor :=
  match p with
  | .nil => cursor
  | .step _ _ _ rest => Prefix.afterCursor rest cursor.next

/-- The walk of a prefix: its instructions one after the other. -/
def walkPrefix (cfg : Config D Raw) (notes : Annotations Raw) (cursor : StaticCursor) :
    {Γ Δ : Ctx D.Ty} → Prefix D Γ Δ → Ctx Ident → State Raw → cfg.domain.State →
      PrefixExit D Raw cfg.domain.State
  | _, _, .nil, ids, s, k => ⟨ids, s, k, []⟩
  | _, _, .step key i results rest, ids, s, k =>
      let one := walkInstr cfg notes cursor key i ids s k
      let after := walkPrefix cfg notes cursor.next rest (bindIds ids results one.returned) one.state
        one.known
      { after with entries := (one.entry.map fun kept => (key, kept)).toList ++ after.entries }

end

/-- A skeleton with entries before it, in order. -/
def Skel.ofEntries {D : Dialect} {outs : List D.Ty} : List (Key × Kept D) → Skel D outs →
    Skel D outs
  | [], rest => rest
  | (key, kept) :: entries, rest => .step key kept (Skel.ofEntries entries rest)

/-! ## How many leaves a term takes -/

section
variable {D : Dialect} {Raw : Type} (rules : Rules D Raw)

mutual
  /-- How many leaves the walk of a term makes: by its structure and the rules' `shared` alone,
  not by what is known, by which regions can run or by how many values are shared. -/
  def Term.leafCount : {Γ : Ctx D.Ty} → {outs : List D.Ty} → Term D Γ outs → Nat
    | _, _, .ret _ => 0
    | _, _, .step _ i _ rest => Instr.leafCount i + Term.leafCount rest
  /-- How many leaves the walk of an instruction makes: an operation kept in order, its results; a
  choice, its regions'; a case analysis, each arm's payload and its own, and its results; a loop,
  its index and carried values, its body's, and its results; a block, its body's; an attempt, its
  number, its body's, and its results. -/
  def Instr.leafCount : {Γ : Ctx D.Ty} → {mid : List D.Ty} → Instr D Γ mid → Nat
    | _, _, .op (res := res) o _ => if rules.shared o = true then 0 else res.length
    | _, _, .guard .. => 0
    | _, _, .choose _ _ _ _ onTrue onFalse =>
        Term.leafCount onTrue + Term.leafCount onFalse
    | _, _, .cases (mid := mid) _ _ _ _ arms => Arms.leafCount arms + mid.length
    | _, _, .loop (carried := carried) (each := each) _ _ _ _ _ body =>
        (carried.length + 1) + Term.leafCount body + (carried.length + each.length)
    | _, _, .block _ body => Term.leafCount body
    | _, _, .attempt (mid := mid) _ _ _ body => 1 + Term.leafCount body + mid.length
  /-- How many leaves the walk of arms makes: each arm's payload and its own. -/
  def Arms.leafCount : {Γ : Ctx D.Ty} → {mid payloads : List D.Ty} →
      Arms D Γ mid payloads → Nat
    | _, _, _, .nil => 0
    | _, _, _, .cons _ arm rest => 1 + Term.leafCount arm + Arms.leafCount rest
end

/-- How many leaves the walk of a prefix makes. -/
def Prefix.leafCount : {Γ Δ : Ctx D.Ty} → Prefix D Γ Δ → Nat
  | _, _, .nil => 0
  | _, _, .step _ i _ rest => Instr.leafCount rules i + Prefix.leafCount rest

end

/-! ## The analysis of a definition, and comparison -/

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw]

/-- The analysis of a body in the context of its inputs, under a summary, from the values given:
the inputs are the first leaves, told to the domain with their types; the summary's requirements
are learned on them; the body is walked; the summary's guarantees are decided where it returns, on
the inputs followed by what it returns, at the definition's place. -/
def analyseFrom (cfg : Config D Raw) (notes : Annotations Raw) {types outs : List D.Ty}
    (summary : Contract Raw) (inputs : Names types)
    (body : Term D (Ctx.empty.extend inputs) outs) (start : Values Raw) :
    Exit D Raw cfg.domain.State outs :=
  let leaves := Ident.leaves 0 types.length
  let learned := learnAll cfg (leaves.map some) summary.requires ⟨start, types.length, [], []⟩
    (cfg.domain.leaves cfg.domain.init (leaves.zip types))
  let walked := walk cfg notes .root body (bindIds Ctx.empty inputs leaves) learned.1 learned.2
  let decided := decideClauses cfg cfg.exitPlace .guarantee ((leaves ++ walked.returned).map some) 0
    summary.postconditions walked.state walked.known
  { walked with state := decided.1, known := decided.2 }

/-- The analysis of a body from the empty table. -/
def analyse (cfg : Config D Raw) (notes : Annotations Raw) {types outs : List D.Ty}
    (summary : Contract Raw) (inputs : Names types)
    (body : Term D (Ctx.empty.extend inputs) outs) : Exit D Raw cfg.domain.State outs :=
  analyseFrom cfg notes summary inputs body (Values.empty cfg.rules.place)

abbrev Diagnostics (Raw : Type) := List (Refusal Raw) × List (Place × Nat)

def State.diagnostics (s : State Raw) : Diagnostics Raw := (s.refusals, s.bounds)

private theorem learnAll_diagnostics (cfg : Config D Raw) (positions : List (Option Ident)) :
    ∀ (es : List (Expr Raw)) (s : State Raw) (k : cfg.domain.State),
      (learnAll cfg positions es s k).1.diagnostics = s.diagnostics
  | [], _, _ => rfl
  | e :: es, s, k => by
    unfold learnAll
    split <;> exact learnAll_diagnostics cfg positions es _ _

/-- In the final operation of an admission walk, only annotations and requirements can add
diagnostics. Its typed results, learned guarantees and skeleton have no remaining reader. -/
def finalDiagnostics (cfg : Config D Raw) (notes : Annotations Raw)
    (cursor : StaticCursor) (key : Key) {Γ mid} (i : Instr D Γ mid)
    (ids : Ctx Ident) (s : State Raw) (k : cfg.domain.State) : Diagnostics Raw :=
  match i with
  | .op op operands =>
    let e := atEntry cfg notes (.instruction cursor key) ids s k
    let written := cfg.rules.written op
    (decideClauses cfg (cfg.place cursor.blocks key) (.requirement written)
      ((idsOf ids operands).map some) 0 (cfg.rules.contract written).preconditions e.1 e.2).1.diagnostics
  | other => (walkInstr cfg notes cursor key other ids s k).state.diagnostics

private theorem finalDiagnostics_eq (cfg : Config D Raw) (notes : Annotations Raw)
    (cursor : StaticCursor) (key : Key) {Γ mid} (i : Instr D Γ mid)
    (ids : Ctx Ident) (s : State Raw) (k : cfg.domain.State) :
    finalDiagnostics cfg notes cursor key i ids s k =
      (walkInstr cfg notes cursor key i ids s k).state.diagnostics := by
  cases i <;> try rfl
  simp only [finalDiagnostics, walkInstr, opStep, decideRequirements_eq, learnGuarantees_eq]
  split <;> rw [learnAll_diagnostics] <;> rfl

/-- Collect the two public lists at return. Every interior instruction uses the ordinary walk. -/
def walkDiagnostics (cfg : Config D Raw) (notes : Annotations Raw)
    (cursor : StaticCursor) : {Γ : Ctx D.Ty} → {outs : List D.Ty} → Term D Γ outs →
    Ctx Ident → State Raw → cfg.domain.State → Diagnostics Raw
  | _, _, .ret _, _, s, _ => s.diagnostics
  | _, _, .step key i results rest, ids, s, k =>
    match rest with
    | .ret _ => finalDiagnostics cfg notes cursor key i ids s k
    | .step .. =>
      let one := walkInstr cfg notes cursor key i ids s k
      walkDiagnostics cfg notes cursor.next rest (bindIds ids results one.returned) one.state one.known

private theorem walkDiagnostics_eq (cfg : Config D Raw) (notes : Annotations Raw)
    (cursor : StaticCursor) : ∀ {Γ outs} (body : Term D Γ outs) ids s k,
    walkDiagnostics cfg notes cursor body ids s k = (walk cfg notes cursor body ids s k).state.diagnostics
  | _, _, .ret _, _, _, _ => rfl
  | _, _, .step key i results rest, ids, s, k => by
    cases rest with
    | ret => exact finalDiagnostics_eq cfg notes cursor key i ids s k
    | step => exact walkDiagnostics_eq cfg notes cursor.next _ _ _ _

def analyseDiagnostics (cfg : Config D Raw) (notes : Annotations Raw) {types outs}
    (summary : Contract Raw) (inputs : Names types) (body : Term D (Ctx.empty.extend inputs) outs) :
    Diagnostics Raw :=
  match summary.postconditions with
  | [] =>
    let leaves := Ident.leaves 0 types.length
    let learned := learnAll cfg (leaves.map some) summary.requires
      ⟨Values.empty cfg.rules.place, types.length, [], []⟩
      (cfg.domain.leaves cfg.domain.init (leaves.zip types))
    walkDiagnostics cfg notes .root body (bindIds Ctx.empty inputs leaves) learned.1 learned.2
  | _ :: _ => (analyse cfg notes summary inputs body).state.diagnostics

theorem analyseDiagnostics_eq (cfg : Config D Raw) (notes : Annotations Raw) {types outs}
    (summary : Contract Raw) (inputs : Names types) (body : Term D (Ctx.empty.extend inputs) outs) :
    analyseDiagnostics cfg notes summary inputs body =
      ((analyse cfg notes summary inputs body).state.refusals,
       (analyse cfg notes summary inputs body).state.bounds) := by
  unfold analyseDiagnostics
  split
  · rename_i empty
    rw [walkDiagnostics_eq]
    simp only [analyse, analyseFrom, empty, decideClauses, decideWith, State.diagnostics]
  · rfl

inductive FactCheckError (Raw : Type) where
  | definition (reason : DefinitionCheckError)
  | refused (reasons : List (Refusal Raw))

/-- The check of facts of a body: its refusals, in the order found, or, when there is none, the
bound of each loop that runs as often as a count with an upper bound. -/
def checkFacts [DecidableEq D.Ty] (cfg : Config D Raw) (notes : Annotations Raw) {types outs : List D.Ty}
    (summary : Contract Raw) (inputs : Names types)
    (body : Term D (Ctx.empty.extend inputs) outs)
    (contractOK : {b : Bool // b = Contract.check (D := D) cfg.assertions summary types outs} := ⟨_, rfl⟩) :
    Except (FactCheckError Raw) (List (Place × Nat)) := do
  (checkDefinition cfg.assertions cfg.lemmas inputs body notes summary contractOK).mapError FactCheckError.definition
  let found := analyseDiagnostics cfg notes summary inputs body
  match found.1 with
  | [] => .ok found.2.reverse
  | refusals => .error (.refused refusals.reverse)

/-- The two walks of a comparison: the first body from the empty table, the second (of the
definition `definition'`, with its own annotations) from the first's final table with the leaf
counter reset, its inputs on the same leaves. Only the table passes from the first to the
second. -/
def analyseBoth (cfg : Config D Raw) (definition' : Key) (notes notes' : Annotations Raw)
    {types outs : List D.Ty} (summary : Contract Raw) (inputs inputs' : Names types)
    (body : Term D (Ctx.empty.extend inputs) outs)
    (body' : Term D (Ctx.empty.extend inputs') outs) :
    Exit D Raw cfg.domain.State outs × Exit D Raw cfg.domain.State outs :=
  let first := analyse cfg notes summary inputs body
  (first, analyseFrom { cfg with definition := definition' } notes' summary inputs' body'
    first.state.values)

/-- The places where the skeletons of two bodies differ, by the dialect's decisions. -/
def compareTerms (cfg : Config D Raw) (checks : SkelRules D) (definition' : Key)
    (notes notes' : Annotations Raw) {types outs : List D.Ty} (summary : Contract Raw)
    (inputs inputs' : Names types) (body : Term D (Ctx.empty.extend inputs) outs)
    (body' : Term D (Ctx.empty.extend inputs') outs) : List BodyLocation :=
  let both := analyseBoth cfg definition' notes notes' summary inputs inputs' body body'
  Skel.differ checks none both.1.skel both.2.skel

inductive FollowError (Raw : Type) where
  | source (reason : DefinitionCheckError)
  | candidate (reason : DefinitionCheckError)
  | body (refusals : List (Refusal Raw)) (differences : List Place)

/-- Check both definitions, then derive the candidate's bounds and differences from a single
pair of walks. Refusals and bounds are reported in traversal order. -/
def followChecked (cfg : Config D Raw) (checks : SkelRules D) (definition' : Key)
    (notes notes' : Annotations Raw) {types outs : List D.Ty} (summary : Contract Raw)
    (inputs inputs' : Names types) (body : Term D (Ctx.empty.extend inputs) outs)
    (body' : Term D (Ctx.empty.extend inputs') outs)
    (contractOK : {b : Bool // b = Contract.check (D := D) cfg.assertions summary types outs} := ⟨_, rfl⟩) :
    Except (FollowError Raw) (List (Place × Nat)) :=
  letI := checks.sameTy
  do
    (checkDefinition cfg.assertions cfg.lemmas inputs body notes summary contractOK).mapError FollowError.source
    (checkDefinition cfg.assertions cfg.lemmas inputs' body' notes' summary contractOK).mapError FollowError.candidate
    let both := analyseBoth cfg definition' notes notes' summary inputs inputs' body body'
    let differences := Skel.differ checks none both.1.skel both.2.skel
    if differences.isEmpty && both.2.state.refusals.isEmpty then return both.2.state.bounds.reverse
    else .error (.body both.2.state.refusals.reverse (differences.map (BodyLocation.toPlace definition' cfg.role)))

/-- Whether the comparison accepts the candidate. -/
def follows (cfg : Config D Raw) (checks : SkelRules D) (definition' : Key)
    (notes notes' : Annotations Raw) {types outs : List D.Ty} (summary : Contract Raw)
    (inputs inputs' : Names types) (body : Term D (Ctx.empty.extend inputs) outs)
    (body' : Term D (Ctx.empty.extend inputs') outs) : Bool :=
  (followChecked cfg checks definition' notes notes' summary inputs inputs' body body').isOk

end

end Zkc.Core.BodyAnalysis
