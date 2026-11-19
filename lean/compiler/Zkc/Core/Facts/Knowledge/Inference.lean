module

public import Zkc.Core.Facts.Domains.Interface
public import Zkc.Core.Facts.Knowledge.BufferedFacts
public import Zkc.Core.Facts.OpFacts

@[expose] public section

namespace Zkc.Core.BodyAnalysis

/-- Numeric and empty types observed by this dialect. Role adapters may inspect holders. -/
structure KnowledgeTypes (T : Type) where
  range : T → Option Range
  empty : T → Bool

structure KnowledgeTypes.Lawful {T Val : Type} (types : KnowledgeTypes T)
    (R : Reading Val) (Typed : Val → T → Prop) : Prop where
  range : ∀ {t v r}, Typed v t → types.range t = some r → ∃ n, R.nat v = some n ∧ r.Has n
  inhabited : ∀ {t v}, Typed v t → types.empty t = false

/-- A dialect supplies the numeric transfer function and first-result form used by this domain. -/
structure KnowledgeOperations (Raw : Type) where
  ranges : Raw → List (Option Range) → List (Option Range)
  form : Raw → Option ResultForm
  /-- The first result has the same numeric reading as the sole operand on a successful run. -/
  preservesNumber : Raw → Bool := fun _ => false
  /-- A constant range rule can avoid querying every operand. Other adapters use the full list. -/
  needsOperandRanges : Raw → Bool := fun _ => true
  ranges_constant : ∀ op, needsOperandRanges op = false → ∀ rs, ranges op [] = ranges op rs := by
    intros; contradiction

/-- Reuse the existing arithmetic catalog during the compiler migration. -/
def KnowledgeOperations.ofFacts {Raw : Type} (ops : OpFacts Raw) : KnowledgeOperations Raw :=
  { ranges := ops.ranges, form := ops.form }

namespace Knowledge

def truth (k : BufferedFacts) (id : Ident) : Option Bool :=
  let atKey := k.truths.find id.key
  if atKey.any (fun f => f.1 == id.key && f.2 == true) then some true
  else if atKey.any (fun f => f.1 == id.key && f.2 == false) then some false
  else none

/-- All queries use the same keys as the knowledge state, including the leaf/value tag. -/
def answers (k : BufferedFacts) : Asks where
  truth := truth k
  exact id := k.pointOf id.key
  upper id := (k.rangeOf id.key).bind Range.hi

def leaves {T : Type} (types : KnowledgeTypes T) : BufferedFacts → List (Ident × T) → BufferedFacts
  | k, [] => k
  | k, (id, t) :: rest =>
    if types.empty t then k.kill else leaves types (k.addRange? id.key (types.range t)) rest

/-- Record a condition or mark a path unreachable if a cached or peer fact contradicts it. -/
def assume (asks : Asks) (k : BufferedFacts) (id : Ident) (b : Bool) : BufferedFacts :=
  if k.hasTruth id.key (!b) || asks.truth id == some (!b) then k.kill else k.addTruth id.key b

/-- Intersect the local range with the most precise numeric answer available from peers. -/
def directRange (asks : Asks) (k : BufferedFacts) (id : Ident) : Option Range :=
  let peer := match asks.exact id with
    | some n => some (Range.point n)
    | none => (asks.upper id).map fun hi => ⟨0, some hi⟩
  Range.meet (k.rangeOf id.key) peer

def rangeFor (asks : Asks) (k : BufferedFacts) (id : Ident) : Option Range :=
  Range.meet (directRange asks k id) ((asks.numberSource id).bind (directRange asks k))

/-- A hull requires a range from every reachable exit. -/
def hullAt {α : Type} (get : α → Option Range) : List α → Option Range
  | [] => none
  | [e] => get e
  | e :: next :: rest => return (← get e).hull (← hullAt get (next :: rest))

abbrev RegionExit := Asks × BufferedFacts × List Ident

def exitRange (i : Nat) (e : RegionExit) : Option Range := do
  rangeFor e.1 e.2.1 (← e.2.2[i]?)

def learnRanges (rangeAt : Nat → Option Range) : List Ident → Nat → BufferedFacts → BufferedFacts
  | [], _, k => k
  | id :: rest, i, k => learnRanges rangeAt rest (i+1) (k.addRange? id.key (rangeAt i))

def after (k : BufferedFacts) (exits : List RegionExit) (results : List Ident) : BufferedFacts :=
  if exits.isEmpty then k.kill else learnRanges (fun i => hullAt (exitRange i) exits) results 0 k

def operationForm {Raw : Type} (ops : KnowledgeOperations Raw)
    (shape : Option (Form Raw × Nat)) : Option (ResultForm × List Ident) := do
  let (.app op ids, 0) ← shape | none
  return (← ops.form op, ids)

/-- Only the first port carries the operation's declared result form. -/
def resultForm {Raw : Type} (ops : KnowledgeOperations Raw) (table : Table Raw) (id : Ident) :
    Option (ResultForm × List Ident) := operationForm ops (table.formOf id)

/-- Recover the identifier used as a key in an existing order fact. -/
def identOfKey (n : Nat) : Ident := if n % 2 = 0 then .leaf (n/2) else .val (n/2)

def limitFor {Raw : Type} (ops : KnowledgeOperations Raw) (table : Table Raw) (k : BufferedFacts)
    (base index : Ident) (accept : Ident → Bool) : Option Ident :=
  (k.orders.find index.key).findSome? fun fact =>
    if fact.first == index.key && fact.strict && fact.byLoop then
      match resultForm ops table (identOfKey fact.second) with
      | some (.difference, [limit, start]) => if base == start && accept limit then some limit else none
      | _ => none
    else none

def sumLimit {Raw : Type} (ops : KnowledgeOperations Raw) (table : Table Raw) (k : BufferedFacts)
    (x t : Ident) (accept : Ident → Bool) : Option Ident :=
  (limitFor ops table k x t accept).orElse fun _ => limitFor ops table k t x accept

/-- If a loop index is below limit minus base, its sum with the base is below the limit. -/
def offsetLimit {Raw : Type} (ops : KnowledgeOperations Raw) (table : Table Raw) (k : BufferedFacts)
    (result : Ident) (accept : Ident → Bool) : Option Ident :=
  match resultForm ops table result with
  | some (.sum, [x,t]) =>
    sumLimit ops table k x t accept
  | _ => none

/-- Learn only result slots the table entry actually owns. -/
def addResultRanges : Nat → Nat → List (Option Range) → BufferedFacts → BufferedFacts
  | _, 0, _, k | _, _, [], k => k
  | lo, n + 1, range :: ranges, k =>
    addResultRanges (lo + 1) n ranges (k.addRange? (Ident.val lo).key range)

def transferRanges {Raw : Type} (ops : KnowledgeOperations Raw) (asks : Asks) (k : BufferedFacts) (e : Entry Raw) : BufferedFacts :=
  match e.form with
  | .app op ids =>
    let inputs := if ops.needsOperandRanges op then ids.map (rangeFor asks k) else []
    addResultRanges e.lo e.count (ops.ranges op inputs) k
  | .select .. => k

def transfer {Raw : Type} (ops : KnowledgeOperations Raw) (asks : Asks) (table : Table Raw)
    (k : BufferedFacts) (e : Entry Raw) : BufferedFacts :=
  let learned := transferRanges ops asks k e
  if e.count = 0 then learned else
    match e.form with
    | .app op [x,t] =>
      if ops.form op == some .sum then
        let bound := do
          let limit ← sumLimit ops table k x t (fun _ => true)
          return (← rangeFor asks k limit).below
        learned.addRange? (Ident.val e.lo).key bound
      else learned
    | _ => learned

/-- Keep the comparison on its written operands and on their numeric representatives.
The latter key survives a placement change or a repeated measurement. -/
def rememberComparison (asks : Asks) (k : BufferedFacts) (x y : Ident)
    (remember : BufferedFacts → Ident → Ident → BufferedFacts) : BufferedFacts :=
  let learned := remember k x y
  let a := asks.numberAt x
  let b := asks.numberAt y
  if a == x && b == y then learned else remember learned a b

/-- Learn the relation of a numbered loop index to its count at a reachable iteration. -/
def numberIndex {T : Type} (asks : Asks) (k : BufferedFacts) (loop : Loop T) : BufferedFacts :=
  if loop.numbered then
    match loop.count with
    | .inl n => k.addRange loop.index.key (Range.point n).below
    | .inr count =>
      let bound := ((rangeFor asks k count).map Range.below).getD ⟨0, none⟩
      rememberComparison asks (k.addRange loop.index.key bound) loop.index count fun state i n =>
        state.addOrder i.key n.key true (byLoop := true)
  else k

def enter {T : Type} (types : KnowledgeTypes T) (asks : Asks) (k : BufferedFacts) (loop : Loop T) : BufferedFacts :=
  if loop.count = .inl 0 then k.kill else
    leaves types (numberIndex asks k loop) ((loop.index, loop.indexType) :: loop.carried.zip loop.types)

def iterationBound (asks : Asks) (k : BufferedFacts) : Nat ⊕ Ident → Option Nat
  | .inl n => some n
  | .inr id => (rangeFor asks k id).bind Range.hi

/-- The term added to a carried value in either operand order, at result port zero. -/
def addedTerm {Raw : Type} (ops : KnowledgeOperations Raw) (table : Table Raw) (carried returned : Ident) :
    Option Ident := do
  let (.app op [a, b], 0) ← table.formOf returned | none
  if ops.form op != some .sum then none
  else if a = carried then some b else if b = carried then some a else none

def carriedRange {Raw : Type} (ops : KnowledgeOperations Raw) (table : Table Raw)
    (before exit : Asks) (k out : BufferedFacts) (high : Option Nat)
    (initial carried returned : Ident) : Option Range := do
  let start ← rangeFor before k initial
  if out.dead || high == some 0 then return start
  let term ← addedTerm ops table carried returned
  let growth ← rangeFor exit out term
  return Range.afterSums start growth high

def afterLoop {Raw T : Type} (ops : KnowledgeOperations Raw) (before exit : Asks) (table : Table Raw)
    (k : BufferedFacts) (L : Loop T) (out : BufferedFacts) (returned made : List Ident) : BufferedFacts :=
  let high := iterationBound before k L.count
  learnRanges (fun i => do
    carriedRange ops table before exit k out high (← L.initial[i]?) (← L.carried[i]?) (← returned[i]?))
    made 0 k

/-- Allocation numbers bound the depth of a freshly shared expression. Leaves have no definition.
The fuel also makes inspection total on a table supplied directly by a caller. -/
def depth : Ident → Nat
  | .leaf _ => 0
  | .val n => n+1

/-- Follow a numeric conversion only from its first result to its single operand. -/
def conversionOperand {Raw : Type} (ops : KnowledgeOperations Raw) (table : Table Raw)
    (id : Ident) : Option Ident :=
  match table.formOf id with
  | some (.app op [source], 0) => if ops.preservesNumber op then some source else none
  | _ => none

/-- Carry a refined range back through a chain of conversions. Each source keeps its own
identifier and intersects the new bound with the ranges it already has. -/
def refineConversionSources {Raw : Type} (ops : KnowledgeOperations Raw) (table : Table Raw) :
    Nat → BufferedFacts → Ident → BufferedFacts
  | 0, k, _ => k
  | fuel+1, k, id =>
    match conversionOperand ops table id with
    | none => k
    | some source =>
      match k.rangeOf id.key with
      | none => k
      | some bound => refineConversionSources ops table fuel (k.addRange source.key bound) source

/-- A comparison may have refined either of its operands. -/
def refineComparedSources {Raw : Type} (ops : KnowledgeOperations Raw) (table : Table Raw)
    (k : BufferedFacts) (left right : Ident) : BufferedFacts :=
  refineConversionSources ops table (depth right)
    (refineConversionSources ops table (depth left) k left) right

def literalTruth {Raw : Type} (ops : KnowledgeOperations Raw) (table : Table Raw) (id : Ident) : Option Bool :=
  match resultForm ops table id with
  | some (.truth b, _) => some b
  | _ => none

/-- In a lazy choice, a result opposite to one literal arm identifies the arm that actually ran. -/
def learnSelection {Raw : Type} (ops : KnowledgeOperations Raw) (table : Table Raw)
    (learn : BufferedFacts → Ident → Bool → BufferedFacts) (k : BufferedFacts) (id : Ident) (b : Bool) : BufferedFacts :=
  match table.formOf id with
  | some (.select condition first second, 0) =>
    if literalTruth ops table second == some (!b) then learn (learn k condition true) first b
    else if literalTruth ops table first == some (!b) then learn (learn k condition false) second b
    else k
  | _ => k

def learnTruth {Raw : Type} (ops : KnowledgeOperations Raw) (asks : Asks) (table : Table Raw) :
    Nat → BufferedFacts → Ident → Bool → BufferedFacts
  | 0, k, id, b => assume asks k id b
  | fuel+1, k, id, b =>
    if k.hasTruth id.key b then k else
      let learned := assume asks k id b
      match resultForm ops table id with
      | some (.less, [x,y]) =>
        refineComparedSources ops table
          (rememberComparison asks learned x y fun k a c =>
            if b then k.pushLess a.key c.key else k.pushLe c.key a.key) x y
      | some (.equal, [x,y]) =>
        refineComparedSources ops table
          (rememberComparison asks learned x y fun k a c =>
            if b then k.pushEqual a.key c.key else k.pushDifferent a.key c.key) x y
      | some (.negation, [x]) => learnTruth ops asks table fuel learned x (!b)
      | some (.conjunction, [x,y]) =>
        if b then learnTruth ops asks table fuel (learnTruth ops asks table fuel learned x true) y true
        else learned
      | some (.disjunction, [x,y]) =>
        if b then learned
        else learnTruth ops asks table fuel (learnTruth ops asks table fuel learned x false) y false
      | _ => learnSelection ops table (learnTruth ops asks table fuel) learned id b

/-- When the result is a difference from a given minuend, return the subtrahend. -/
def subtractedTerm {Raw : Type} (ops : KnowledgeOperations Raw) (table : Table Raw) (result minuend : Ident) : Option Ident :=
  match resultForm ops table result with
  | some (.difference, [a,t]) => if a = minuend then some t else none
  | _ => none

def separates (asks : Asks) (k : BufferedFacts) (strict : Bool) (term : Option Ident) : Bool :=
  term.any fun t => !strict || ((rangeFor asks k t).any fun r => 0 < r.lo)

/-- An addition whose other operand is known to be zero preserves the first operand. -/
def zeroAddend {Raw : Type} (ops : KnowledgeOperations Raw) (table : Table Raw) (asks : Asks) (k : BufferedFacts)
    (operand result : Ident) : Bool :=
  (addedTerm ops table operand result).any (fun t => (asks.orElse (answers k)).exact t == some 0)

def sameNumber (asks : Asks) (k : BufferedFacts) (x y : Ident) : Bool :=
  asks.numberAt x == asks.numberAt y ||
    ((asks.orElse (answers k)).exact x).any fun n => (asks.orElse (answers k)).exact y == some n

/-- Compare numeric operands of a comparison whose execution witnesses that both are numbers. -/
def orderedAt {Raw : Type} (ops : KnowledgeOperations Raw) (table : Table Raw) (asks : Asks) (k : BufferedFacts) (left right : Ident) (strict : Bool) : Bool :=
  (!strict && left == right) || k.hasOrder left.key right.key strict ||
    FactCheck.rangesOrder (rangeFor asks k left) (rangeFor asks k right) strict ||
    separates asks k strict (addedTerm ops table left right) ||
    separates asks k strict (subtractedTerm ops table left right) ||
    (offsetLimit ops table k left (sameNumber asks k · right)).isSome ||
    (!strict && zeroAddend ops table asks k right left)

def ordered {Raw : Type} (ops : KnowledgeOperations Raw) (table : Table Raw)
    (asks : Asks) (k : BufferedFacts) (left right : Ident) (strict : Bool) : Bool :=
  orderedAt ops table asks k left right strict || Id.run do
    let a := asks.numberAt left
    let b := asks.numberAt right
    return (a != left || b != right) && orderedAt ops table asks k a b strict

/-- Two sums may share an operand while their remaining operands have the same known value
without sharing a table slot. This is used by slice-length contracts. -/
def matchingSums {Raw : Type} (ops : KnowledgeOperations Raw) (table : Table Raw) (asks : Asks) (k : BufferedFacts)
    (left right : Ident) : Bool :=
  match resultForm ops table left, resultForm ops table right with
  | some (.sum, [a,b]), some (.sum, [x,y]) =>
    (sameNumber asks k a x && sameNumber asks k b y) ||
      (sameNumber asks k a y && sameNumber asks k b x)
  | _, _ => false

def compareNumbers {Raw : Type} (ops : KnowledgeOperations Raw) (table : Table Raw) (asks : Asks) (k : BufferedFacts) (left right : Ident) (equal : Bool) : Option Bool :=
  if equal then
    if ordered ops table asks k left right true || ordered ops table asks k right left true then some false
    else if (ordered ops table asks k left right false && ordered ops table asks k right left false) ||
        matchingSums ops table asks k left right then some true
    else none
  else if ordered ops table asks k left right true then some true
  else if ordered ops table asks k right left false then some false else none

/-- A controlling argument decides a conjunction or disjunction even when its peer is unknown. -/
def combineTruth (conjunction : Bool) (first second : Option Bool) : Option Bool :=
  if first == some (!conjunction) || second == some (!conjunction) then some (!conjunction)
  else if first == some conjunction && second == some conjunction then some conjunction else none

/-- Scoped to one query, so entries retain the same table, external answers and knowledge state.
An entry can remember that a shared expression was already inspected and its truth is unknown. -/
abbrev TruthCache := BitTree (Ident × Option Bool)

def TruthCache.lookup (cache : TruthCache) (id : Ident) : Option (Option Bool) :=
  ((cache.find FactCheck.factDepth id.key).find? (fun item => item.1 == id)).map Prod.snd

def TruthCache.remember (cache : TruthCache) (id : Ident) (answer : Option Bool) : TruthCache :=
  cache.insert FactCheck.factDepth id.key (id, answer)

def evalTruth {Raw : Type} (ops : KnowledgeOperations Raw) (asks : Asks) (table : Table Raw) (k : BufferedFacts)
    (child : Ident → TruthCache → Option Bool × TruthCache) (id : Ident) (cache : TruthCache) :
    Option Bool × TruthCache :=
  let shape := table.formOf id
  match operationForm ops shape with
  | some (.truth b, _) => (some b, cache)
  | some (.less, [x,y]) => (compareNumbers ops table asks k x y false, cache)
  | some (.equal, [x,y]) => (compareNumbers ops table asks k x y true, cache)
  | some (.negation, [x]) =>
    let one := child x cache
    (one.1.map (!·), one.2)
  | some (.conjunction, [x,y]) =>
    let left := child x cache
    if left.1 == some false then (some false, left.2) else
      let right := child y left.2
      (combineTruth true left.1 right.1, right.2)
  | some (.disjunction, [x,y]) =>
    let left := child x cache
    if left.1 == some true then (some true, left.2) else
      let right := child y left.2
      (combineTruth false left.1 right.1, right.2)
  | _ =>
    match shape with
    | some (.select cond first second, 0) =>
      let test := child cond cache
      match test.1 with
      | none => (none, test.2)
      | some which => child (if which then first else second) test.2
    | _ => (none, cache)

def cachedTruth {Raw : Type} (ops : KnowledgeOperations Raw) (asks : Asks) (table : Table Raw) (k : BufferedFacts) :
    Nat → Ident → TruthCache → Option Bool × TruthCache
  | 0, id, cache => ((asks.orElse (answers k)).truth id, cache)
  | fuel+1, id, cache =>
    match cache.lookup id with
    | some answer => (answer, cache)
    | none =>
      match (asks.orElse (answers k)).truth id with
      | some b => (some b, cache)
      | none =>
        let (answer, seen) := evalTruth ops asks table k (cachedTruth ops asks table k fuel) id cache
        (answer, seen.remember id answer)

def decideTruth {Raw : Type} (ops : KnowledgeOperations Raw) (asks : Asks) (table : Table Raw) (k : BufferedFacts)
    (id : Ident) : Option Bool :=
  let known := (asks.orElse (answers k)).truth id
  match id with
  | .leaf _ => known
  | .val n => known.orElse fun _ =>
    (evalTruth ops asks table k (cachedTruth ops asks table k n) id (.leaf [])).1

/-- The result keeps its own identifier and type range. A source truth may be known
from the state, from a peer, or by evaluating its shared expression. -/
def observe {Raw : Type} (ops : KnowledgeOperations Raw) (asks : Asks) (table : Table Raw)
    (k : BufferedFacts) (source result : Ident) : BufferedFacts :=
  let ranged := k.addRange? result.key (rangeFor asks k source)
  match decideTruth ops asks table k source with
  | some b => assume asks ranged result b
  | none => ranged

/-- The fact domain uses the dialect's operation observations and its local type information. -/
@[reducible] def domain {Raw T : Type} (types : KnowledgeTypes T) (ops : KnowledgeOperations Raw) : Domain T Raw where
  State := BufferedFacts
  init := BufferedFacts.empty
  dead := BufferedFacts.dead
  leaves := leaves types
  transfer := transfer ops
  observe := observe ops
  assume asks table k id := learnTruth ops asks table (depth id) k id
  truth asks table k id := decideTruth ops asks table k id
  after _ := after
  enter asks _ := enter types asks
  afterLoop := afterLoop ops
  answers := answers

end Knowledge
end Zkc.Core.BodyAnalysis
