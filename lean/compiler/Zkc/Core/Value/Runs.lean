module

public import Zkc.Core.Value.Growth
public import Zkc.Core.Meaning.Fold
public import Zkc.Core.Process.Same

@[expose] public section

/-!
The meaning of a skeleton over a table, and that it is one meaning.

A value of a semantics with its type (`Semantics.Dyn`) is what the table's applications read and
give. A dialect ties its values to a semantics by a relation on written forms and three laws
(`ValueRules.Binding`): an operation that is a value returns what its written form gives on the
operands, or stops `undefined`; a written form gives one result on given operands; and a written
form that the dialect says commutes gives the same results on its two operands exchanged.

The value of an identifier is read from the values of the leaves through the table (`Reads`): a
leaf has its value; a result of an application has what the written operation gives on the
values of its operands. With leaves that are no results (`Leaves`), an identifier has one value
(`Reads.functional`).

The meaning of a skeleton is a relation, `Skel.Runs`: the processes that do what the skeleton
says, reading each operand through the table. What follows an entry runs for every result that
the entry can return on permitted replies, with that result as the values of its leaves; what
follows an attempt runs from every end of the attempt that can return, since an end that cannot
return is never passed. The relation fixes a process up to the base relation
(`Skel.Runs.same`): two processes that run one skeleton mean the same.
-/

namespace Zkc.Core

open FactCheck (Valuation Table Entry)

/-! ## Values of any type -/

section
variable {D : Dialect}

/-- A value of a semantics with its type. -/
abbrev Semantics.Dyn (sem : Semantics D) : Type := (τ : D.Ty) × sem.Val τ

/-- Values, each with its type. -/
def Semantics.dyns (sem : Semantics D) : {items : List D.Ty} → HList sem.Val items → List sem.Dyn
  | [], .nil => []
  | _ :: _, .cons v rest => ⟨_, v⟩ :: sem.dyns rest

/-- One iteration of a loop, from the process of its body at an iteration number and carried
values: what `Semantics.loopStep` is, without the environment. -/
def Semantics.stepOf (sem : Semantics D) {carried each : List D.Ty}
    (bodyOf : Nat → HList sem.Val carried → Process sem.S sem.H (HList sem.Val (carried ++ each)))
    (i : Nat) (state : sem.LoopState carried each) :
    Process sem.S sem.H (sem.LoopState carried each) :=
  (bodyOf i state.1).bind fun out =>
    .done ((HList.split carried out).1, state.2.push (HList.split carried out).2)

/-- Values with their types are as many as the types. -/
theorem Semantics.dyns_length (sem : Semantics D) :
    ∀ {items : List D.Ty} (values : HList sem.Val items), (sem.dyns values).length = items.length
  | [], .nil => rfl
  | _ :: _, .cons _ rest => congrArg (· + 1) (sem.dyns_length rest)

/-- Two values of one type that are equal with their type are equal. -/
theorem Semantics.dyn_inj (sem : Semantics D) {τ : D.Ty} {v v' : sem.Val τ}
    (same : (⟨τ, v⟩ : sem.Dyn) = ⟨τ, v'⟩) : v = v' :=
  eq_of_heq (Sigma.mk.inj same).2

/-- Values of the same types that are equal with their types are equal. -/
theorem Semantics.dyns_injective (sem : Semantics D) :
    ∀ {items : List D.Ty} {values values' : HList sem.Val items},
      sem.dyns values = sem.dyns values' → values = values'
  | [], .nil, .nil, _ => rfl
  | _ :: _, .cons v rest, .cons v' rest', same => by
      simp only [Semantics.dyns, List.cons.injEq] at same
      rw [sem.dyn_inj same.1, sem.dyns_injective same.2]

end

/-! ## The laws of the values of a dialect -/

/-- The laws that tie the values of a dialect to a semantics: an operation that is a value
returns what its written form gives on the operands, or stops `undefined`; a written form
gives one result on returned operands; and a written form that commutes gives the same results
on its two operands exchanged. -/
structure ValueRules.Binding {D : Dialect} {Raw : Type} (rules : ValueRules D Raw)
    (sem : Semantics D) (Run : Raw → List sem.Dyn → List sem.Dyn → Prop)
    (undefined : sem.H → Prop) : Prop where
  computes : ∀ {ins res : List D.Ty} (o : D.Op ins res) (raw : Raw), rules.written o = some raw →
    ∀ (key : Key) (path : List Frame) (values : HList sem.Val ins),
      (∃ results, sem.op key o path values = .done results ∧
          Run raw (sem.dyns values) (sem.dyns results)) ∨
        ∃ stop, sem.op key o path values = .halt stop ∧ undefined stop
  functional : ∀ raw operands results results', Run raw operands results →
    Run raw operands results' → results = results'
  commutative : ∀ raw, rules.commutes raw = true → ∀ (first second : sem.Dyn) results,
    Run raw [first, second] results → Run raw [second, first] results

/-! ## Reading a value from the leaves through the table -/

section
variable {Val Raw : Type} (Run : Raw → List Val → List Val → Prop) (table : Table Raw)

mutual
  /-- The value of an identifier, from the values of the leaves: a leaf has its value; a result
  of an application has what the written operation gives on the values of the operands. -/
  inductive Reads (ρ : Valuation Val) : Nat → Val → Prop where
    | leaf {id : Nat} {v : Val} (valued : ρ id = some v) : Reads ρ id v
    | entry {e : Entry Raw} {j : Nat} {operands results : List Val} {v : Val} (known : e ∈ table)
        (position : j < e.count) (read : ReadsAll ρ e.args operands)
        (ran : Run e.written operands results) (result : results[j]? = some v) :
        Reads ρ (e.lo + j) v
  /-- The values of identifiers, in order. -/
  inductive ReadsAll (ρ : Valuation Val) : List Nat → List Val → Prop where
    | nil : ReadsAll ρ [] []
    | cons {id : Nat} {ids : List Nat} {v : Val} {vs : List Val} (first : Reads ρ id v)
        (others : ReadsAll ρ ids vs) : ReadsAll ρ (id :: ids) (v :: vs)
end

/-- The leaves and the results of applications are different identifiers: no result of an
entry of the table has a value in the valuation. -/
def Leaves (ρ : Valuation Val) : Prop :=
  ∀ e, e ∈ table → ∀ j, j < e.count → ρ (e.lo + j) = none

/-- An identifier has one value: for a written form that gives one result, a table whose
entries' operands are below their results and whose results are apart, and leaves that are no
results. -/
theorem Reads.functional
    (functional : ∀ raw operands results results', Run raw operands results →
      Run raw operands results' → results = results')
    {n : Nat} (wf : Table.WF n table) {ρ : Valuation Val} (leaves : Leaves table ρ) :
    ∀ {id : Nat} {v v' : Val}, Reads Run table ρ id v → Reads Run table ρ id v' → v = v' := by
  intro id v v' first
  revert v'
  refine Reads.rec (motive_1 := fun id v _ => ∀ {v'}, Reads Run table ρ id v' → v = v')
    (motive_2 := fun ids vs _ => ∀ {vs'}, ReadsAll Run table ρ ids vs' → vs = vs')
    ?leaf ?entry ?nil ?cons first
  case leaf =>
    intro id v valued v' second
    cases second with
    | leaf valued' => rw [valued] at valued'; exact Option.some.inj valued'
    | entry known position _ _ _ => rw [leaves _ known _ position] at valued; cases valued
  case entry =>
    intro e j operands results v known position _ ran result same v' second
    generalize hid : e.lo + j = id at second
    cases second with
    | leaf valued =>
        rw [← hid, leaves _ known _ position] at valued
        cases valued
    | @entry e' j' operands' results' v'' known' position' read' ran' result' =>
        obtain rfl := Table.WF.disjoint wf known known' j j' position position' hid
        obtain rfl : j = j' := by omega
        obtain rfl := same read'
        obtain rfl := functional _ _ _ _ ran ran'
        rw [result] at result'
        exact Option.some.inj result'
  case nil =>
    intro vs' second
    cases second
    rfl
  case cons =>
    intro id ids v vs _ _ sameFirst sameOthers vs' second
    cases second with
    | cons first' others' => rw [sameFirst first', sameOthers others']

/-- Identifiers have one list of values, as each has one value. -/
theorem ReadsAll.functional
    (functional : ∀ raw operands results results', Run raw operands results →
      Run raw operands results' → results = results')
    {n : Nat} (wf : Table.WF n table) {ρ : Valuation Val} (leaves : Leaves table ρ) :
    ∀ {ids : List Nat} {vs vs' : List Val}, ReadsAll Run table ρ ids vs →
      ReadsAll Run table ρ ids vs' → vs = vs'
  | [], _, _, .nil, .nil => rfl
  | _ :: _, _, _, .cons first others, .cons first' others' => by
      rw [Reads.functional Run table functional wf leaves first first',
        ReadsAll.functional functional wf leaves others others']

/-- A value read through a table is read through every table with its entries, from every
valuation with the values of the leaves. -/
theorem Reads.mono {table' : Table Raw} {ρ ρ' : Valuation Val}
    (sub : ∀ e, e ∈ table → e ∈ table') (le : ρ.Le ρ') {id : Nat} {v : Val}
    (read : Reads Run table ρ id v) : Reads Run table' ρ' id v :=
  Reads.rec (motive_1 := fun id v _ => Reads Run table' ρ' id v)
    (motive_2 := fun ids vs _ => ReadsAll Run table' ρ' ids vs)
    (fun valued => .leaf (le _ _ valued))
    (fun known position _ ran result first => .entry (sub _ known) position first ran result)
    .nil (fun _ _ first others => .cons first others) read

/-- Values read through a table are read through every table with its entries, from every
valuation with the values of the leaves. -/
theorem ReadsAll.mono {table' : Table Raw} {ρ ρ' : Valuation Val}
    (sub : ∀ e, e ∈ table → e ∈ table') (le : ρ.Le ρ') :
    ∀ {ids : List Nat} {vs : List Val}, ReadsAll Run table ρ ids vs → ReadsAll Run table' ρ' ids vs
  | [], _, .nil => .nil
  | _ :: _, _, .cons first others =>
      .cons (Reads.mono Run table sub le first) (ReadsAll.mono sub le others)

/-- Identifiers read, position by position, as values as many. -/
theorem ReadsAll.of_getElem? {ρ : Valuation Val} :
    ∀ {ids : List Nat} {vs : List Val}, ids.length = vs.length →
      (∀ (k id : Nat) (v : Val), ids[k]? = some id → vs[k]? = some v → Reads Run table ρ id v) →
      ReadsAll Run table ρ ids vs
  | [], [], _, _ => .nil
  | [], _ :: _, len, _ => nomatch len
  | _ :: _, [], len, _ => nomatch len
  | id :: _, v :: _, len, each =>
      .cons (each 0 id v rfl rfl)
        (ReadsAll.of_getElem? (Nat.succ.inj len) fun k id' v' at_ at' =>
          each (k + 1) id' v' at_ at')

/-- Consecutive identifiers that hold values read as those values. -/
theorem ReadsAll.leaves {ρ : Valuation Val} (lo : Nat) (vs : List Val)
    (valued : ∀ k, k < vs.length → ρ (lo + k) = vs[k]?) :
    ReadsAll Run table ρ (List.range' lo vs.length) vs := by
  refine ReadsAll.of_getElem? Run table (by simp) fun k id v at_ at' => ?_
  have below : k < vs.length := by
    rcases List.getElem?_eq_some_iff.mp at' with ⟨lt, _⟩
    exact lt
  rw [List.getElem?_range' below, Nat.one_mul, Option.some.injEq] at at_
  subst at_
  exact .leaf (by rw [valued k below, at'])

/-- Values set from an identifier on read as themselves there. -/
theorem ReadsAll.setFrom (ρ : Valuation Val) (lo : Nat) (vs : List Val) :
    ReadsAll Run table (ρ.setFrom lo vs) (List.range' lo vs.length) vs :=
  ReadsAll.leaves Run table lo vs fun k below => FactCheck.setFrom_at ρ lo vs k below

/-- The results of an entry read as what its written operation gives on its operands. -/
theorem ReadsAll.results {ρ : Valuation Val} {e : Entry Raw} (known : e ∈ table)
    {operands results : List Val} (read : ReadsAll Run table ρ e.args operands)
    (ran : Run e.written operands results) (count : results.length = e.count) :
    ReadsAll Run table ρ (List.range' e.lo e.count) results := by
  refine ReadsAll.of_getElem? Run table (by simp [count]) fun k id v at_ at' => ?_
  have below : k < e.count := by
    rcases List.getElem?_eq_some_iff.mp at' with ⟨lt, _⟩
    omega
  rw [List.getElem?_range' below, Nat.one_mul, Option.some.injEq] at at_
  subst at_
  exact .entry known below read ran at'

end

section
variable {Raw : Type}

/-- Values set at identifiers apart from the table keep the leaves apart from the results. -/
theorem Leaves.setFrom {Val : Type} {table : Table Raw} {ρ : Valuation Val}
    (leaves : Leaves table ρ) {lo : Nat} {vs : List Val} (apart : LeavesApart table lo vs.length) :
    Leaves table (ρ.setFrom lo vs) := by
  intro e known j below
  simp only [FactCheck.Valuation.setFrom]
  rw [ite_eq_right fun inside => apart e known j below (e.lo + j - lo) (by omega) (by omega)]
  exact leaves e known j below

end

/-! ## The processes that run a skeleton -/

section
variable {D : Dialect} {Raw : Type} (sem : Semantics D)
  (permitted : ∀ op, sem.S.Reply op → Prop)
  (Run : Raw → List sem.Dyn → List sem.Dyn → Prop) (table : Table Raw)

/-- The number of iterations that a count says, on the values of the leaves. -/
def Count.Is {w : D.Who} (ρ : Valuation sem.Dyn) : Count D w → Nat → Prop
  | .fixed n, count => count = n
  | .value (t := t) id ok, count =>
      ∃ v : sem.Val t, Reads Run table ρ id ⟨t, v⟩ ∧ count = sem.count ok v

mutual
  /-- The process does what the skeleton says, from a path and the values of the leaves: each
  entry reads its operands through the table, and what follows an entry runs with the entry's
  results as the values of its leaves, for every result that the entry can return on permitted
  replies. -/
  inductive Skel.Runs : List Frame → Valuation sem.Dyn → {outs : List D.Ty} → Skel D outs →
      Process sem.S sem.H (HList sem.Val outs) → Prop where
    | ret {path ρ outs} {exit : List Nat} (values : HList sem.Val outs)
        (read : ReadsAll Run table ρ exit (sem.dyns values)) :
        Skel.Runs path ρ (.ret exit : Skel D outs) (.done values)
    | effect {path ρ outs ins res} {key : Key} {o : D.Op ins res} {operands : List Nat}
        {results : Nat} {rest : Skel D outs}
        {k : HList sem.Val res → Process sem.S sem.H (HList sem.Val outs)}
        (values : HList sem.Val ins) (read : ReadsAll Run table ρ operands (sem.dyns values))
        (next : ∀ returned, (sem.op key o path values).CanReturn permitted returned →
          Skel.Runs path (ρ.setFrom results (sem.dyns returned)) rest (k returned)) :
        Skel.Runs path ρ (.effect key o operands results rest) ((sem.op key o path values).bind k)
    | guardHolds {path ρ outs t} {key : Key} {w : D.Who} {condition : Nat} {ok : D.Condition w t}
        {why : Reason} {rest : Skel D outs} {p : Process sem.S sem.H (HList sem.Val outs)}
        (v : sem.Val t) (read : Reads Run table ρ condition ⟨t, v⟩)
        (holds : sem.holds ok v = true) (next : Skel.Runs path ρ rest p) :
        Skel.Runs path ρ (.guard key w condition ok why rest) p
    | guardStops {path ρ outs t} {key : Key} {w : D.Who} {condition : Nat} {ok : D.Condition w t}
        {why : Reason} {rest : Skel D outs} (v : sem.Val t)
        (read : Reads Run table ρ condition ⟨t, v⟩) (fails : sem.holds ok v = false) :
        Skel.Runs path ρ (.guard key w condition ok why rest) (.halt (sem.stop w why ⟨path, key⟩))
    | chooseTrue {path ρ outs mid t} {key : Key} {w : D.Who} {condition : Nat}
        {ok : D.Condition w t} {onTrue onFalse : Skel D mid} {results : Nat} {rest : Skel D outs}
        {first : Process sem.S sem.H (HList sem.Val mid)}
        {k : HList sem.Val mid → Process sem.S sem.H (HList sem.Val outs)}
        (v : sem.Val t) (read : Reads Run table ρ condition ⟨t, v⟩)
        (holds : sem.holds ok v = true) (region : Skel.Runs path ρ onTrue first)
        (next : ∀ returned, first.CanReturn permitted returned →
          Skel.Runs path (ρ.setFrom results (sem.dyns returned)) rest (k returned)) :
        Skel.Runs path ρ (.choose key w condition ok onTrue onFalse results rest) (first.bind k)
    | chooseFalse {path ρ outs mid t} {key : Key} {w : D.Who} {condition : Nat}
        {ok : D.Condition w t} {onTrue onFalse : Skel D mid} {results : Nat} {rest : Skel D outs}
        {first : Process sem.S sem.H (HList sem.Val mid)}
        {k : HList sem.Val mid → Process sem.S sem.H (HList sem.Val outs)}
        (v : sem.Val t) (read : Reads Run table ρ condition ⟨t, v⟩)
        (fails : sem.holds ok v = false) (region : Skel.Runs path ρ onFalse first)
        (next : ∀ returned, first.CanReturn permitted returned →
          Skel.Runs path (ρ.setFrom results (sem.dyns returned)) rest (k returned)) :
        Skel.Runs path ρ (.choose key w condition ok onTrue onFalse results rest) (first.bind k)
    | cases {path ρ outs mid t payloads} {key : Key} {w : D.Who} {subject : Nat}
        {ok : D.Alternatives w t payloads} {arms : SkelArms D mid payloads} {results : Nat}
        {rest : Skel D outs} {first : Process sem.S sem.H (HList sem.Val mid)}
        {k : HList sem.Val mid → Process sem.S sem.H (HList sem.Val outs)}
        (v : sem.Val t) (read : Reads Run table ρ subject ⟨t, v⟩)
        (region : SkelArms.Runs path ρ arms (sem.pick ok v) first)
        (next : ∀ returned, first.CanReturn permitted returned →
          Skel.Runs path (ρ.setFrom results (sem.dyns returned)) rest (k returned)) :
        Skel.Runs path ρ (.cases key w subject ok arms results rest) (first.bind k)
    | loop {path ρ outs carried each} {key : Key} {w : D.Who} {times : Count D w}
        {initial : List Nat} {inputs : Nat} {body : Skel D (carried ++ each)} {results : Nat}
        {rest : Skel D outs}
        {k : sem.LoopState carried each → Process sem.S sem.H (HList sem.Val outs)}
        (count : Nat) (counted : times.Is sem Run table ρ count)
        (start : HList sem.Val carried)
        (read : ReadsAll Run table ρ initial (sem.dyns start))
        (bodyOf : Nat → HList sem.Val carried →
          Process sem.S sem.H (HList sem.Val (carried ++ each)))
        (iteration : ∀ i state, i < count →
          (Process.iterate i (sem.stepOf bodyOf) 0 (start, HList.empties each)).CanReturn permitted
            state →
          Skel.Runs (path ++ [.iteration key i])
            (ρ.setFrom inputs (⟨D.index w, sem.index w i⟩ :: sem.dyns state.1)) body
            (bodyOf i state.1))
        (next : ∀ final,
          (Process.iterate count (sem.stepOf bodyOf) 0 (start, HList.empties each)).CanReturn
            permitted final →
          Skel.Runs path
            (ρ.setFrom results
              (sem.dyns (final.1.append (sem.collected times.size final.2)))) rest (k final)) :
        Skel.Runs path ρ (.loop key w times initial inputs body results rest)
          ((Process.iterate count (sem.stepOf bodyOf) 0 (start, HList.empties each)).bind k)
    | block {path ρ outs mid} {key : Key} {number : Nat} {body : Skel D mid} {results : Nat}
        {rest : Skel D outs} {first : Process sem.S sem.H (HList sem.Val mid)}
        {k : HList sem.Val mid → Process sem.S sem.H (HList sem.Val outs)}
        (region : Skel.Runs (path ++ [.iteration key number]) ρ body first)
        (next : ∀ returned, first.CanReturn permitted returned →
          Skel.Runs path (ρ.setFrom results (sem.dyns returned)) rest (k returned)) :
        Skel.Runs path ρ (.block key number body results rest) (first.bind k)
    | attempt {path ρ outs mid} {key : Key} {w : D.Who} {input : Nat} {body : Skel D mid}
        {results : Nat} {rest : Skel D outs}
        (bodyOf : sem.Val (D.index w) → Process sem.S sem.H (HList sem.Val mid))
        {k : HList sem.Val mid → Process sem.S sem.H (HList sem.Val outs)}
        (region : ∀ number, (sem.begin w key path).CanReturn permitted number →
          Skel.Runs path (ρ.setFrom input [⟨D.index w, number⟩]) body (bodyOf number))
        (next : ∀ number returned, (sem.begin w key path).CanReturn permitted number →
          (bodyOf number).CanReturn permitted returned →
          (sem.settle w key path).CanReturn permitted () →
          Skel.Runs path (ρ.setFrom results (sem.dyns returned)) rest (k returned)) :
        Skel.Runs path ρ (.attempt key w input body results rest)
          ((sem.begin w key path).bind fun number =>
            (bodyOf number).bind fun returned => (sem.settle w key path).bind fun _ => k returned)
  /-- The process does what the arm of the alternative says. -/
  inductive SkelArms.Runs : List Frame → Valuation sem.Dyn → {mid payloads : List D.Ty} →
      SkelArms D mid payloads → Pick sem.Val payloads →
      Process sem.S sem.H (HList sem.Val mid) → Prop where
    | here {path ρ mid payload payloads} {input : Nat} {arm : Skel D mid}
        {rest : SkelArms D mid payloads} {v : sem.Val payload}
        {p : Process sem.S sem.H (HList sem.Val mid)}
        (region : Skel.Runs path (ρ.setFrom input [⟨payload, v⟩]) arm p) :
        SkelArms.Runs path ρ (.cons input arm rest) (.here v) p
    | there {path ρ mid payload payloads} {input : Nat} {arm : Skel D mid}
        {rest : SkelArms D mid payloads} {pick : Pick sem.Val payloads}
        {p : Process sem.S sem.H (HList sem.Val mid)}
        (region : SkelArms.Runs path ρ rest pick p) :
        SkelArms.Runs path ρ (.cons (payload := payload) input arm rest) (.there pick) p
end

/-- How often a count says a loop runs is read through every table with the entries, from every
valuation with the values of the leaves. -/
theorem Count.Is.mono {w : D.Who} {table' : Table Raw} {ρ ρ' : Valuation sem.Dyn}
    (sub : ∀ e, e ∈ table → e ∈ table') (le : ρ.Le ρ') :
    ∀ {times : Count D w} {count : Nat}, times.Is sem Run table ρ count →
      times.Is sem Run table' ρ' count
  | .fixed _, _, is => is
  | .value _ _, _, ⟨v, read, is⟩ => ⟨v, Reads.mono Run table sub le read, is⟩

/-- A count says one number of iterations, when every identifier has one value. -/
theorem Count.Is.unique
    (functional : ∀ raw operands results results', Run raw operands results →
      Run raw operands results' → results = results')
    {n : Nat} (wf : Table.WF n table) {ρ : Valuation sem.Dyn} (leaves : Leaves table ρ)
    {w : D.Who} :
    ∀ {times : Count D w} {count count' : Nat}, times.Is sem Run table ρ count →
      times.Is sem Run table ρ count' → count = count'
  | .fixed _, _, _, is, is' => is.trans is'.symm
  | .value _ _, _, _, ⟨_, read, is⟩, ⟨_, read', is'⟩ => by
      rw [is, is', sem.dyn_inj (Reads.functional Run table functional wf leaves read read')]

mutual
  /-- A process that runs a skeleton over a table runs it over every table with its entries. -/
  theorem Skel.Runs.grow {table' : Table Raw} (sub : ∀ e, e ∈ table → e ∈ table') :
      ∀ {outs : List D.Ty} (skel : Skel D outs) {path : List Frame} {ρ : Valuation sem.Dyn}
        {p : Process sem.S sem.H (HList sem.Val outs)},
        Skel.Runs sem permitted Run table path ρ skel p →
        Skel.Runs sem permitted Run table' path ρ skel p
    | _, .ret _, _, _, _, .ret values read =>
        .ret values (ReadsAll.mono Run table sub (.refl _) read)
    | _, .effect _ _ _ _ rest, _, _, _, .effect values read next =>
        .effect values (ReadsAll.mono Run table sub (.refl _) read) fun returned returns =>
          Skel.Runs.grow sub rest (next returned returns)
    | _, .guard _ _ _ _ _ rest, _, _, _, .guardHolds v read holds next =>
        .guardHolds v (Reads.mono Run table sub (.refl _) read) holds
          (Skel.Runs.grow sub rest next)
    | _, .guard _ _ _ _ _ _, _, _, _, .guardStops v read fails =>
        .guardStops v (Reads.mono Run table sub (.refl _) read) fails
    | _, .choose _ _ _ _ onTrue _ _ rest, _, _, _, .chooseTrue v read holds region next =>
        .chooseTrue v (Reads.mono Run table sub (.refl _) read) holds
          (Skel.Runs.grow sub onTrue region) fun returned returns =>
            Skel.Runs.grow sub rest (next returned returns)
    | _, .choose _ _ _ _ _ onFalse _ rest, _, _, _, .chooseFalse v read fails region next =>
        .chooseFalse v (Reads.mono Run table sub (.refl _) read) fails
          (Skel.Runs.grow sub onFalse region) fun returned returns =>
            Skel.Runs.grow sub rest (next returned returns)
    | _, .cases _ _ _ _ arms _ rest, _, _, _, .cases v read region next =>
        .cases v (Reads.mono Run table sub (.refl _) read)
          (SkelArms.Runs.grow sub arms region) fun returned returns =>
            Skel.Runs.grow sub rest (next returned returns)
    | _, .loop _ _ _ _ _ body _ rest, _, _, _,
        .loop count counted start read bodyOf iteration next =>
        .loop count (Count.Is.mono sem Run table sub (.refl _) counted) start
          (ReadsAll.mono Run table sub (.refl _) read) bodyOf
          (fun i state below returns =>
            Skel.Runs.grow sub body (iteration i state below returns))
          fun final returns => Skel.Runs.grow sub rest (next final returns)
    | _, .block _ _ body _ rest, _, _, _, .block region next =>
        .block (Skel.Runs.grow sub body region) fun returned returns =>
          Skel.Runs.grow sub rest (next returned returns)
    | _, .attempt _ _ _ body _ rest, _, _, _, .attempt bodyOf region next =>
        .attempt bodyOf (fun number began => Skel.Runs.grow sub body (region number began))
          fun number returned began ran settled =>
            Skel.Runs.grow sub rest (next number returned began ran settled)
  /-- A process that runs arms over a table runs them over every table with its entries. -/
  theorem SkelArms.Runs.grow {table' : Table Raw} (sub : ∀ e, e ∈ table → e ∈ table') :
      ∀ {mid payloads : List D.Ty} (arms : SkelArms D mid payloads) {path : List Frame}
        {ρ : Valuation sem.Dyn} {pick : Pick sem.Val payloads}
        {p : Process sem.S sem.H (HList sem.Val mid)},
        SkelArms.Runs sem permitted Run table path ρ arms pick p →
        SkelArms.Runs sem permitted Run table' path ρ arms pick p
    | _, _, .cons _ arm _, _, _, _, _, .here region => .here (Skel.Runs.grow sub arm region)
    | _, _, .cons _ _ rest, _, _, _, _, .there region =>
        .there (SkelArms.Runs.grow sub rest region)
end

end

/-! ## One skeleton, one meaning -/

section
variable {D : Dialect} {Raw : Type} (sem : Semantics D)
  (permitted : ∀ op, sem.S.Reply op → Prop)
  (Run : Raw → List sem.Dyn → List sem.Dyn → Prop)

mutual
  /-- Two processes that run one skeleton over one table, from the same path and the same values
  of the leaves, mean the same. -/
  theorem Skel.Runs.same
      (functional : ∀ raw operands results results', Run raw operands results →
        Run raw operands results' → results = results')
      {table : Table Raw} {n : Nat} (wf : Table.WF n table) :
      ∀ {outs : List D.Ty} (skel : Skel D outs), skel.Apart table →
        ∀ {path : List Frame} {ρ : Valuation sem.Dyn}
          {p q : Process sem.S sem.H (HList sem.Val outs)}, Leaves table ρ →
          Skel.Runs sem permitted Run table path ρ skel p →
          Skel.Runs sem permitted Run table path ρ skel q → Process.SameWhen permitted p q
    | _, .ret _, _, _, _, _, _, leaves, first, second => by
        cases first with
        | ret values read =>
          cases second with
          | ret values' read' =>
            rw [sem.dyns_injective (ReadsAll.functional Run table functional wf leaves read read')]
            exact .refl _
    | _, .effect _ _ _ _ rest, apart, _, _, _, _, leaves, first, second => by
        cases first with
        | effect values read next =>
          cases second with
          | effect values' read' next' =>
            obtain rfl := sem.dyns_injective
              (ReadsAll.functional Run table functional wf leaves read read')
            exact Process.SameWhen.bind (.refl _) (Process.every_canReturn _)
              fun returned returns => Skel.Runs.same functional wf rest apart.2
                (leaves.setFrom (by rw [sem.dyns_length]; exact apart.1))
                (next returned returns) (next' returned returns)
    | _, .guard _ _ _ _ _ rest, apart, _, _, _, _, leaves, first, second => by
        cases first with
        | guardHolds v read holds next =>
          cases second with
          | guardHolds v' read' holds' next' =>
            exact Skel.Runs.same functional wf rest apart leaves next next'
          | guardStops v' read' fails' =>
            obtain rfl := sem.dyn_inj (Reads.functional Run table functional wf leaves read read')
            rw [holds] at fails'
            cases fails'
        | guardStops v read fails =>
          cases second with
          | guardHolds v' read' holds' next' =>
            obtain rfl := sem.dyn_inj (Reads.functional Run table functional wf leaves read read')
            rw [fails] at holds'
            cases holds'
          | guardStops v' read' fails' => exact .refl _
    | _, .choose _ _ _ _ onTrue onFalse _ rest, apart, _, _, _, _, leaves, first, second => by
        cases first with
        | chooseTrue v read holds region next =>
          cases second with
          | chooseTrue v' read' holds' region' next' =>
            have regionSame :=
              Skel.Runs.same functional wf onTrue apart.1 leaves region region'
            exact Process.SameWhen.bind regionSame (Process.every_canReturn _)
              fun returned returns => Skel.Runs.same functional wf rest apart.2.2.2
                (leaves.setFrom (by rw [sem.dyns_length]; exact apart.2.2.1))
                (next returned returns) (next' returned (regionSame.canReturn returns))
          | chooseFalse v' read' fails' region' next' =>
            obtain rfl := sem.dyn_inj (Reads.functional Run table functional wf leaves read read')
            rw [holds] at fails'
            cases fails'
        | chooseFalse v read fails region next =>
          cases second with
          | chooseTrue v' read' holds' region' next' =>
            obtain rfl := sem.dyn_inj (Reads.functional Run table functional wf leaves read read')
            rw [fails] at holds'
            cases holds'
          | chooseFalse v' read' fails' region' next' =>
            have regionSame :=
              Skel.Runs.same functional wf onFalse apart.2.1 leaves region region'
            exact Process.SameWhen.bind regionSame (Process.every_canReturn _)
              fun returned returns => Skel.Runs.same functional wf rest apart.2.2.2
                (leaves.setFrom (by rw [sem.dyns_length]; exact apart.2.2.1))
                (next returned returns) (next' returned (regionSame.canReturn returns))
    | _, .cases _ _ _ _ arms _ rest, apart, _, _, _, _, leaves, first, second => by
        cases first with
        | cases v read region next =>
          cases second with
          | cases v' read' region' next' =>
            obtain rfl := sem.dyn_inj (Reads.functional Run table functional wf leaves read read')
            have armsSame :=
              SkelArms.Runs.same functional wf arms apart.1 leaves region region'
            exact Process.SameWhen.bind armsSame (Process.every_canReturn _)
              fun returned returns => Skel.Runs.same functional wf rest apart.2.2
                (leaves.setFrom (by rw [sem.dyns_length]; exact apart.2.1))
                (next returned returns) (next' returned (armsSame.canReturn returns))
    | _, .loop (carried := carried) (each := each) _ _ _ _ _ body _ rest, apart, _, _, _, _,
        leaves, first, second => by
        cases first with
        | loop count counted start read bodyOf iteration next =>
          cases second with
          | loop count' counted' start' read' bodyOf' iteration' next' =>
            obtain rfl := Count.Is.unique sem Run table functional wf leaves counted counted'
            obtain rfl := sem.dyns_injective
              (ReadsAll.functional Run table functional wf leaves read read')
            have stepSame : ∀ i (state : sem.LoopState carried each), i < count →
                (Process.iterate i (sem.stepOf bodyOf) 0 (start, HList.empties each)).CanReturn
                  permitted state →
                (Process.iterate i (sem.stepOf bodyOf') 0 (start, HList.empties each)).CanReturn
                  permitted state →
                Process.SameWhen permitted (sem.stepOf bodyOf i state)
                  (sem.stepOf bodyOf' i state) :=
              fun i state below returns returns' =>
                Process.SameWhen.bind
                  (Skel.Runs.same functional wf body apart.2.1
                    (leaves.setFrom (by
                      simp only [List.length_cons, sem.dyns_length]
                      exact apart.1))
                    (iteration i state below returns) (iteration' i state below returns'))
                  (Process.every_true _ _) fun _ _ => .refl _
            have iterationsSame := Process.SameWhen.iterate_below
              (fun i state =>
                (Process.iterate i (sem.stepOf bodyOf) 0 (start, HList.empties each)).CanReturn
                    permitted state ∧
                  (Process.iterate i (sem.stepOf bodyOf') 0 (start, HList.empties each)).CanReturn
                    permitted state)
              count (fun i state below reached => stepSame i state below reached.1 reached.2)
              (fun i state below reached => Process.every_mono _ permitted
                (fun after returns =>
                  ⟨Process.CanReturn.iterate_succ reached.1 (by rw [Nat.zero_add]; exact returns),
                    Process.CanReturn.iterate_succ reached.2 (by
                      rw [Nat.zero_add]
                      exact (stepSame i state below reached.1 reached.2).canReturn returns)⟩)
                (fun _ h => h) (Process.every_canReturn _))
              count 0 (start, HList.empties each) (Nat.le_of_eq (Nat.zero_add _))
              ⟨.done _, .done _⟩
            exact Process.SameWhen.bind iterationsSame (Process.every_canReturn _)
              fun final returns => Skel.Runs.same functional wf rest apart.2.2.2
                (leaves.setFrom (by
                  rw [sem.dyns_length, List.length_append, List.length_map]
                  exact apart.2.2.1))
                (next final returns) (next' final (iterationsSame.canReturn returns))
    | _, .block _ _ body _ rest, apart, _, _, _, _, leaves, first, second => by
        cases first with
        | block region next =>
          cases second with
          | block region' next' =>
            have bodySame := Skel.Runs.same functional wf body apart.1 leaves region region'
            exact Process.SameWhen.bind bodySame (Process.every_canReturn _)
              fun returned returns => Skel.Runs.same functional wf rest apart.2.2
                (leaves.setFrom (by rw [sem.dyns_length]; exact apart.2.1))
                (next returned returns) (next' returned (bodySame.canReturn returns))
    | _, .attempt _ _ _ body _ rest, apart, _, _, _, _, leaves, first, second => by
        cases first with
        | attempt bodyOf region next =>
          cases second with
          | attempt bodyOf' region' next' =>
            refine Process.SameWhen.bind (.refl _) (Process.every_canReturn _)
              fun number began => ?_
            have bodySame := Skel.Runs.same functional wf body apart.2.1
              (leaves.setFrom apart.1) (region number began) (region' number began)
            refine Process.SameWhen.bind bodySame (Process.every_canReturn _)
              fun returned ran => ?_
            refine Process.SameWhen.bind (.refl _) (Process.every_canReturn _)
              fun ended settled => ?_
            cases ended
            exact Skel.Runs.same functional wf rest apart.2.2.2
              (leaves.setFrom (by rw [sem.dyns_length]; exact apart.2.2.1))
              (next number returned began ran settled)
              (next' number returned began (bodySame.canReturn ran) settled)
  /-- Two processes that run the arms of one skeleton on one alternative mean the same. -/
  theorem SkelArms.Runs.same
      (functional : ∀ raw operands results results', Run raw operands results →
        Run raw operands results' → results = results')
      {table : Table Raw} {n : Nat} (wf : Table.WF n table) :
      ∀ {mid payloads : List D.Ty} (arms : SkelArms D mid payloads), arms.Apart table →
        ∀ {path : List Frame} {ρ : Valuation sem.Dyn} {pick : Pick sem.Val payloads}
          {p q : Process sem.S sem.H (HList sem.Val mid)}, Leaves table ρ →
          SkelArms.Runs sem permitted Run table path ρ arms pick p →
          SkelArms.Runs sem permitted Run table path ρ arms pick q →
          Process.SameWhen permitted p q
    | _, _, .nil, _, _, _, _, _, _, _, first, _ => nomatch first
    | _, _, .cons _ arm rest, apart, _, _, _, _, _, leaves, first, second => by
        cases first with
        | here region =>
          cases second with
          | here region' =>
            exact Skel.Runs.same functional wf arm apart.2.1 (leaves.setFrom apart.1)
              region region'
        | there region =>
          cases second with
          | there region' =>
            exact SkelArms.Runs.same functional wf rest apart.2.2 leaves region region'
end

end

end Zkc.Core
