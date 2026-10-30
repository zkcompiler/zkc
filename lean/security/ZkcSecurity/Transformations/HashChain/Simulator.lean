module

public import ZkcSecurity.Transformations.HashChain.Model
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic

@[expose] public section

/-! The traced concrete oracle, the simulator and the simulated experiment of a
hash chain.

**The bad event.** `traced` is the lazy random oracle on primitive inputs with a
trace of the joint primitive-query sequence of the adversary and the verifier,
in call order. A *reached* state is the state of some history in the cache
(`Reached`). A call *generates* a state when it binds an event or absorbs at a
reached state (`Generating`). The trace records, after each fresh call, the
state the call read and, for a generating call, the state it returned
(`Trace.seen`). The bad flag is raised when a fresh generating call returns a
state already in that record:

- a *collision*, when it equals a state an earlier call generated; or
- a *prediction*, when an earlier call already read it as a state, so an
  adversary queried a guessed state before the chain reached it.

A call at a state that no call generates is answered like every other input and
is not bad. Ordinary precomputation is not prediction: the generating call
comes before the calls that read its state. The flag never falls
(`traced_bad_mono`), and a fresh answer raises it with probability at most the
length of the record over the number of digests.

**The simulator.** `simulator` answers the same primitive calls from two lazily
sampled tables: a history table with one cell per history key and counter block
below the width, and an auxiliary table for every other input. A request at a
reached state with a block below the width is answered by the history cell of
the reached history followed by the request's occurrence; every other call,
including requests at states no call has generated, gets an auxiliary cell.
The simulator records the history of each state that a fresh binding or absorbing
answer generates, keeping the first one, so a request's history key never
changes once assigned.

**The simulated experiment.** The adversary runs against the simulator; the
statement's validator then runs as the typed transform of
`ZkcSecurity.FiatShamir.Typed` with history oracle `historyAnswer`, which reads
the history cells of a key in block order. The validator makes no primitive
call: it reads the history table only.

`Consistent` and `Agrees` relate a trace to a simulator state: the cache's
requests at reached states hold the history cells of their histories, the
history cells belong to reached histories, reached histories are unique, every
reached state and every state read is recorded, and, for `Agrees`, every other
cache entry is the auxiliary cell and the simulator's recorded histories are
exactly the reached ones. The chain lemmas describe how one fresh answer changes
the reached histories.
-/

set_option autoImplicit false

namespace ZkcSecurity.HashChain
open OracleComp OracleSpec ZkcSecurity.FiatShamir

/-- The cached answer at `key`, or a fresh uniform answer, recorded. -/
def lazy {K V : Type} [DecidableEq K] [SampleableType V] (cache : K → Option V) (key : K) :
    ProbComp (V × (K → Option V)) :=
  match cache key with
  | some value => pure (value, cache)
  | none => do
      let value ← $ᵗ V
      pure (value, Function.update cache key (some value))

variable {E S X : Type}

section Reach

/-- A state is reached when some history has it in the cache. -/
def Reached (cache : Input E S X → Option S) (state : S) : Prop :=
  ∃ history, chainState cache history = some state

/-- A call generates a state when it binds an event or absorbs at a reached
state. -/
def Generating (cache : Input E S X → Option S) : Input E S X → Prop
  | .bind _ => True
  | .absorb state _ => Reached cache state
  | _ => False

/-- The history whose state a generating call determines. -/
def NewHistory (cache : Input E S X → Option S) : Input E S X → List E → Prop
  | .bind event, history => history = [event]
  | .absorb state event, history =>
      ∃ before, history = before ++ [event] ∧ chainState cache before = some state
  | _, _ => False

/-- A request served by the history table: at a reached state, with a block
below the width. -/
def Routed (width : ℕ) (cache : Input E S X → Option S) : Input E S X → Prop
  | .request state _ block => Reached cache state ∧ block < width
  | _ => False

end Reach

section Trace

/-- The concrete oracle's cache with the record of the joint primitive-query
trace: the states read and generated so far, and the bad flag. -/
structure Trace (E S X : Type) where
  cache : Input E S X → Option S
  seen : List S
  bad : Bool

/-- The empty trace. -/
def Trace.empty : Trace E S X := ⟨fun _ => none, [], false⟩

variable [DecidableEq E] [DecidableEq S] [DecidableEq X]

open Classical in
/-- Record a fresh answer: cache it, record the state the call read and, for a
generating call, the state it returned, and raise the flag when a generating
call returns a recorded state. -/
noncomputable def Trace.record (trace : Trace E S X) (input : Input E S X) (answer : S) :
    Trace E S X where
  cache := Function.update trace.cache input (some answer)
  seen := trace.seen ++ input.state?.toList ++ if Generating trace.cache input then [answer] else []
  bad := if Generating trace.cache input ∧ answer ∈ trace.seen then true else trace.bad

variable [SampleableType S]

/-- The lazy random oracle on primitive inputs, with the trace. -/
noncomputable def traced : QueryImpl (Primitive E S X) (StateT (Trace E S X) ProbComp) :=
  fun input => StateT.mk fun trace =>
    match trace.cache input with
    | some answer => pure (answer, trace)
    | none => do
        let answer ← $ᵗ S
        pure (answer, trace.record input answer)

theorem traced_run (input : Input E S X) (trace : Trace E S X) :
    (traced input).run trace =
      match trace.cache input with
      | some answer => pure (answer, trace)
      | none => ($ᵗ S) >>= fun answer => pure (answer, trace.record input answer) := rfl

/-- The flag never falls. -/
theorem traced_bad_mono (input : Input E S X) (trace : Trace E S X) (isBad : trace.bad = true) :
    ∀ result ∈ support ((traced input).run trace), result.2.bad = true := by
  intro result member
  rw [traced_run] at member
  cases cached : trace.cache input with
  | some answer =>
      rw [cached] at member
      simp only [support_pure, Set.mem_singleton_iff] at member
      subst member
      exact isBad
  | none =>
      rw [cached] at member
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
      obtain ⟨answer, -, rfl⟩ := member
      simp only [Trace.record]
      split <;> simp [isBad]

end Trace

section Simulator

/-- The simulator's tables: the auxiliary cells, the history cells, and the
history each generated state reaches, first come first kept. The fresh
auxiliary answers in order and the history keys in order of their first cell
are kept for comparison with a simulator that reads a private tape and whole
history answers. -/
structure Simulated (E S X : Type) (width : ℕ) where
  aux : Input E S X → Option S
  history : List E × Fin width → Option S
  reached : S → Option (List E)
  consumed : List S
  touched : List (List E)

/-- The empty tables. -/
def Simulated.empty (width : ℕ) : Simulated E S X width :=
  ⟨fun _ => none, fun _ => none, fun _ => none, [], []⟩

variable [DecidableEq E] [DecidableEq S] [DecidableEq X] [SampleableType S] (width : ℕ)

/-- The history a fresh answer of a generating call reaches: binding reaches the
one-event history, absorbing at a state with a history reaches that history
extended by the event. A state that already has a history keeps it. -/
def noteReached (reached : S → Option (List E)) (input : Input E S X) (answer : S) :
    S → Option (List E) :=
  match reached answer with
  | some _ => reached
  | none =>
      match input with
      | .bind event => Function.update reached answer (some [event])
      | .absorb state event =>
          match reached state with
          | some history => Function.update reached answer (some (history ++ [event]))
          | none => reached
      | _ => reached

/-- Record a fresh auxiliary answer. -/
def Simulated.recordAux (tables : Simulated E S X width) (input : Input E S X) (answer : S) :
    Simulated E S X width :=
  { tables with aux := Function.update tables.aux input (some answer)
                reached := noteReached tables.reached input answer
                consumed := tables.consumed ++ [answer] }

/-- Record a fresh history cell. -/
def Simulated.recordHistory (tables : Simulated E S X width) (key : List E) (block : Fin width)
    (answer : S) : Simulated E S X width :=
  { tables with history := Function.update tables.history (key, block) (some answer)
                touched := if key ∈ tables.touched then tables.touched else tables.touched ++ [key] }

/-- An auxiliary cell. -/
def auxCell (input : Input E S X) : StateT (Simulated E S X width) ProbComp S :=
  StateT.mk fun tables =>
    match tables.aux input with
    | some answer => pure (answer, tables)
    | none => do
        let answer ← $ᵗ S
        pure (answer, tables.recordAux width input answer)

/-- A history cell. -/
def historyBlock (key : List E) (block : Fin width) : StateT (Simulated E S X width) ProbComp S :=
  StateT.mk fun tables =>
    match tables.history (key, block) with
    | some answer => pure (answer, tables)
    | none => do
        let answer ← $ᵗ S
        pure (answer, tables.recordHistory width key block answer)

/-- The history oracle's answer at a key: its cells in block order. -/
def historyAnswer (key : List E) : StateT (Simulated E S X width) ProbComp (Fin width → S) :=
  collect width (historyBlock width key)

/-- The history oracle asked by the transform: its answer at the absorbed
history followed by the query's occurrence. -/
def historyAsk (preceding : List E) (event : E) :
    StateT (Simulated E S X width) ProbComp (Fin width → S) :=
  historyAnswer width (preceding ++ [event])

/-- The simulator: a request at a state with a recorded history and a block below
the width is the history cell of that history followed by the request's
occurrence; every other call is an auxiliary cell. -/
def simulator : QueryImpl (Primitive E S X) (StateT (Simulated E S X width) ProbComp) :=
  fun input => StateT.mk fun tables =>
    match input with
    | .request state event block =>
        match tables.reached state with
        | some history =>
            if below : block < width then
              (historyBlock width (history ++ [event]) ⟨block, below⟩).run tables
            else (auxCell width (.request state event block)).run tables
        | none => (auxCell width (.request state event block)).run tables
    | input => (auxCell width input).run tables

variable {I : PIR.Signature} {P A Stmt : Type}

/-- The simulated experiment: the adversary against the simulator, then the
typed transform of the statement's validator over the history table. -/
noncomputable def simulatedExperiment (absorb : Typed.Interface I E P (Raw E S width))
    (validator : Stmt → PIR.Process I A) (initial : Stmt → List E)
    (adversary : OracleComp (Primitive E S X) (Stmt × List P)) :
    ProbComp (Stmt × (PIR.Outcome A × List P)) := do
  let started ← (simulateQ (simulator width) adversary).run (Simulated.empty width)
  let result ← (Typed.transform absorb (historyAsk width) (validator started.1.1)
    (initial started.1.1) started.1.2).run' started.2
  pure (started.1.1, result)

end Simulator

section Invariants
variable (width : ℕ)

/-- The trace and the tables agree on what the validator can read: requests at
reached states hold the history cells of their histories, history cells belong
to reached histories, reached histories are unique, and every reached state and
every state read is recorded, with the flag down. -/
structure Consistent (trace : Trace E S X) (tables : Simulated E S X width) : Prop where
  good : trace.bad = false
  requests : ∀ history state event block (below : block < width),
    chainState trace.cache history = some state →
      trace.cache (.request state event block) = tables.history (history ++ [event], ⟨block, below⟩)
  cells : ∀ key block, tables.history (key, block) ≠ none →
    ∃ history event state, key = history ++ [event] ∧ chainState trace.cache history = some state
  unique : ∀ history other state, chainState trace.cache history = some state →
    chainState trace.cache other = some state → history = other
  reachedSeen : ∀ history state, chainState trace.cache history = some state → state ∈ trace.seen
  readSeen : ∀ input answer state, trace.cache input = some answer → input.state? = some state →
    state ∈ trace.seen

/-- Consistency, and every cache entry that is not routed to the history table is
the auxiliary cell. -/
structure Agrees (trace : Trace E S X) (tables : Simulated E S X width) : Prop
    extends Consistent width trace tables where
  aux : ∀ input, ¬ Routed width trace.cache input → trace.cache input = tables.aux input
  reachedIff : ∀ state history,
    tables.reached state = some history ↔ chainState trace.cache history = some state

end Invariants

section ChainLemmas
variable [DecidableEq E] [DecidableEq S] [DecidableEq X]

omit [DecidableEq E] [DecidableEq S] [DecidableEq X] in
/-- Reached histories survive a larger cache. -/
theorem chainState_mono {cache larger : Input E S X → Option S}
    (extends_ : ∀ input answer, cache input = some answer → larger input = some answer) :
    ∀ history state, chainState cache history = some state →
      chainState larger history = some state := by
  have fromMono : ∀ (events : List E) (start state : S),
      chainFrom cache start events = some state → chainFrom larger start events = some state := by
    intro events
    induction events with
    | nil => intro start state reached; exact reached
    | cons event rest ih =>
        intro start state reached
        simp only [chainFrom, Option.bind_eq_some_iff] at reached ⊢
        obtain ⟨next, cached, rest'⟩ := reached
        exact ⟨next, extends_ _ _ cached, ih next state rest'⟩
  intro history state reached
  cases history with
  | nil => simp at reached
  | cons event rest =>
      simp only [chainState, Option.bind_eq_some_iff] at reached ⊢
      obtain ⟨start, cached, rest'⟩ := reached
      exact ⟨start, extends_ _ _ cached, fromMono rest start state rest'⟩

/-- Caching a fresh answer keeps every cached entry. -/
theorem update_extends {cache : Input E S X → Option S} {input : Input E S X} {answer : S}
    (fresh : cache input = none) :
    ∀ other value, cache other = some value →
      Function.update cache input (some answer) other = some value := by
  intro other value cached
  have different : other ≠ input := by
    rintro rfl
    rw [fresh] at cached
    cases cached
  rw [Function.update_of_ne different]
  exact cached

/-- Caching an input that generates no state keeps every history's state. -/
theorem chainState_update_of_not_generating {cache : Input E S X → Option S}
    {input : Input E S X} (idle : ¬ Generating cache input) (answer : Option S) :
    ∀ history, chainState (Function.update cache input answer) history = chainState cache history := by
  intro history
  induction history using List.reverseRecOn with
  | nil => rfl
  | append_singleton before event ih =>
      by_cases empty : before = []
      · subst empty
        simp only [List.nil_append, chainState_singleton]
        refine Function.update_of_ne ?_ _ _
        rintro same
        exact idle (same ▸ trivial)
      · rw [chainState_append_singleton _ empty, chainState_append_singleton _ empty, ih]
        cases reached : chainState cache before with
        | none => rfl
        | some state =>
            simp only [Option.bind_some]
            refine Function.update_of_ne ?_ _ _
            rintro same
            exact idle (same ▸ ⟨before, reached⟩)

/-- After a generating call returns a fresh state with no cached successor,
every reached history is an old one or the call's new history at that state. -/
theorem chainState_update_generating {cache : Input E S X → Option S} {input : Input E S X}
    {answer : S}
    (stuck : ∀ event, Function.update cache input (some answer) (.absorb answer event) = none) :
    ∀ history state, chainState (Function.update cache input (some answer)) history = some state →
      chainState cache history = some state ∨ (state = answer ∧ NewHistory cache input history) := by
  intro history
  induction history using List.reverseRecOn with
  | nil => intro state reached; simp at reached
  | append_singleton before event ih =>
      intro state reached
      by_cases empty : before = []
      · subst empty
        simp only [List.nil_append, chainState_singleton] at reached ⊢
        by_cases same : input = .bind event
        · subst same
          rw [Function.update_self] at reached
          cases reached
          exact Or.inr ⟨rfl, rfl⟩
        · rw [Function.update_of_ne (Ne.symm same)] at reached
          exact Or.inl reached
      · rw [chainState_append_singleton _ empty, Option.bind_eq_some_iff] at reached
        obtain ⟨middle, reachedBefore, step⟩ := reached
        rcases ih middle reachedBefore with old | ⟨rfl, -⟩
        · by_cases same : input = .absorb middle event
          · subst same
            rw [Function.update_self] at step
            cases step
            exact Or.inr ⟨rfl, before, rfl, old⟩
          · rw [Function.update_of_ne (Ne.symm same)] at step
            left
            rw [chainState_append_singleton _ empty, old, Option.bind_some]
            exact step
        · rw [stuck event] at step
          cases step

/-- A generating call's new history reaches its answer once cached. -/
theorem chainState_newHistory {cache : Input E S X → Option S} {input : Input E S X}
    {answer : S} (fresh : cache input = none) :
    ∀ history, NewHistory cache input history →
      chainState (Function.update cache input (some answer)) history = some answer := by
  intro history isNew
  cases input with
  | bind event =>
      cases isNew
      simp
  | absorb state event =>
      obtain ⟨before, rfl, reached⟩ := isNew
      rw [chainState_append_singleton _ (ne_nil_of_chainState _ reached),
        chainState_mono (update_extends fresh) before state reached]
      simp
  | request => cases isNew
  | other => cases isNew

omit [DecidableEq E] [DecidableEq S] [DecidableEq X] in
/-- A fresh generating call's new history had no state before. -/
theorem chainState_newHistory_none {cache : Input E S X → Option S} {input : Input E S X}
    (fresh : cache input = none) :
    ∀ history, NewHistory cache input history → chainState cache history = none := by
  intro history isNew
  cases input with
  | bind event =>
      cases isNew
      simpa using fresh
  | absorb state event =>
      obtain ⟨before, rfl, reached⟩ := isNew
      rw [chainState_append_singleton _ (ne_nil_of_chainState _ reached), reached]
      simpa using fresh
  | request => cases isNew
  | other => cases isNew

omit [DecidableEq E] [DecidableEq S] [DecidableEq X] in
/-- Two new histories of one call are equal when reached histories are unique. -/
theorem newHistory_unique {cache : Input E S X → Option S} {input : Input E S X}
    (unique : ∀ history other state, chainState cache history = some state →
      chainState cache other = some state → history = other) :
    ∀ history other, NewHistory cache input history → NewHistory cache input other →
      history = other := by
  intro history other first second
  cases input with
  | bind event =>
      cases first
      cases second
      rfl
  | absorb state event =>
      obtain ⟨before, rfl, reached⟩ := first
      obtain ⟨before', rfl, reached'⟩ := second
      rw [unique before before' state reached reached']
  | request => cases first
  | other => cases first

end ChainLemmas

end ZkcSecurity.HashChain
