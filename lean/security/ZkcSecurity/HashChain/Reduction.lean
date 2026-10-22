module

public import ZkcSecurity.HashChain.Steps
public import VCVio.ProgramLogic.Relational.SimulateQ.Basic

@[expose] public section

/-! The hash-chain experiment is the simulated experiment up to the bad event.

The concrete experiment runs the adversary and then the chain verifier on one
lazily sampled hash. The simulated experiment runs the adversary against the
simulator and then the typed transform over the history table. Coupled call by
call, the two runs return equal results unless the joint primitive-query trace
of the concrete run raises the bad flag:

- while the adversary runs, each call is answered equally and the trace and the
  tables keep agreeing (`ZkcSecurity.HashChain.adversary_step`), lifted to the
  whole adversary by `ZkcSecurity.VCVio.UntilBad.relTriple_simulateQ_run`;
- the verifier's binding and absorbing calls generate the states of its own
  history, which keeps consistency or raises the flag (`initial_support`);
- the verifier's counter blocks at its reached history are that history's cells
  (`collect_coupling`), so its decoded values, and with them its outcome, are
  those of the typed transform (`verifier_coupling`).

`experiment_coupling` is the coupling of the two experiments. `concrete_le` is
the resulting inequality for any event of the result:

```text
Pr[event | concrete] ≤ Pr[event | simulated] + Pr[the trace raises the bad flag]
```

where the concrete run is the lazy random oracle on primitive inputs and the
bad flag is observed on the same run with its trace (`traced`), which answers
every call exactly as the random oracle does (`randomOracle_coupling`).
-/

set_option autoImplicit false

namespace ZkcSecurity.HashChain
open OracleComp OracleSpec OracleComp.ProgramLogic.Relational ZkcSecurity.FiatShamir
open ZkcSecurity.VCVio.UntilBad

variable {E S X : Type} [DecidableEq E] [DecidableEq S] [DecidableEq X] [SampleableType S]
  {width : ℕ}

section Persistence

/-- A run of the traced oracle from a bad trace ends bad. -/
theorem traced_persists {α : Type} (computation : OracleComp (Primitive E S X) α)
    (trace : Trace E S X) (isBad : trace.bad = true) :
    ∀ result ∈ support ((simulateQ traced computation).run trace), result.2.bad = true :=
  support_bad traced (fun trace => trace.bad = true)
    (fun input trace isBad => traced_bad_mono input trace isBad) computation trace isBad

/-- From a bad trace, a traced run is related to any computation by a
postcondition that admits bad left results. -/
theorem relTriple_of_bad {α β : Type} (computation : OracleComp (Primitive E S X) α)
    {trace : Trace E S X} (isBad : trace.bad = true) (other : ProbComp β)
    {R : α × Trace E S X → β → Prop} (admits : ∀ one two, one.2.bad = true → R one two) :
    RelTriple ((simulateQ traced computation).run trace) other R :=
  relTriple_of_left fun one member two =>
    admits one two (traced_persists computation trace isBad one member)

end Persistence

section Verifier
variable {I : PIR.Signature} {P A : Type}

omit [DecidableEq E] [DecidableEq S] [DecidableEq X] [SampleableType S] in
/-- A generating call's cached answer is the state of its new history. -/
theorem chainState_newHistory_of_cached {cache : Input E S X → Option S} {input : Input E S X}
    {history : List E} (isNew : NewHistory cache input history) {answer : S}
    (cached : cache input = some answer) : chainState cache history = some answer := by
  cases input with
  | bind event =>
      cases isNew
      simpa using cached
  | absorb state event =>
      obtain ⟨before, rfl, reached⟩ := isNew
      rw [chainState_append_singleton _ (ne_nil_of_chainState _ reached), reached]
      simpa using cached
  | request => exact isNew.elim
  | other => exact isNew.elim

/-- A cached or fresh answer of a generating call is the state of its new
history, unless the call raises the flag. -/
theorem generating_support {trace : Trace E S X} {tables : Simulated E S X width}
    (consistent : Consistent width trace tables) {input : Input E S X}
    (generating : Generating trace.cache input) {history : List E}
    (isNew : NewHistory trace.cache input history) :
    ∀ result ∈ support ((traced input).run trace),
      result.2.bad = true ∨
        (Consistent width result.2 tables ∧ chainState result.2.cache history = some result.1) := by
  intro result member
  rw [traced_run] at member
  cases cached : trace.cache input with
  | some answer =>
      rw [cached] at member
      simp only [support_pure, Set.mem_singleton_iff] at member
      subst member
      exact Or.inr ⟨consistent, chainState_newHistory_of_cached isNew cached⟩
  | none =>
      rw [cached] at member
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
      obtain ⟨answer, -, rfl⟩ := member
      by_cases seen : answer ∈ trace.seen
      · exact Or.inl (Trace.record_bad_of _ _ ⟨generating, seen⟩)
      · exact Or.inr ⟨consistent.record_generating cached generating seen,
          chainState_newHistory cached history isNew⟩

/-- Absorbing at the state of a reached history reaches the extended history,
unless the call raises the flag. -/
theorem absorb_support {trace : Trace E S X} {tables : Simulated E S X width}
    (consistent : Consistent width trace tables) {history : List E} {state : S}
    (reached : chainState trace.cache history = some state) (event : E) :
    ∀ result ∈ support ((traced (.absorb state event)).run trace),
      result.2.bad = true ∨ (Consistent width result.2 tables ∧
        chainState result.2.cache (history ++ [event]) = some result.1) :=
  generating_support (input := .absorb state event) consistent ⟨history, reached⟩
    ⟨history, rfl, reached⟩

/-- A counter block at a reached history is that history's cell. -/
theorem request_step {trace : Trace E S X} {tables : Simulated E S X width}
    (consistent : Consistent width trace tables) {history : List E} {state : S}
    (reached : chainState trace.cache history = some state) (event : E) (block : Fin width) :
    RelTriple ((traced (.request state event block.val)).run trace)
      ((historyBlock width (history ++ [event]) block).run tables)
      (fun one two => one.1 = two.1 ∧ Consistent width one.2 two.2 ∧
        chainState one.2.cache history = some state) := by
  rw [traced_run]
  have cell := consistent.requests history state event block.val block.isLt reached
  have idle : ¬ Generating trace.cache (.request state event block.val : Input E S X) := id
  cases cached : trace.cache (.request state event block.val) with
  | some answer =>
      rw [cached] at cell
      rw [historyBlock_run_some cell.symm]
      exact relTriple_pure_pure ⟨rfl, consistent, reached⟩
  | none =>
      rw [cached] at cell
      rw [historyBlock_run_none cell.symm]
      refine relTriple_fresh fun answer => ⟨rfl, ?_, ?_⟩
      · exact consistent.record_routed reached event block answer
      · rw [Trace.record_cache, chainState_update_of_not_generating idle]
        exact reached

/-- The counter blocks of a request at a reached history are that history's
cells, read in the same order. -/
theorem collect_coupling {history : List E} {state : S} (event : E) :
    ∀ (count : ℕ) (blockOf : Fin count → Fin width) (trace : Trace E S X)
      (tables : Simulated E S X width), Consistent width trace tables →
      chainState trace.cache history = some state →
      RelTriple
        ((collect count fun index => traced (.request state event (blockOf index).val)).run trace)
        ((collect count fun index => historyBlock width (history ++ [event]) (blockOf index)).run
          tables)
        (fun one two => one.1 = two.1 ∧ Consistent width one.2 two.2 ∧
          chainState one.2.cache history = some state) := by
  intro count
  induction count with
  | zero =>
      intro blockOf trace tables consistent reached
      simp only [collect, StateT.run_pure]
      exact relTriple_pure_pure ⟨rfl, consistent, reached⟩
  | succ count ih =>
      intro blockOf trace tables consistent reached
      simp only [collect, StateT.run_bind, StateT.run_pure]
      refine relTriple_bind (request_step consistent reached event (blockOf 0))
        fun one two ⟨same, consistent', reached'⟩ => ?_
      refine relTriple_bind (ih (fun index => blockOf index.succ) one.2 two.2 consistent' reached')
        fun one' two' ⟨same', consistent'', reached''⟩ => ?_
      rw [same, same']
      exact relTriple_pure_pure ⟨rfl, consistent'', reached''⟩

/-- Absorbing events from the state of a reached history reaches the extended
history, unless a call raises the flag. -/
theorem absorbAll_support (tables : Simulated E S X width) :
    ∀ (events before : List E) (state : S) (trace : Trace E S X),
      Consistent width trace tables → chainState trace.cache before = some state →
      ∀ result ∈ support ((absorbAll (fun input => traced input) state events).run trace),
        result.2.bad = true ∨ (Consistent width result.2 tables ∧
          chainState result.2.cache (before ++ events) = some result.1) := by
  intro events
  induction events with
  | nil =>
      intro before state trace consistent reached result member
      simp only [absorbAll, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact Or.inr ⟨consistent, by simpa using reached⟩
  | cons event rest ih =>
      intro before state trace consistent reached result member
      simp only [absorbAll, StateT.run_bind, mem_support_bind_iff] at member
      obtain ⟨step, stepMember, restMember⟩ := member
      rcases absorb_support consistent reached event step stepMember with
        isBad | ⟨consistent', reached'⟩
      · left
        rw [← simulateQ_absorbAll traced rest step.1] at restMember
        exact traced_persists _ step.2 isBad result restMember
      · rcases ih (before ++ [event]) step.1 step.2 consistent' reached' result restMember with
          isBad | ⟨consistent'', reached''⟩
        · exact Or.inl isBad
        · exact Or.inr ⟨consistent'', by simpa using reached''⟩

/-- The verifier with the chain and the typed transform over the history table
return the same outcome and unread proof, unless the trace raises the flag. -/
theorem verifier_coupling (absorb : Typed.Interface I E P (Raw E S width))
    (process : PIR.Process I A) :
    ∀ (state : S) (history : List E) (proof : List P) (trace : Trace E S X)
      (tables : Simulated E S X width),
      trace.bad = true ∨ (Consistent width trace tables ∧
        chainState trace.cache history = some state) →
      RelTriple ((chainTransform absorb (fun input => traced input) process state history proof).run
          trace)
        ((Typed.transform absorb (historyAsk width) process history proof).run tables)
        (fun one two => one.2.bad = true ∨ one.1 = two.1) := by
  induction process with
  | done value =>
      intro state history proof trace tables _
      simp only [chainTransform, Typed.transform, StateT.run_pure]
      exact relTriple_pure_pure (Or.inr rfl)
  | halt stop =>
      intro state history proof trace tables _
      simp only [chainTransform, Typed.transform, StateT.run_pure]
      exact relTriple_pure_pure (Or.inr rfl)
  | call operation next ih =>
      intro state history proof trace tables start
      by_cases isBad : trace.bad = true
      · rw [← simulateQ_chainTransform traced absorb]
        exact relTriple_of_bad _ isBad _ fun _ _ bad => Or.inl bad
      obtain ⟨consistent, reached⟩ := start.resolve_left isBad
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      · cases proof with
        | nil =>
            rw [Zkc.Transcript.transform_receive_nil absorb _ absorbed]
            simp only [chainTransform, absorbed, StateT.run_pure]
            exact relTriple_pure_pure (Or.inr rfl)
        | cons message rest =>
            rw [Zkc.Transcript.transform_receive absorb _ absorbed]
            simp only [chainTransform, absorbed]
            cases recover (event message) with
            | none =>
                simp only [StateT.run_pure]
                exact relTriple_pure_pure (Or.inr rfl)
            | some value =>
                simp only [StateT.run_bind]
                refine relTriple_bind_left fun step member => ?_
                rcases absorb_support consistent reached _ step member with
                  stepBad | ⟨consistent', reached'⟩
                · exact ih value _ _ _ _ _ (Or.inl stepBad)
                · exact ih value _ _ _ _ _ (Or.inr ⟨consistent', reached'⟩)
      · rw [Zkc.Transcript.transform_send absorb _ absorbed]
        simp only [chainTransform, absorbed, StateT.run_bind]
        refine relTriple_bind_left fun step member => ?_
        rcases absorb_support consistent reached event step member with
          stepBad | ⟨consistent', reached'⟩
        · exact ih value _ _ _ _ _ (Or.inl stepBad)
        · exact ih value _ _ _ _ _ (Or.inr ⟨consistent', reached'⟩)
      · rw [Zkc.Transcript.transform_query absorb _ absorbed]
        simp only [chainTransform, absorbed, StateT.run_bind, historyAsk, historyAnswer]
        refine relTriple_bind (collect_coupling event width (fun index => index) trace tables
          consistent reached) fun blocks cells ⟨same, consistent', reached'⟩ => ?_
        refine relTriple_bind_left fun step member => ?_
        rw [same]
        rcases absorb_support consistent' reached' event step member with
          stepBad | ⟨consistent'', reached''⟩
        · cases decode cells.1 with
          | none =>
              simp only [StateT.run_pure]
              exact relTriple_pure_pure (Or.inl stepBad)
          | some value => exact ih value _ _ _ _ _ (Or.inl stepBad)
        · cases decode cells.1 with
          | none =>
              simp only [StateT.run_pure]
              exact relTriple_pure_pure (Or.inr rfl)
          | some value => exact ih value _ _ _ _ _ (Or.inr ⟨consistent'', reached''⟩)
      · rw [Zkc.Transcript.transform_refuse absorb _ absorbed]
        simp only [chainTransform, absorbed, StateT.run_pure]
        exact relTriple_pure_pure (Or.inr rfl)

/-- Binding and absorbing the initial history, then the verifier with the chain,
against the typed transform from the initial history. -/
theorem chainRun_coupling (absorb : Typed.Interface I E P (Raw E S width))
    (validator : PIR.Process I A) {initial : List E} (nonempty : initial ≠ []) (proof : List P)
    {trace : Trace E S X} {tables : Simulated E S X width}
    (consistent : Consistent width trace tables) :
    RelTriple ((chainRun absorb (fun input => traced input) validator initial proof).run trace)
      ((Typed.transform absorb (historyAsk width) validator initial proof).run tables)
      (fun one two => one.2.bad = true ∨ one.1 = two.1) := by
  obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil nonempty
  simp only [chainRun, StateT.run_bind]
  refine relTriple_bind_left fun step member => ?_
  rcases generating_support (input := .bind first) consistent trivial rfl step member with
    stepBad | ⟨consistent', reached'⟩
  · refine relTriple_bind_left fun started startedMember => ?_
    rw [← simulateQ_absorbAll traced rest step.1] at startedMember
    exact verifier_coupling absorb validator _ _ proof _ tables
      (Or.inl (traced_persists _ step.2 stepBad started startedMember))
  · refine relTriple_bind_left fun started startedMember => ?_
    rcases absorbAll_support tables rest [first] step.1 step.2 consistent' reached' started
        startedMember with startedBad | ⟨consistent'', reached''⟩
    · exact verifier_coupling absorb validator _ _ proof _ tables (Or.inl startedBad)
    · exact verifier_coupling absorb validator _ _ proof _ tables
        (Or.inr ⟨consistent'', by simpa using reached''⟩)

end Verifier

section Experiments
variable {I : PIR.Signature} {P A Stmt : Type}

omit [DecidableEq E] [DecidableEq S] [DecidableEq X] [SampleableType S] in
/-- The empty trace agrees with the empty tables. -/
theorem agrees_empty : Agrees width (Trace.empty : Trace E S X) (Simulated.empty width) := by
  have unreached : ∀ (history : List E) (state : S),
      chainState (Trace.empty : Trace E S X).cache history ≠ some state := by
    intro history state
    cases history with
    | nil => simp
    | cons event rest => simp [chainState, Trace.empty]
  refine ⟨⟨rfl, ?_, ?_, ?_, ?_, ?_⟩, fun _ _ => rfl, ?_⟩
  · exact fun history state _ _ _ reached => absurd reached (unreached history state)
  · exact fun _ _ present => absurd rfl present
  · exact fun history _ state reached => absurd reached (unreached history state)
  · exact fun history state reached => absurd reached (unreached history state)
  · intro _ _ _ cached
    cases cached
  · exact fun state history => ⟨fun recorded => (by cases recorded),
      fun reached => absurd reached (unreached history state)⟩

/-- The concrete experiment with its trace against the simulated experiment:
equal results unless the trace raises the bad flag. -/
theorem experiment_coupling (absorb : Typed.Interface I E P (Raw E S width))
    (validator : Stmt → PIR.Process I A) (initial : Stmt → List E)
    (nonempty : ∀ statement, initial statement ≠ [])
    (adversary : OracleComp (Primitive E S X) (Stmt × List P)) :
    RelTriple ((simulateQ traced (experiment absorb validator initial adversary)).run Trace.empty)
      (simulatedExperiment width absorb validator initial adversary)
      (fun one two => one.2.bad = true ∨ one.1 = two) := by
  simp only [experiment, simulatedExperiment, simulateQ_bind, simulateQ_map, simulateQ_chainRun,
    StateT.run_bind, StateT.run_map, StateT.run'_eq, bind_map_left]
  refine relTriple_bind (relTriple_simulateQ_run traced (simulator width)
    (fun trace => trace.bad = true) (Agrees width)
    (fun input trace isBad => traced_bad_mono input trace isBad)
    (fun input trace tables agrees _ => adversary_step input trace tables agrees) adversary
    Trace.empty (Simulated.empty width) (Or.inr agrees_empty)) fun one two coupled => ?_
  rcases coupled with oneBad | ⟨same, agrees⟩
  · refine relTriple_of_left fun result member _ => Or.inl ?_
    rw [support_map] at member
    obtain ⟨run, runMember, rfl⟩ := member
    rw [← simulateQ_chainRun traced] at runMember
    exact traced_persists _ one.2 oneBad run runMember
  · rw [same]
    have verified := chainRun_coupling absorb (validator two.1.1) (nonempty two.1.1) two.1.2
      agrees.toConsistent
    simp only [bind_pure_comp]
    refine relTriple_map (relTriple_post_mono verified ?_)
    rintro first second (firstBad | sameResult)
    · exact Or.inl firstBad
    · exact Or.inr (by rw [sameResult])

/-- The traced oracle answers every call as the lazy random oracle on primitive
inputs does. -/
theorem randomOracle_coupling {α : Type} (computation : OracleComp (Primitive E S X) α) :
    RelTriple ((simulateQ randomOracle computation).run' ∅)
      ((simulateQ traced computation).run Trace.empty) (fun one two => one = two.1) := by
  have coupled := OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run
    (randomOracle (spec := Primitive E S X)) traced
    (fun cache trace => ∀ input, cache input = trace.cache input) computation
    (fun input cache trace agree => by
      rw [randomOracle.run_eq, traced_run, ← agree input]
      cases cached : cache input with
      | some answer => exact relTriple_pure_pure ⟨rfl, agree⟩
      | none =>
          refine relTriple_fresh fun answer => ⟨rfl, fun other => ?_⟩
          by_cases same : other = input
          · subst same
            simp
          · rw [QueryCache.cacheQuery_of_ne _ _ same, Trace.record_cache,
              Function.update_of_ne same]
            exact agree other)
    ∅ Trace.empty (fun _ => rfl)
  rw [StateT.run'_eq, ← id_map ((simulateQ traced computation).run Trace.empty)]
  exact relTriple_map (relTriple_post_mono coupled fun _ _ related => related.1)

/-- The concrete experiment exceeds the simulated experiment by at most the
probability that the joint primitive-query trace raises the bad flag, for any
event of the result. -/
theorem concrete_le (absorb : Typed.Interface I E P (Raw E S width))
    (validator : Stmt → PIR.Process I A) (initial : Stmt → List E)
    (nonempty : ∀ statement, initial statement ≠ [])
    (adversary : OracleComp (Primitive E S X) (Stmt × List P))
    (event : Stmt × (PIR.Outcome A × List P) → Prop) :
    Pr{let result ← (simulateQ randomOracle (experiment absorb validator initial adversary)).run' ∅}[
        event result] ≤
      Pr{let result ← simulatedExperiment width absorb validator initial adversary}[event result] +
        Pr{let result ← ((simulateQ traced (experiment absorb validator initial adversary)).run
          Trace.empty)}[result.2.bad = true] := by
  have traced_le := prEvent_le_of_relTriple
    (randomOracle_coupling (experiment absorb validator initial adversary))
    (event := event) (target := fun result => event result.1)
    fun one two (same : one = two.1) holds => by rw [← same]; exact holds
  have simulated_le := prEvent_le_add_bad (bad := fun trace : Trace E S X => trace.bad = true)
    (R := Eq) (experiment_coupling absorb validator initial nonempty adversary)
    (event := event) (target := event)
    fun one two (same : one = two) holds => by rw [← same]; exact holds
  exact traced_le.trans simulated_le

end Experiments

end ZkcSecurity.HashChain
