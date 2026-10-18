module

public import ZkcSecurity.HashChain.Simulator
public import ZkcSecurity.VCVio.UntilBad

@[expose] public section

/-! One primitive call of the concrete oracle against one simulator step.

From a trace and tables that agree, the traced oracle and the simulator answer
one call with equal answers and agreeing successors, unless the call raises the
bad flag (`adversary_step`): a cached answer is the cell that holds it; a fresh
answer is one fresh uniform sample on both sides, recorded at the call's input
and at its cell. The cell is fresh because requests at reached states hold the
history cells of their histories and reached histories are unique; it stays
consistent because a fresh generating answer outside the record has no cached
successor and no history cell, so the call's new history is the only new reached
history.

The validator's own calls need only consistency: a generating call keeps it or
raises the flag (`generating_support`), and a counter block at a reached history
is the history cell (`request_step`).
-/

set_option autoImplicit false

namespace ZkcSecurity.HashChain
open OracleComp OracleSpec OracleComp.ProgramLogic.Relational ZkcSecurity.FiatShamir

variable {E S X : Type} [DecidableEq E] [DecidableEq S] [DecidableEq X] {width : ℕ}

section Lazy
variable {K V : Type} [DecidableEq K] [SampleableType V]

theorem lazy_some {cache : K → Option V} {key : K} {value : V} (cached : cache key = some value) :
    lazy cache key = pure (value, cache) := by
  unfold lazy
  rw [cached]

theorem lazy_none {cache : K → Option V} {key : K} (fresh : cache key = none) :
    lazy cache key = ($ᵗ V) >>= fun value => pure (value, Function.update cache key (some value)) := by
  unfold lazy
  rw [fresh]

omit [DecidableEq K] in
/-- Two fresh uniform samples, coupled to be equal. -/
theorem relTriple_fresh {α β : Type} {first : V → α} {second : V → β} {R : α → β → Prop}
    (related : ∀ value, R (first value) (second value)) :
    RelTriple (($ᵗ V : ProbComp V) >>= fun value => pure (first value))
      (($ᵗ V : ProbComp V) >>= fun value => pure (second value)) R :=
  relTriple_bind relTriple_uniformSample_refl fun one two same => by
    cases same
    exact relTriple_pure_pure (related one)

end Lazy

section Record

/-- The cache after recording. -/
@[simp] theorem Trace.record_cache (trace : Trace E S X) (input : Input E S X) (answer : S) :
    (trace.record input answer).cache = Function.update trace.cache input (some answer) := rfl

theorem Trace.seen_subset_record (trace : Trace E S X) (input : Input E S X) (answer : S) :
    ∀ state ∈ trace.seen, state ∈ (trace.record input answer).seen := by
  intro state member
  simp [Trace.record, member]

theorem Trace.read_mem_record (trace : Trace E S X) {input : Input E S X} (answer : S) {state : S}
    (reads : input.state? = some state) : state ∈ (trace.record input answer).seen := by
  simp [Trace.record, reads]

theorem Trace.answer_mem_record (trace : Trace E S X) {input : Input E S X} (answer : S)
    (generating : Generating trace.cache input) : answer ∈ (trace.record input answer).seen := by
  simp [Trace.record, generating]

theorem Trace.record_bad_of_not (trace : Trace E S X) (input : Input E S X) {answer : S}
    (quiet : ¬ (Generating trace.cache input ∧ answer ∈ trace.seen)) :
    (trace.record input answer).bad = trace.bad := by
  simp [Trace.record, quiet]

theorem Trace.record_bad_of (trace : Trace E S X) (input : Input E S X) {answer : S}
    (loud : Generating trace.cache input ∧ answer ∈ trace.seen) :
    (trace.record input answer).bad = true := by
  simp [Trace.record, loud]

end Record

section Consistency
variable {trace : Trace E S X} {tables : Simulated E S X width}

omit [DecidableEq E] [DecidableEq S] [DecidableEq X] in
/-- A history cell key that is a reached history followed by an event. -/
theorem append_singleton_inj {first second : List E} {event other : E}
    (same : first ++ [event] = second ++ [other]) : first = second ∧ event = other := by
  obtain ⟨prefixes, lasts⟩ := List.append_inj' same rfl
  exact ⟨prefixes, List.singleton_inj.mp lasts⟩

omit [DecidableEq E] [DecidableEq S] [DecidableEq X] in
/-- A history without a state has no history cells. -/
theorem Consistent.history_none (consistent : Consistent width trace tables) {history : List E}
    (unreached : chainState trace.cache history = none) (event : E) (block : Fin width) :
    tables.history (history ++ [event], block) = none := by
  by_contra present
  obtain ⟨before, other, state, key, reached⟩ := consistent.cells _ _ present
  obtain ⟨rfl, rfl⟩ := append_singleton_inj key
  rw [unreached] at reached
  cases reached

/-- A fresh generating answer outside the record keeps the trace consistent. -/
theorem Consistent.record_generating (consistent : Consistent width trace tables)
    {input : Input E S X} (fresh : trace.cache input = none)
    (generating : Generating trace.cache input) {answer : S} (unseen : answer ∉ trace.seen) :
    Consistent width (trace.record input answer) tables := by
  have notAt : ∀ event, input ≠ .absorb answer event := by
    rintro event rfl
    obtain ⟨history, reached⟩ := generating
    exact unseen (consistent.reachedSeen history answer reached)
  have stuck : ∀ event,
      Function.update trace.cache input (some answer) (.absorb answer event) = none := by
    intro event
    rw [Function.update_of_ne (Ne.symm (notAt event))]
    cases cached : trace.cache (.absorb answer event) with
    | none => rfl
    | some value => exact absurd (consistent.readSeen _ value answer cached rfl) unseen
  have notRequest : ∀ state event block, input ≠ .request state event block := by
    rintro state event block rfl
    exact generating
  have reach := chainState_update_generating stuck
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Trace.record_bad_of_not _ _ fun loud => unseen loud.2]
    exact consistent.good
  · intro history state event block below reached
    rw [Trace.record_cache, Function.update_of_ne (Ne.symm (notRequest state event block))]
    rcases reach history state reached with old | ⟨same, isNew⟩
    · exact consistent.requests history state event block below old
    · rw [same, consistent.history_none (chainState_newHistory_none fresh history isNew)]
      cases cached : trace.cache (.request answer event block) with
      | none => rfl
      | some value => exact absurd (consistent.readSeen _ value answer cached rfl) unseen
  · intro key block present
    obtain ⟨history, event, state, rfl, reached⟩ := consistent.cells key block present
    exact ⟨history, event, state, rfl, chainState_mono (update_extends fresh) _ _ reached⟩
  · intro history other state first second
    rcases reach history state first with old | ⟨rfl, isNew⟩ <;>
      rcases reach other _ second with old' | ⟨same, isNew'⟩
    · exact consistent.unique history other state old old'
    · subst same
      exact absurd (consistent.reachedSeen _ _ old) unseen
    · exact absurd (consistent.reachedSeen _ _ old') unseen
    · exact newHistory_unique consistent.unique history other isNew isNew'
  · intro history state reached
    rcases reach history state reached with old | ⟨rfl, -⟩
    · exact Trace.seen_subset_record _ _ _ _ (consistent.reachedSeen history state old)
    · exact Trace.answer_mem_record _ _ generating
  · intro other value state cached reads
    by_cases same : other = input
    · subst same
      exact Trace.read_mem_record _ _ reads
    · rw [Trace.record_cache, Function.update_of_ne same] at cached
      exact Trace.seen_subset_record _ _ _ _ (consistent.readSeen other value state cached reads)

/-- A fresh answer of a call that is neither generating nor a request keeps the
trace consistent. -/
theorem Consistent.record_idle (consistent : Consistent width trace tables)
    {input : Input E S X} (fresh : trace.cache input = none)
    (idle : ¬ Generating trace.cache input)
    (notRequest : ∀ state event block, input ≠ .request state event block) (answer : S) :
    Consistent width (trace.record input answer) tables := by
  have same := chainState_update_of_not_generating idle (some answer)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Trace.record_bad_of_not _ _ fun loud => idle loud.1]
    exact consistent.good
  · intro history state event block below reached
    rw [Trace.record_cache, same] at *
    rw [Function.update_of_ne (Ne.symm (notRequest state event block))]
    exact consistent.requests history state event block below reached
  · intro key block present
    simp only [Trace.record_cache, same]
    exact consistent.cells key block present
  · intro history other state first second
    rw [Trace.record_cache, same] at first second
    exact consistent.unique history other state first second
  · intro history state reached
    rw [Trace.record_cache, same] at reached
    exact Trace.seen_subset_record _ _ _ _ (consistent.reachedSeen history state reached)
  · intro other value state cached reads
    by_cases equal : other = input
    · subst equal
      exact Trace.read_mem_record _ _ reads
    · rw [Trace.record_cache, Function.update_of_ne equal] at cached
      exact Trace.seen_subset_record _ _ _ _ (consistent.readSeen other value state cached reads)

/-- A fresh counter block at a reached history, recorded in its history cell,
keeps the trace consistent. -/
theorem Consistent.record_routed (consistent : Consistent width trace tables)
    {history : List E} {state : S} (reached : chainState trace.cache history = some state)
    (event : E) (block : Fin width) (answer : S) :
    Consistent width (trace.record (.request state event block.val) answer)
      { tables with history :=
          Function.update tables.history (history ++ [event], block) (some answer) } := by
  have idle : ¬ Generating trace.cache (.request state event block.val : Input E S X) := id
  have same := chainState_update_of_not_generating idle (some answer)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Trace.record_bad_of_not _ _ fun loud => idle loud.1]
    exact consistent.good
  · intro history' state' event' block' below reached'
    rw [Trace.record_cache, same] at reached'
    rw [Trace.record_cache]
    by_cases equal : (Input.request state' event' block' : Input E S X) =
        .request state event block.val
    · cases equal
      have sameHistory := consistent.unique history' history state reached' reached
      subst sameHistory
      have sameBlock : (⟨block.val, below⟩ : Fin width) = block := Fin.ext rfl
      rw [sameBlock, Function.update_self]
      exact (Function.update_self (history' ++ [event], block) (some answer) tables.history).symm
    · rw [Function.update_of_ne equal]
      have different : (history' ++ [event'], (⟨block', below⟩ : Fin width)) ≠
          (history ++ [event], block) := by
        intro key
        obtain ⟨prefixes, events⟩ := Prod.mk.inj key
        obtain ⟨rfl, rfl⟩ := append_singleton_inj prefixes
        rw [reached] at reached'
        cases reached'
        exact equal (by rw [show block' = block.val from congrArg Fin.val events])
      exact (consistent.requests history' state' event' block' below reached').trans
        (Function.update_of_ne different _ _).symm
  · intro key block' present
    by_cases equal : (key, block') = (history ++ [event], block)
    · obtain ⟨rfl, -⟩ := Prod.mk.inj equal
      exact ⟨history, event, state, rfl, by rw [Trace.record_cache, same]; exact reached⟩
    · simp only [Function.update_of_ne equal] at present
      obtain ⟨history', event', state', rfl, reached'⟩ := consistent.cells key block' present
      exact ⟨history', event', state', rfl, by rw [Trace.record_cache, same]; exact reached'⟩
  · intro history' other state' first second
    rw [Trace.record_cache, same] at first second
    exact consistent.unique history' other state' first second
  · intro history' state' reached'
    rw [Trace.record_cache, same] at reached'
    exact Trace.seen_subset_record _ _ _ _ (consistent.reachedSeen history' state' reached')
  · intro other value state' cached reads
    by_cases equal : other = .request state event block.val
    · subst equal
      exact Trace.read_mem_record _ _ reads
    · rw [Trace.record_cache, Function.update_of_ne equal] at cached
      exact Trace.seen_subset_record _ _ _ _ (consistent.readSeen other value state' cached reads)

/-- A fresh request that the history table does not serve keeps the trace
consistent with unchanged history cells. -/
theorem Consistent.record_unrouted (consistent : Consistent width trace tables)
    {state : S} {event : E} {block : ℕ}
    (unrouted : ¬ (Reached trace.cache state ∧ block < width)) (answer : S) :
    Consistent width (trace.record (.request state event block) answer) tables := by
  have idle : ¬ Generating trace.cache (.request state event block : Input E S X) := id
  have same := chainState_update_of_not_generating idle (some answer)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Trace.record_bad_of_not _ _ fun loud => idle loud.1]
    exact consistent.good
  · intro history' state' event' block' below reached'
    rw [Trace.record_cache, same] at reached'
    rw [Trace.record_cache]
    by_cases equal : (Input.request state' event' block' : Input E S X) = .request state event block
    · cases equal
      exact absurd ⟨⟨history', reached'⟩, below⟩ unrouted
    · rw [Function.update_of_ne equal]
      exact consistent.requests history' state' event' block' below reached'
  · intro key block' present
    obtain ⟨history', event', state', rfl, reached'⟩ := consistent.cells key block' present
    exact ⟨history', event', state', rfl, by rw [Trace.record_cache, same]; exact reached'⟩
  · intro history' other state' first second
    rw [Trace.record_cache, same] at first second
    exact consistent.unique history' other state' first second
  · intro history' state' reached'
    rw [Trace.record_cache, same] at reached'
    exact Trace.seen_subset_record _ _ _ _ (consistent.reachedSeen history' state' reached')
  · intro other value state' cached reads
    by_cases equal : other = .request state event block
    · subst equal
      exact Trace.read_mem_record _ _ reads
    · rw [Trace.record_cache, Function.update_of_ne equal] at cached
      exact Trace.seen_subset_record _ _ _ _ (consistent.readSeen other value state' cached reads)

omit [DecidableEq E] [DecidableEq S] [DecidableEq X] in
/-- Consistency reads only the history cells. -/
theorem Consistent.with_aux (consistent : Consistent width trace tables)
    (aux : Input E S X → Option S) : Consistent width trace { tables with aux := aux } :=
  ⟨consistent.good, consistent.requests, consistent.cells, consistent.unique,
    consistent.reachedSeen, consistent.readSeen⟩

omit [DecidableEq E] [DecidableEq S] [DecidableEq X] in
/-- Routed requests stay routed in a larger cache. -/
theorem routed_mono {cache larger : Input E S X → Option S}
    (extends_ : ∀ input answer, cache input = some answer → larger input = some answer)
    {input : Input E S X} (routed : Routed width cache input) : Routed width larger input := by
  cases input with
  | request state event block =>
      obtain ⟨⟨history, reached⟩, below⟩ := routed
      exact ⟨⟨history, chainState_mono extends_ history state reached⟩, below⟩
  | bind => exact routed.elim
  | absorb => exact routed.elim
  | other => exact routed.elim

omit [DecidableEq E] [DecidableEq S] [DecidableEq X] in
/-- Agreeing tables reach the same states as the trace. -/
theorem Agrees.chainState_aux (agrees : Agrees width trace tables) :
    ∀ history, chainState tables.aux history = chainState trace.cache history :=
  chainState_congr tables.aux (fun event => (agrees.aux (.bind event) id).symm)
    (fun state event => (agrees.aux (.absorb state event) id).symm)

omit [DecidableEq E] [DecidableEq S] [DecidableEq X] in
theorem Agrees.routed_iff (agrees : Agrees width trace tables) (input : Input E S X) :
    Routed width tables.aux input ↔ Routed width trace.cache input := by
  cases input with
  | request state event block =>
      simp only [Routed, Reached, agrees.chainState_aux]
  | bind => exact Iff.rfl
  | absorb => exact Iff.rfl
  | other => exact Iff.rfl

/-- A fresh answer recorded in the auxiliary cell of an unrouted call keeps the
agreement, given consistency. -/
theorem Agrees.record_aux (agrees : Agrees width trace tables) {input : Input E S X}
    (fresh : trace.cache input = none) {answer : S}
    (consistent : Consistent width (trace.record input answer) tables) :
    Agrees width (trace.record input answer)
      { tables with aux := Function.update tables.aux input (some answer) } := by
  refine ⟨consistent.with_aux _, fun other unrouted => ?_⟩
  by_cases same : other = input
  · subst same
    simp
  · simp only [Trace.record_cache, Function.update_of_ne same]
    exact agrees.aux other fun routed => unrouted (routed_mono (update_extends fresh) routed)

/-- A fresh answer recorded in the history cell of a routed request keeps the
agreement. -/
theorem Agrees.record_routed (agrees : Agrees width trace tables) {history : List E} {state : S}
    (reached : chainState trace.cache history = some state) (event : E) (block : Fin width)
    (fresh : trace.cache (.request state event block.val) = none) (answer : S) :
    Agrees width (trace.record (.request state event block.val) answer)
      { tables with history :=
          Function.update tables.history (history ++ [event], block) (some answer) } := by
  refine ⟨agrees.toConsistent.record_routed reached event block answer, fun other unrouted => ?_⟩
  by_cases same : other = .request state event block.val
  · subst same
    have idle : ¬ Generating trace.cache (.request state event block.val : Input E S X) := id
    refine absurd ⟨⟨history, ?_⟩, block.isLt⟩ unrouted
    rw [Trace.record_cache, chainState_update_of_not_generating idle]
    exact reached
  · simp only [Trace.record_cache, Function.update_of_ne same]
    exact agrees.aux other fun routed => unrouted (routed_mono (update_extends fresh) routed)

end Consistency

section Dispatch
variable [SampleableType S]

theorem auxCell_run (input : Input E S X) (tables : Simulated E S X width) :
    (auxCell width input).run tables =
      (fun result => (result.1, { tables with aux := result.2 })) <$> lazy tables.aux input := rfl

omit [DecidableEq S] [DecidableEq X] in
theorem historyBlock_run (key : List E) (block : Fin width) (tables : Simulated E S X width) :
    (historyBlock width key block).run tables =
      (fun result => (result.1, { tables with history := result.2 })) <$>
        lazy tables.history (key, block) := rfl

/-- The simulator answers an unrouted call from its auxiliary cell. -/
theorem simulator_run_unrouted (tables : Simulated E S X width) {input : Input E S X}
    (unrouted : ¬ Routed width tables.aux input) :
    (simulator width input).run tables = (auxCell width input).run tables := by
  cases input with
  | request state event block =>
      have unrouted' : ¬ (Reached tables.aux state ∧ block < width) := unrouted
      unfold simulator
      simp only [StateT.run_mk]
      rw [dite_eq_right_of_eq_false (eq_false unrouted')]
  | bind => rfl
  | absorb => rfl
  | other => rfl

/-- The simulator answers a routed request from the history cell of the
reached history. -/
theorem simulator_run_routed (tables : Simulated E S X width) {history : List E} {state : S}
    (reached : chainState tables.aux history = some state)
    (unique : ∀ other, chainState tables.aux other = some state → other = history)
    (event : E) {block : ℕ} (below : block < width) :
    (simulator width (.request state event block)).run tables =
      (historyBlock width (history ++ [event]) ⟨block, below⟩).run tables := by
  have routed : Reached tables.aux state ∧ block < width := ⟨⟨history, reached⟩, below⟩
  unfold simulator
  simp only [StateT.run_mk]
  rw [dite_eq_left_of_eq_true (eq_true routed), unique _ (Classical.choose_spec (of_eq_true (eq_true routed)).1)]

end Dispatch

section AdversaryStep
variable [SampleableType S]

/-- One call: the traced oracle and the simulator answer equally and keep the
agreement, unless the call raises the flag. -/
theorem adversary_step (input : Input E S X) (trace : Trace E S X)
    (tables : Simulated E S X width) (agrees : Agrees width trace tables) :
    RelTriple ((traced input).run trace) ((simulator width input).run tables)
      (fun one two => one.2.bad = true ∨ (one.1 = two.1 ∧ Agrees width one.2 two.2)) := by
  rw [traced_run]
  by_cases routed : Routed width trace.cache input
  · cases input with
    | bind => exact routed.elim
    | absorb => exact routed.elim
    | other => exact routed.elim
    | request state event block =>
        obtain ⟨⟨history, reached⟩, below⟩ := routed
        have reachedAux : chainState tables.aux history = some state := by
          rw [agrees.chainState_aux]
          exact reached
        have unique : ∀ other, chainState tables.aux other = some state → other = history :=
          fun other otherReached => agrees.unique other history state
            (by rw [← agrees.chainState_aux]; exact otherReached) reached
        rw [simulator_run_routed tables reachedAux unique event below, historyBlock_run]
        have cell := agrees.requests history state event block below reached
        cases cached : trace.cache (.request state event block) with
        | some answer =>
            rw [cached] at cell
            rw [lazy_some cell.symm]
            simp only [map_pure]
            exact relTriple_pure_pure (Or.inr ⟨rfl, agrees⟩)
        | none =>
            rw [cached] at cell
            rw [lazy_none cell.symm]
            simp only [map_bind, map_pure]
            refine relTriple_fresh fun answer => Or.inr ⟨rfl, ?_⟩
            exact agrees.record_routed reached event ⟨block, below⟩ cached answer
  · rw [simulator_run_unrouted tables ((agrees.routed_iff input).not.mpr routed), auxCell_run]
    have cell := agrees.aux input routed
    cases cached : trace.cache input with
    | some answer =>
        rw [cached] at cell
        rw [lazy_some cell.symm]
        simp only [map_pure]
        exact relTriple_pure_pure (Or.inr ⟨rfl, agrees⟩)
    | none =>
        rw [cached] at cell
        rw [lazy_none cell.symm]
        simp only [map_bind, map_pure]
        refine relTriple_fresh fun answer => ?_
        by_cases loud : Generating trace.cache input ∧ answer ∈ trace.seen
        · exact Or.inl (Trace.record_bad_of _ _ loud)
        · refine Or.inr ⟨rfl, agrees.record_aux cached ?_⟩
          by_cases generating : Generating trace.cache input
          · exact agrees.toConsistent.record_generating cached generating
              fun seen => loud ⟨generating, seen⟩
          · cases input with
            | request state event block =>
                exact agrees.toConsistent.record_unrouted routed answer
            | bind => exact absurd trivial generating
            | absorb =>
                exact agrees.toConsistent.record_idle cached generating
                  (by intro _ _ _ same; cases same) answer
            | other =>
                exact agrees.toConsistent.record_idle cached generating
                  (by intro _ _ _ same; cases same) answer

end AdversaryStep

end ZkcSecurity.HashChain
