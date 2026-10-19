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
      (tables.recordHistory width (history ++ [event]) block answer) := by
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
    · simp only [Simulated.recordHistory, Function.update_of_ne equal] at present
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
theorem Consistent.of_history {other : Simulated E S X width}
    (consistent : Consistent width trace tables) (same : other.history = tables.history) :
    Consistent width trace other :=
  ⟨consistent.good, fun history state event block below reached => by
      rw [same]; exact consistent.requests history state event block below reached,
    fun key block present => consistent.cells key block (by rwa [same] at present),
    consistent.unique, consistent.reachedSeen, consistent.readSeen⟩

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
/-- A state has a recorded history exactly when it is reached. -/
theorem Agrees.recorded_iff (agrees : Agrees width trace tables) (state : S) :
    (∃ history, tables.reached state = some history) ↔ Reached trace.cache state := by
  simp only [Reached, agrees.reachedIff]

/-- The recorded histories after a fresh generating answer outside the record
are the reached histories of the trace that records it. -/
theorem Agrees.noteReached_generating (agrees : Agrees width trace tables) {input : Input E S X}
    (fresh : trace.cache input = none) (generating : Generating trace.cache input) {answer : S}
    (unseen : answer ∉ trace.seen) :
    ∀ state history, noteReached tables.reached input answer state = some history ↔
      chainState (trace.record input answer).cache history = some state := by
  have notAt : ∀ event, input ≠ .absorb answer event := by
    rintro event rfl
    obtain ⟨history, reached⟩ := generating
    exact unseen (agrees.reachedSeen history answer reached)
  have stuck : ∀ event,
      Function.update trace.cache input (some answer) (.absorb answer event) = none := by
    intro event
    rw [Function.update_of_ne (Ne.symm (notAt event))]
    cases cached : trace.cache (.absorb answer event) with
    | none => rfl
    | some value => exact absurd (agrees.readSeen _ value answer cached rfl) unseen
  have unrecorded : tables.reached answer = none := by
    cases recorded : tables.reached answer with
    | none => rfl
    | some history =>
        exact absurd (agrees.reachedSeen history answer ((agrees.reachedIff _ _).mp recorded))
          unseen
  -- the new history of the call, and the update it records
  obtain ⟨newHistory, isNew, noted⟩ : ∃ newHistory, NewHistory trace.cache input newHistory ∧
      noteReached tables.reached input answer =
        Function.update tables.reached answer (some newHistory) := by
    cases input with
    | bind event =>
        exact ⟨[event], rfl, by simp only [noteReached, unrecorded]⟩
    | absorb state event =>
        obtain ⟨before, reachedBefore⟩ := generating
        refine ⟨before ++ [event], ⟨before, rfl, reachedBefore⟩, ?_⟩
        have recordedBefore := (agrees.reachedIff state before).mpr reachedBefore
        simp only [noteReached, unrecorded, recordedBefore]
    | request => exact generating.elim
    | other => exact generating.elim
  intro state history
  rw [noted, Trace.record_cache]
  constructor
  · intro recorded
    by_cases same : state = answer
    · subst same
      rw [Function.update_self] at recorded
      cases recorded
      exact chainState_newHistory fresh _ isNew
    · rw [Function.update_of_ne same] at recorded
      exact chainState_mono (update_extends fresh) _ _ ((agrees.reachedIff _ _).mp recorded)
  · intro reached
    rcases chainState_update_generating stuck history state reached with old | ⟨rfl, isNew'⟩
    · have different : state ≠ answer := by
        rintro rfl
        exact unseen (agrees.reachedSeen history _ old)
      rw [Function.update_of_ne different]
      exact (agrees.reachedIff _ _).mpr old
    · rw [Function.update_self, newHistory_unique agrees.unique history newHistory isNew' isNew]

omit [DecidableEq E] [DecidableEq X] in
/-- An answer that generates no state records no history. -/
theorem noteReached_idle {reached : S → Option (List E)} {input : Input E S X} {answer : S}
    (idle : ∀ state event, input = .absorb state event → reached state = none)
    (notBind : ∀ event, input ≠ .bind event) :
    noteReached reached input answer = reached := by
  unfold noteReached
  cases reached answer with
  | some _ => rfl
  | none =>
      cases input with
      | bind event => exact absurd rfl (notBind event)
      | absorb state event => simp only [idle state event rfl]
      | request => rfl
      | other => rfl

/-- A fresh answer recorded in the auxiliary cell of an unrouted call keeps the
agreement, given consistency and the recorded histories. -/
theorem Agrees.record_aux (agrees : Agrees width trace tables) {input : Input E S X}
    (fresh : trace.cache input = none) {answer : S}
    (consistent : Consistent width (trace.record input answer) tables)
    (recorded : ∀ state history, noteReached tables.reached input answer state = some history ↔
      chainState (trace.record input answer).cache history = some state) :
    Agrees width (trace.record input answer) (tables.recordAux width input answer) := by
  refine ⟨consistent.of_history rfl, fun other unrouted => ?_, recorded⟩
  by_cases same : other = input
  · subst same
    simp [Simulated.recordAux]
  · simp only [Trace.record_cache, Simulated.recordAux, Function.update_of_ne same]
    exact agrees.aux other fun routed => unrouted (routed_mono (update_extends fresh) routed)

/-- A fresh answer recorded in the history cell of a routed request keeps the
agreement. -/
theorem Agrees.record_routed (agrees : Agrees width trace tables) {history : List E} {state : S}
    (reached : chainState trace.cache history = some state) (event : E) (block : Fin width)
    (fresh : trace.cache (.request state event block.val) = none) (answer : S) :
    Agrees width (trace.record (.request state event block.val) answer)
      (tables.recordHistory width (history ++ [event]) block answer) := by
  have idle : ¬ Generating trace.cache (.request state event block.val : Input E S X) := id
  refine ⟨agrees.toConsistent.record_routed reached event block answer,
    fun other unrouted => ?_, fun state' history' => ?_⟩
  · by_cases same : other = .request state event block.val
    · subst same
      refine absurd ⟨⟨history, ?_⟩, block.isLt⟩ unrouted
      rw [Trace.record_cache, chainState_update_of_not_generating idle]
      exact reached
    · simp only [Trace.record_cache, Simulated.recordHistory, Function.update_of_ne same]
      exact agrees.aux other fun routed => unrouted (routed_mono (update_extends fresh) routed)
  · rw [Trace.record_cache, chainState_update_of_not_generating idle]
    exact agrees.reachedIff state' history'

end Consistency

section Dispatch
variable [SampleableType S]

theorem auxCell_run_some {input : Input E S X} {tables : Simulated E S X width} {answer : S}
    (cached : tables.aux input = some answer) :
    (auxCell width input).run tables = pure (answer, tables) := by
  simp only [auxCell, StateT.run_mk, cached]

theorem auxCell_run_none {input : Input E S X} {tables : Simulated E S X width}
    (fresh : tables.aux input = none) :
    (auxCell width input).run tables =
      ($ᵗ S) >>= fun answer => pure (answer, tables.recordAux width input answer) := by
  simp only [auxCell, StateT.run_mk, fresh]

omit [DecidableEq S] [DecidableEq X] in
theorem historyBlock_run_some {key : List E} {block : Fin width} {tables : Simulated E S X width}
    {answer : S} (cached : tables.history (key, block) = some answer) :
    (historyBlock width key block).run tables = pure (answer, tables) := by
  simp only [historyBlock, StateT.run_mk, cached]

omit [DecidableEq S] [DecidableEq X] in
theorem historyBlock_run_none {key : List E} {block : Fin width} {tables : Simulated E S X width}
    (fresh : tables.history (key, block) = none) :
    (historyBlock width key block).run tables =
      ($ᵗ S) >>= fun answer => pure (answer, tables.recordHistory width key block answer) := by
  simp only [historyBlock, StateT.run_mk, fresh]

/-- The simulator answers a call that its recorded histories do not route from its
auxiliary cell. -/
theorem simulator_run_unrouted (tables : Simulated E S X width) {input : Input E S X}
    (unrouted : ∀ state event block history, input = .request state event block →
      tables.reached state = some history → width ≤ block) :
    (simulator width input).run tables = (auxCell width input).run tables := by
  cases input with
  | request state event block =>
      unfold simulator
      simp only [StateT.run_mk]
      cases recorded : tables.reached state with
      | none => rfl
      | some history =>
          have notBelow : ¬ block < width := by
            have := unrouted state event block history rfl recorded
            omega
          simp only [notBelow, ↓reduceDIte]
  | bind => rfl
  | absorb => rfl
  | other => rfl

/-- The simulator answers a request at a state with a recorded history, with a
block below the width, from that history's cell. -/
theorem simulator_run_routed (tables : Simulated E S X width) {history : List E} {state : S}
    (recorded : tables.reached state = some history) (event : E) {block : ℕ}
    (below : block < width) :
    (simulator width (.request state event block)).run tables =
      (historyBlock width (history ++ [event]) ⟨block, below⟩).run tables := by
  unfold simulator
  simp only [StateT.run_mk, recorded, below, ↓reduceDIte]

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
        rw [simulator_run_routed tables ((agrees.reachedIff state history).mpr reached) event below]
        have cell := agrees.requests history state event block below reached
        cases cached : trace.cache (.request state event block) with
        | some answer =>
            rw [cached] at cell
            rw [historyBlock_run_some cell.symm]
            exact relTriple_pure_pure (Or.inr ⟨rfl, agrees⟩)
        | none =>
            rw [cached] at cell
            rw [historyBlock_run_none cell.symm]
            refine relTriple_fresh fun answer => Or.inr ⟨rfl, ?_⟩
            exact agrees.record_routed reached event ⟨block, below⟩ cached answer
  · have unrouted : ∀ state event block history, input = .request state event block →
        tables.reached state = some history → width ≤ block := by
      rintro state event block history rfl recorded
      by_contra below
      exact routed ⟨⟨history, (agrees.reachedIff state history).mp recorded⟩, by omega⟩
    rw [simulator_run_unrouted tables unrouted]
    have cell := agrees.aux input routed
    cases cached : trace.cache input with
    | some answer =>
        rw [cached] at cell
        rw [auxCell_run_some cell.symm]
        exact relTriple_pure_pure (Or.inr ⟨rfl, agrees⟩)
    | none =>
        rw [cached] at cell
        rw [auxCell_run_none cell.symm]
        refine relTriple_fresh fun answer => ?_
        by_cases loud : Generating trace.cache input ∧ answer ∈ trace.seen
        · exact Or.inl (Trace.record_bad_of _ _ loud)
        · refine Or.inr ⟨rfl, ?_⟩
          by_cases generating : Generating trace.cache input
          · have unseen : answer ∉ trace.seen := fun seen => loud ⟨generating, seen⟩
            exact agrees.record_aux cached (agrees.toConsistent.record_generating cached generating
              unseen) (agrees.noteReached_generating cached generating unseen)
          · have idleAbsorb : ∀ state event, input = .absorb state event →
                tables.reached state = none := by
              rintro state event rfl
              cases recorded : tables.reached state with
              | none => rfl
              | some history =>
                  exact absurd ⟨history, (agrees.reachedIff state history).mp recorded⟩ generating
            have notBind : ∀ event, input ≠ .bind event := by
              rintro event rfl
              exact generating trivial
            have same := chainState_update_of_not_generating generating (some answer)
            refine agrees.record_aux cached ?_ fun state history => ?_
            · cases input with
              | request state event block =>
                  exact agrees.toConsistent.record_unrouted routed answer
              | bind event => exact absurd rfl (notBind event)
              | absorb =>
                  exact agrees.toConsistent.record_idle cached generating
                    (by intro _ _ _ same; cases same) answer
              | other =>
                  exact agrees.toConsistent.record_idle cached generating
                    (by intro _ _ _ same; cases same) answer
            · rw [noteReached_idle idleAbsorb notBind, Trace.record_cache, same]
              exact agrees.reachedIff state history

end AdversaryStep

end ZkcSecurity.HashChain
