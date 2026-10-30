module

public import ZkcSecurity.ProgramLogic.Transcript.Typed

@[expose] public section

/-! Provider simulations and their query-cost relation.

A provider realizes the ideal history oracle with primitive calls: compressions,
permutations or byte hashes, carrying chain or sponge states between calls. A
provider simulation relates the concrete experiment, in which the adversary
calls the primitive families directly and the verifier runs the provider, to the
ideal experiment over the history oracle of `ZkcSecurity.FiatShamir.Typed`. It
is stated for one property, one provider and one class of bounded executions.
This module fixes its type; it states no simulation of a particular provider.

- `Budget Family`: the primitive calls an adversary may make on every path, per
  primitive family. `FamilyQueryBound` is that bound on an oracle computation,
  and it implies a total bound of the summed budget
  (`FamilyQueryBound.isTotalQueryBound`); `chargedBudget` sums it over selected
  families.
- `Expansion.total`: the primitive calls of one verifier run within an
  execution bound, initialization included:
  `initialization + Σ_e n_e · v_e + Σ_r n_r · v_r`, with `v_e` and `v_r` the calls
  per absorbed event kind and per request kind and `n_e`, `n_r` their
  occurrence counts at the bound's maxima.
- `QueryCost`: the budget translation `cost : Budget Family → ℕ` (monotone), the
  verifier expansion `expansion : ExecBound → ℕ` and the loss
  `loss : Budget Family → ℕ → ENNReal`, applied to the adversary's budget and
  the verifier expansion. `QueryCost.ofCounts` aggregates an `Expansion` over
  the counts of each execution bound.
- A `Simulator` answers each primitive call of a concrete adversary from the
  history oracle, its own state and a private tape. In a state, a call either
  belongs to an **attempt**, the TranscriptQuery `key` it realizes, or is
  answered privately with no TranscriptQuery (for example a fresh digest for a
  query at a state no history reaches). A call of an attempt whose answer is
  not recorded asks the history oracle at `key` and records the answer; a call
  of an attempt whose answer is recorded reuses it through `shared`
  (`handle_fresh`, `handle_recorded`, `handle_private`, `attempt_answer`). The
  simulator's laws make this charge each attempt once: no answer is recorded
  at the start (`recorded_start`); recording and private replies keep the
  other recorded answers (`recorded_persists`) and keep every call assigned to
  an attempt assigned to it (`attempt_record`, `attempt_respond`, hence
  `attempt_persists`), so a repeated call stays in its attempt; and the calls
  the simulator declares to make up one concrete attempt (`together`, such as
  both calls of a split-hash grinding attempt or the counter blocks of an
  extended output) belong to one attempt in every state (`attempt_together`).
- `Simulator.Runs` records the calls of a path with the attempt each belonged
  to and its reply. On every run, an ideal answer is recorded exactly for the
  attempts of earlier calls, so the first call of an attempt, whichever call of
  the attempt it is, makes exactly the attempt's TranscriptQuery
  (`Runs.first_call`) and every later call reuses its answer
  (`Runs.later_call`); any two calls of one attempt, in either order and with
  any calls between them, are answered from one ideal answer
  (`Runs.shared_answer`); and a call made after a call of the same concrete
  attempt belongs to the earlier call's attempt (`Runs.constituent_attempt`).
  Every path of the translated program is a run (`translate_runs`). The laws
  constrain calls assigned to an attempt; a call answered privately may later
  join one, as a query at a state that a later answer reaches does, and any
  difference this makes from the concrete primitive is charged to the
  simulation's loss.
- `Simulator.translate` runs the adversary against the simulator: a
  deterministic oracle program over the history oracle for each tape. Each
  primitive call makes at most one TranscriptQuery, and none outside the
  families that carry attempts (`Simulator.translate_queryBound`).
- `Simulation`: a tape type per budget (private randomness, drawn uniformly
  before the oracle computation and never charged), the simulator, the families
  that carry attempts, the query-cost relation with `cost` covering their budget,
  and the inequality

  ```text
  concreteFailure A b ≤ idealFailure (translate q A) b + loss q (expansion b)
  ```

  for every adversary `A` within the budget `q` and every execution bound `b`,
  where `translate q A` draws the tape and runs the translated program. The
  verifier's own TranscriptQueries are charged on the ideal side by the typed
  engine's validator cost, not by `cost`.

Every translated program in the support of `translate q A` has at most
`cost q` TranscriptQueries on every path (`Simulation.transport`), hence the
typed engine's weighted budget (`Simulation.weightedBudget`). An ideal bound for
mixtures of provers bounded on their support transfers to the concrete
experiment with the loss added (`Simulation.concrete_le`); the typed engine's
theorems for such mixtures are such bounds, for a fixed statement
(`randomized_soundness_of_queryBound`, from `Typed.randomized_soundness_weighted`)
and for statements each prover chooses after its queries
(`randomized_adaptive_soundness_of_queryBound`; with a weighted budget,
`Typed.randomized_adaptive_soundness_weighted`).
-/

set_option autoImplicit false

namespace ZkcSecurity.FiatShamir.Provider
open OracleComp OracleSpec

/-- The primitive calls an adversary may make on every path, per primitive
family. -/
abbrev Budget (Family : Type) := Family → ℕ

section Bounds
variable {ι Family α : Type} {spec : OracleSpec ι} [DecidableEq Family]

/-- At most `budget f` calls of each primitive family `f` on every path, where
`family` sends a primitive query to its family. -/
def FamilyQueryBound (family : ι → Family) (computation : OracleComp spec α)
    (budget : Budget Family) : Prop :=
  IsQueryBound computation budget (fun query remaining => 0 < remaining (family query))
    (fun query remaining =>
      Function.update remaining (family query) (remaining (family query) - 1))

theorem familyQueryBound_query_bind_iff (family : ι → Family) {query : ι}
    {next : spec query → OracleComp spec α} {budget : Budget Family} :
    FamilyQueryBound family (liftM (spec.query query) >>= next) budget ↔
      0 < budget (family query) ∧ ∀ reply, FamilyQueryBound family (next reply)
        (Function.update budget (family query) (budget (family query) - 1)) :=
  Iff.rfl

/-- A bound per family bounds the total number of calls by the summed budget. -/
theorem FamilyQueryBound.isTotalQueryBound [Fintype Family] (family : ι → Family) :
    ∀ (computation : OracleComp spec α) (budget : Budget Family),
      FamilyQueryBound family computation budget →
        IsTotalQueryBound computation (∑ kind, budget kind) := by
  intro computation
  induction computation using OracleComp.inductionOn with
  | pure value => intro _ _; trivial
  | query_bind query next ih =>
      intro budget bounded
      obtain ⟨positive, rest⟩ := (familyQueryBound_query_bind_iff family).mp bounded
      have member : family query ∈ (Finset.univ : Finset Family) := Finset.mem_univ _
      have total : ∑ kind, budget kind = budget (family query) +
          ∑ kind ∈ Finset.univ.erase (family query), budget kind :=
        (Finset.add_sum_erase _ _ member).symm
      have updated : ∑ kind, Function.update budget (family query)
          (budget (family query) - 1) kind =
          (budget (family query) - 1) + ∑ kind ∈ Finset.univ.erase (family query), budget kind := by
        rw [Finset.sum_update_of_mem member, Finset.sdiff_singleton_eq_erase]
      refine isTotalQueryBound_query_bind_iff.mpr ⟨?_, fun reply => ?_⟩
      · rw [total]
        omega
      · have bound := ih reply _ (rest reply)
        rw [updated] at bound
        refine bound.mono (le_of_eq ?_)
        rw [total]
        omega

/-- The budget summed over the families `charged` selects. -/
def chargedBudget [Fintype Family] (charged : Family → Prop) [DecidablePred charged]
    (budget : Budget Family) : ℕ :=
  ∑ kind ∈ Finset.univ.filter charged, budget kind

/-- Spending one call of a charged family lowers the charged budget by one. -/
theorem chargedBudget_update_charged [Fintype Family] {charged : Family → Prop}
    [DecidablePred charged] {budget : Budget Family} {kind : Family} (selected : charged kind)
    (positive : 0 < budget kind) :
    chargedBudget charged (Function.update budget kind (budget kind - 1)) + 1 =
      chargedBudget charged budget := by
  have member : kind ∈ Finset.univ.filter charged := by simp [selected]
  unfold chargedBudget
  rw [Finset.sum_update_of_mem member, ← Finset.add_sum_erase _ _ member,
    Finset.sdiff_singleton_eq_erase]
  omega

/-- Spending one call of another family leaves the charged budget unchanged. -/
theorem chargedBudget_update_uncharged [Fintype Family] {charged : Family → Prop}
    [DecidablePred charged] {budget : Budget Family} {kind : Family} (other : ¬ charged kind)
    (calls : ℕ) :
    chargedBudget charged (Function.update budget kind calls) = chargedBudget charged budget := by
  unfold chargedBudget
  refine Finset.sum_congr rfl fun member selected => ?_
  have different : member ≠ kind := by
    rintro rfl
    exact other (Finset.mem_filter.mp selected).2
  exact Function.update_of_ne different _ _

end Bounds

section Expansion

/-- Occurrence counts of absorbed event kinds and request kinds in one verifier
run at an execution bound's maxima. -/
structure ExecutionCounts (EventKind RequestKind : Type) where
  events : EventKind → ℕ
  requests : RequestKind → ℕ

/-- A provider's primitive calls at initialization, per absorbed event kind and
per request kind. -/
structure Expansion (EventKind RequestKind : Type) where
  initialization : ℕ
  perEvent : EventKind → ℕ
  perRequest : RequestKind → ℕ

variable {EventKind RequestKind : Type} [Fintype EventKind] [Fintype RequestKind]

/-- The primitive calls of one verifier run within the counts, initialization
included. -/
def Expansion.total (expansion : Expansion EventKind RequestKind)
    (counts : ExecutionCounts EventKind RequestKind) : ℕ :=
  expansion.initialization + ∑ kind, counts.events kind * expansion.perEvent kind +
    ∑ kind, counts.requests kind * expansion.perRequest kind

/-- Initialization is part of every run's expansion. -/
theorem Expansion.initialization_le_total (expansion : Expansion EventKind RequestKind)
    (counts : ExecutionCounts EventKind RequestKind) :
    expansion.initialization ≤ expansion.total counts := by
  unfold Expansion.total
  omega

end Expansion

/-- The query-cost relation of a provider simulation, as consumed: the
TranscriptQuery budget `cost q` of the translated adversary for a primitive
budget `q` (monotone), the primitive calls `expansion b` of one verifier run
within the execution bound `b`, and the loss `loss q (expansion b)`. -/
structure QueryCost (Family ExecBound : Type) where
  cost : Budget Family → ℕ
  monotone : Monotone cost
  expansion : ExecBound → ℕ
  loss : Budget Family → ℕ → ENNReal

/-- A query-cost relation whose verifier expansion aggregates a provider's
per-step calls over the occurrence counts of each execution bound. -/
def QueryCost.ofCounts {Family ExecBound EventKind RequestKind : Type} [Fintype EventKind]
    [Fintype RequestKind] (cost : Budget Family → ℕ) (monotone : Monotone cost)
    (expansion : Expansion EventKind RequestKind)
    (counts : ExecBound → ExecutionCounts EventKind RequestKind)
    (loss : Budget Family → ℕ → ENNReal) : QueryCost Family ExecBound where
  cost := cost
  monotone := monotone
  expansion executions := expansion.total (counts executions)
  loss := loss

section Simulators
variable {ι D : Type} {primitive : OracleSpec ι} {R : D → Type} {Tape : Type}

/-- A simulator of the primitive families from the history oracle `OracleSpec.ofFn R`,
its own state and a private tape. -/
structure Simulator (primitive : OracleSpec ι) (R : D → Type) (Tape : Type) where
  /-- The simulator's state: its tables, its position on the tape and the ideal
  answers it has recorded. -/
  State : Type
  /-- The state before the first call, from the private tape. -/
  start : Tape → State
  /-- The attempt a call belongs to in a state: the TranscriptQuery it realizes,
  or none for a call the simulator answers privately. -/
  attempt : State → ι → Option D
  /-- The ideal answer the state records for a key. -/
  recorded : State → (key : D) → Option (R key)
  /-- Record the ideal answer of a key. -/
  record : State → (key : D) → R key → State
  /-- The reply to a call of the attempt `key`, read from the attempt's ideal
  answer. -/
  shared : (query : ι) → (key : D) → R key → primitive.Range query
  /-- The reply to a call outside every attempt and the successor state; no
  TranscriptQuery. -/
  respond : State → (query : ι) → primitive.Range query × State
  /-- Calls that make up one concrete attempt together, such as the two calls of
  a split-hash grinding attempt or the counter blocks of an extended output. -/
  together : ι → ι → Prop
  /-- No ideal answer is recorded before the first call. -/
  recorded_start : ∀ tape key, recorded (start tape) key = none
  recorded_record : ∀ state key answer, recorded (record state key answer) key = some answer
  recorded_record_of_ne : ∀ state key other answer, other ≠ key →
    recorded (record state key answer) other = recorded state other
  recorded_respond : ∀ state query key, recorded (respond state query).2 key = recorded state key
  /-- A call assigned to an attempt stays assigned to it after a recorded
  answer. -/
  attempt_record : ∀ state key answer query attemptKey, attempt state query = some attemptKey →
    attempt (record state key answer) query = some attemptKey
  /-- A call assigned to an attempt stays assigned to it after a private reply. -/
  attempt_respond : ∀ state call query attemptKey, attempt state query = some attemptKey →
    attempt (respond state call).2 query = some attemptKey
  /-- The calls of one concrete attempt belong to the same attempt in every
  state. -/
  attempt_together : ∀ state query other, together query other →
    attempt state query = attempt state other

namespace Simulator
variable (simulator : Simulator primitive R Tape)

/-- The simulator's answer to one primitive call: the first call of an attempt
asks the history oracle at the attempt's key and records the answer; a later
call of the attempt reuses the recorded answer; a call outside every attempt is
answered privately. -/
def handle : QueryImpl primitive (StateT simulator.State (OracleComp (OracleSpec.ofFn R))) :=
  fun query state =>
    match simulator.attempt state query with
    | some key =>
        match simulator.recorded state key with
        | some ideal => pure (simulator.shared query key ideal, state)
        | none =>
            (fun ideal => (simulator.shared query key ideal, simulator.record state key ideal)) <$>
              liftM ((OracleSpec.ofFn R).query key)
    | none => pure (simulator.respond state query)

/-- The first call of an attempt makes exactly the attempt's TranscriptQuery and
records its answer. -/
theorem handle_fresh {query : ι} {state : simulator.State} {key : D}
    (belongs : simulator.attempt state query = some key) (fresh : simulator.recorded state key = none) :
    (simulator.handle query).run state =
      (fun ideal => (simulator.shared query key ideal, simulator.record state key ideal)) <$>
        liftM ((OracleSpec.ofFn R).query key) := by
  change (match simulator.attempt state query with
    | some key =>
        match simulator.recorded state key with
        | some ideal => pure (simulator.shared query key ideal, state)
        | none =>
            (fun ideal => (simulator.shared query key ideal, simulator.record state key ideal)) <$>
              liftM ((OracleSpec.ofFn R).query key)
    | none => pure (simulator.respond state query)) = _
  rw [belongs]
  simp only [fresh]

/-- A later call of a recorded attempt makes no TranscriptQuery and is answered
from the recorded answer. -/
theorem handle_recorded {query : ι} {state : simulator.State} {key : D} {ideal : R key}
    (belongs : simulator.attempt state query = some key)
    (recorded : simulator.recorded state key = some ideal) :
    (simulator.handle query).run state = pure (simulator.shared query key ideal, state) := by
  change (match simulator.attempt state query with
    | some key =>
        match simulator.recorded state key with
        | some ideal => pure (simulator.shared query key ideal, state)
        | none =>
            (fun ideal => (simulator.shared query key ideal, simulator.record state key ideal)) <$>
              liftM ((OracleSpec.ofFn R).query key)
    | none => pure (simulator.respond state query)) = _
  rw [belongs]
  simp only [recorded]

/-- A call outside every attempt makes no TranscriptQuery. -/
theorem handle_private {query : ι} {state : simulator.State}
    (outside : simulator.attempt state query = none) :
    (simulator.handle query).run state = pure (simulator.respond state query) := by
  change (match simulator.attempt state query with
    | some key =>
        match simulator.recorded state key with
        | some ideal => pure (simulator.shared query key ideal, state)
        | none =>
            (fun ideal => (simulator.shared query key ideal, simulator.record state key ideal)) <$>
              liftM ((OracleSpec.ofFn R).query key)
    | none => pure (simulator.respond state query)) = _
  rw [outside]

/-- Shared-answer consistency for one call: once `ideal` is recorded for an
attempt, a call of that attempt is answered from `ideal` and the recorded answer
stays. Over a whole run, `Runs.later_call` and `Runs.shared_answer` derive the
same consistency for every call of the attempt, whichever call came first. -/
theorem attempt_answer {query : ι} {state : simulator.State} {key : D} {ideal : R key}
    (belongs : simulator.attempt state query = some key)
    (recorded : simulator.recorded state key = some ideal) :
    ∀ result ∈ support ((simulator.handle query).run state),
      result.1 = simulator.shared query key ideal ∧ simulator.recorded result.2 key = some ideal := by
  rw [simulator.handle_recorded belongs recorded]
  intro result member
  rw [support_pure, Set.mem_singleton_iff] at member
  subst member
  exact ⟨rfl, recorded⟩

/-- A recorded ideal answer persists through every call, so later calls of its
attempt, interleaved with any other calls, are answered from it
(`attempt_answer`, `Runs.later_call`). -/
theorem recorded_persists {query : ι} {state : simulator.State} {key : D} {ideal : R key}
    (recorded : simulator.recorded state key = some ideal) :
    ∀ result ∈ support ((simulator.handle query).run state),
      simulator.recorded result.2 key = some ideal := by
  intro result member
  rcases belongs : simulator.attempt state query with _ | other
  · rw [simulator.handle_private belongs, support_pure, Set.mem_singleton_iff] at member
    subst member
    rw [simulator.recorded_respond]
    exact recorded
  · rcases otherRecorded : simulator.recorded state other with _ | answer
    · rw [simulator.handle_fresh belongs otherRecorded, support_map] at member
      obtain ⟨fresh, _, rfl⟩ := member
      have different : key ≠ other := by
        rintro rfl
        rw [recorded] at otherRecorded
        cases otherRecorded
      rw [simulator.recorded_record_of_ne _ _ _ _ different]
      exact recorded
    · rw [simulator.handle_recorded belongs otherRecorded, support_pure,
        Set.mem_singleton_iff] at member
      subst member
      exact recorded

/-- Assignments to attempts persist through every call. -/
theorem attempt_persists {query other : ι} {state : simulator.State} {key : D}
    (assigned : simulator.attempt state other = some key) :
    ∀ result ∈ support ((simulator.handle query).run state),
      simulator.attempt result.2 other = some key := by
  intro result member
  rcases belongs : simulator.attempt state query with _ | attemptKey
  · rw [simulator.handle_private belongs, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact simulator.attempt_respond _ _ _ _ assigned
  · rcases recorded : simulator.recorded state attemptKey with _ | ideal
    · rw [simulator.handle_fresh belongs recorded, support_map] at member
      obtain ⟨fresh, _, rfl⟩ := member
      exact simulator.attempt_record _ _ _ _ _ assigned
    · rw [simulator.handle_recorded belongs recorded, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact assigned

/-- One call makes at most one TranscriptQuery, and none outside an attempt. -/
theorem handle_queryBound (query : ι) (state : simulator.State) :
    IsTotalQueryBound ((simulator.handle query).run state)
      (if (simulator.attempt state query).isSome then 1 else 0) := by
  rcases belongs : simulator.attempt state query with _ | key
  · rw [simulator.handle_private belongs]
    trivial
  · rcases recorded : simulator.recorded state key with _ | ideal
    · rw [simulator.handle_fresh belongs recorded, map_eq_bind_pure_comp]
      exact isTotalQueryBound_query_bind_iff.mpr ⟨Nat.one_pos, fun _ => trivial⟩
    · rw [simulator.handle_recorded belongs recorded]
      trivial

/-! #### Runs

A run is the sequence of calls a path of the translated program makes, each
with the attempt it belonged to when it was made and its reply. On every run:
assignments to attempts persist; an ideal answer is recorded exactly for the
attempts of earlier calls, since none is recorded at the start; every recorded
answer is the one that every call of its attempt was answered from; and a call
made after a call of the same concrete attempt belongs to that call's attempt.
Hence the first call of an attempt on a path, whichever call of the attempt it
is, makes exactly the attempt's TranscriptQuery (`Runs.first_call`), every later
call reuses its answer (`Runs.later_call`), and any two calls of one attempt, in
either order and with any calls between them, are answered from one ideal
answer (`Runs.shared_answer`, `Runs.constituent_attempt`). Every path of the
translated program is a run (`Runs.run`, `translate_runs`). -/

/-- Calls that belong to one concrete attempt: the same call repeated, or calls
the simulator declares to make up one attempt, in either order. -/
def Constituents (query other : ι) : Prop :=
  query = other ∨ simulator.together query other ∨ simulator.together other query

theorem Constituents.symm {query other : ι} (constituents : simulator.Constituents query other) :
    simulator.Constituents other query := by
  rcases constituents with rfl | together | together
  · exact Or.inl rfl
  · exact Or.inr (Or.inr together)
  · exact Or.inr (Or.inl together)

/-- Constituent calls belong to one attempt in every state. -/
theorem attempt_constituents {query other : ι} (constituents : simulator.Constituents query other)
    (state : simulator.State) : simulator.attempt state query = simulator.attempt state other := by
  rcases constituents with rfl | together | together
  · rfl
  · exact simulator.attempt_together state query other together
  · exact (simulator.attempt_together state other query together).symm

end Simulator

/-- One answered call on a path: the call, the attempt it belonged to in the
state where it was made, and its reply. -/
structure Answered (primitive : OracleSpec ι) (D : Type) where
  query : ι
  attempt : Option D
  reply : primitive.Range query

namespace Simulator
variable (simulator : Simulator primitive R Tape)

/-- The runs of the simulator from a tape: the answered calls of a path and the
state after them. -/
inductive Runs (tape : Tape) : List (Answered primitive D) → simulator.State → Prop
  | start : Runs tape [] (simulator.start tape)
  | step {trace : List (Answered primitive D)} {state : simulator.State} {query : ι}
      {result : primitive.Range query × simulator.State} :
      Runs tape trace state → result ∈ support ((simulator.handle query).run state) →
        Runs tape (trace ++ [⟨query, simulator.attempt state query, result.1⟩]) result.2

/-- The invariant of runs: persistent assignments, recorded answers exactly for
the attempts of earlier calls, consistent replies, and constituent calls in the
attempt of the earlier one. -/
def RunInvariant (trace : List (Answered primitive D)) (state : simulator.State) : Prop :=
  (∀ entry ∈ trace, ∀ key, entry.attempt = some key → simulator.attempt state entry.query = some key) ∧
    (∀ key, (simulator.recorded state key).isSome ↔ ∃ entry ∈ trace, entry.attempt = some key) ∧
    (∀ key ideal, simulator.recorded state key = some ideal → ∀ entry ∈ trace,
      entry.attempt = some key → entry.reply = simulator.shared entry.query key ideal) ∧
    trace.Pairwise fun first second => simulator.Constituents first.query second.query →
      ∀ key, first.attempt = some key → second.attempt = some key

theorem Runs.invariant {tape : Tape} {trace : List (Answered primitive D)}
    {state : simulator.State} (runs : simulator.Runs tape trace state) :
    simulator.RunInvariant trace state := by
  induction runs with
  | start =>
      refine ⟨fun _ member => absurd member List.not_mem_nil, fun key => ?_,
        fun _ _ _ _ member => absurd member List.not_mem_nil, List.Pairwise.nil⟩
      simp [simulator.recorded_start]
  | @step trace state query result _ member ih =>
      obtain ⟨persists, provenance, consistent, ordered⟩ := ih
      have later : ∀ entry ∈ trace, ∀ key, entry.attempt = some key →
          simulator.attempt result.2 entry.query = some key :=
        fun entry inTrace key assigned =>
          simulator.attempt_persists (persists entry inTrace key assigned) result member
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro entry inTrace key assigned
        rcases List.mem_append.mp inTrace with old | new
        · exact later entry old key assigned
        · rw [List.mem_singleton] at new
          subst new
          exact simulator.attempt_persists assigned result member
      · intro key
        simp only [List.mem_append, List.mem_singleton]
        rcases belongs : simulator.attempt state query with _ | attemptKey
        · rw [simulator.handle_private belongs, support_pure, Set.mem_singleton_iff] at member
          subst member
          rw [simulator.recorded_respond, provenance key]
          constructor
          · rintro ⟨entry, inTrace, assigned⟩
            exact ⟨entry, Or.inl inTrace, assigned⟩
          · rintro ⟨entry, inTrace | rfl, assigned⟩
            · exact ⟨entry, inTrace, assigned⟩
            · dsimp only at assigned
              cases assigned
        · rcases recorded : simulator.recorded state attemptKey with _ | ideal
          · rw [simulator.handle_fresh belongs recorded, support_map] at member
            obtain ⟨fresh, _, rfl⟩ := member
            by_cases same : key = attemptKey
            · subst same
              rw [simulator.recorded_record]
              simp
            · rw [simulator.recorded_record_of_ne _ _ _ _ same, provenance key]
              constructor
              · rintro ⟨entry, inTrace, assigned⟩
                exact ⟨entry, Or.inl inTrace, assigned⟩
              · rintro ⟨entry, inTrace | rfl, assigned⟩
                · exact ⟨entry, inTrace, assigned⟩
                · dsimp only at assigned
                  exact absurd (Option.some.inj assigned).symm same
          · rw [simulator.handle_recorded belongs recorded, support_pure,
              Set.mem_singleton_iff] at member
            subst member
            rw [provenance key]
            constructor
            · rintro ⟨entry, inTrace, assigned⟩
              exact ⟨entry, Or.inl inTrace, assigned⟩
            · rintro ⟨entry, inTrace | rfl, assigned⟩
              · exact ⟨entry, inTrace, assigned⟩
              · dsimp only at assigned
                obtain rfl := Option.some.inj assigned
                exact (provenance attemptKey).mp (by simp [recorded])
      · intro key ideal recordedNow entry inTrace assigned
        rcases belongs : simulator.attempt state query with _ | attemptKey
        · rw [simulator.handle_private belongs, support_pure, Set.mem_singleton_iff] at member
          subst member
          rw [simulator.recorded_respond] at recordedNow
          rcases List.mem_append.mp inTrace with old | new
          · exact consistent key ideal recordedNow entry old assigned
          · rw [List.mem_singleton] at new
            subst new
            change simulator.attempt state query = some key at assigned
            rw [belongs] at assigned
            cases assigned
        · rcases recorded : simulator.recorded state attemptKey with _ | stored
          · rw [simulator.handle_fresh belongs recorded, support_map] at member
            obtain ⟨fresh, _, rfl⟩ := member
            by_cases same : key = attemptKey
            · subst same
              rw [simulator.recorded_record] at recordedNow
              cases recordedNow
              rcases List.mem_append.mp inTrace with old | new
              · have absent := (provenance key).mpr ⟨entry, old, assigned⟩
                rw [recorded] at absent
                cases absent
              · rw [List.mem_singleton] at new
                subst new
                rfl
            · rw [simulator.recorded_record_of_ne _ _ _ _ same] at recordedNow
              rcases List.mem_append.mp inTrace with old | new
              · exact consistent key ideal recordedNow entry old assigned
              · rw [List.mem_singleton] at new
                subst new
                change simulator.attempt state query = some key at assigned
                rw [belongs] at assigned
                exact absurd (Option.some.inj assigned).symm same
          · rw [simulator.handle_recorded belongs recorded, support_pure,
              Set.mem_singleton_iff] at member
            subst member
            rcases List.mem_append.mp inTrace with old | new
            · exact consistent key ideal recordedNow entry old assigned
            · rw [List.mem_singleton] at new
              subst new
              change simulator.attempt state query = some key at assigned
              rw [belongs] at assigned
              obtain rfl := Option.some.inj assigned
              rw [recorded] at recordedNow
              cases recordedNow
              rfl
      · refine List.pairwise_append.mpr ⟨ordered, List.pairwise_singleton _ _, ?_⟩
        intro first inTrace second new constituents key assigned
        rw [List.mem_singleton] at new
        subst new
        exact (simulator.attempt_constituents constituents state).symm.trans
          (persists first inTrace key assigned)

/-- First-call charging: on a run, the first call of an attempt, whichever call
of the attempt it is, makes exactly the attempt's TranscriptQuery and records
its answer. -/
theorem Runs.first_call {tape : Tape} {trace : List (Answered primitive D)}
    {state : simulator.State} (runs : simulator.Runs tape trace state) {query : ι} {key : D}
    (belongs : simulator.attempt state query = some key)
    (first : ∀ entry ∈ trace, entry.attempt ≠ some key) :
    (simulator.handle query).run state =
      (fun ideal => (simulator.shared query key ideal, simulator.record state key ideal)) <$>
        liftM ((OracleSpec.ofFn R).query key) := by
  refine simulator.handle_fresh belongs ?_
  rcases recorded : simulator.recorded state key with _ | ideal
  · rfl
  · obtain ⟨entry, inTrace, assigned⟩ :=
      ((Runs.invariant simulator runs).2.1 key).mp (by simp [recorded])
    exact absurd assigned (first entry inTrace)

/-- A later call of an attempt makes no TranscriptQuery and is answered from the
answer every earlier call of the attempt was answered from. -/
theorem Runs.later_call {tape : Tape} {trace : List (Answered primitive D)}
    {state : simulator.State} (runs : simulator.Runs tape trace state) {query : ι} {key : D}
    (belongs : simulator.attempt state query = some key) {entry : Answered primitive D}
    (inTrace : entry ∈ trace) (assigned : entry.attempt = some key) :
    ∃ ideal, (simulator.handle query).run state = pure (simulator.shared query key ideal, state) ∧
      entry.reply = simulator.shared entry.query key ideal := by
  obtain ⟨_, provenance, consistent, _⟩ := Runs.invariant simulator runs
  obtain ⟨ideal, recorded⟩ := Option.isSome_iff_exists.mp
    ((provenance key).mpr ⟨entry, inTrace, assigned⟩)
  exact ⟨ideal, simulator.handle_recorded belongs recorded,
    consistent key ideal recorded entry inTrace assigned⟩

/-- Shared-answer consistency on a run: any two calls of one attempt, in either
order and with any calls between them, are answered from one ideal answer. -/
theorem Runs.shared_answer {tape : Tape} {trace : List (Answered primitive D)}
    {state : simulator.State} (runs : simulator.Runs tape trace state) {key : D}
    {first second : Answered primitive D} (firstIn : first ∈ trace) (secondIn : second ∈ trace)
    (firstAssigned : first.attempt = some key) (secondAssigned : second.attempt = some key) :
    ∃ ideal, first.reply = simulator.shared first.query key ideal ∧
      second.reply = simulator.shared second.query key ideal := by
  obtain ⟨_, provenance, consistent, _⟩ := Runs.invariant simulator runs
  obtain ⟨ideal, recorded⟩ := Option.isSome_iff_exists.mp
    ((provenance key).mpr ⟨first, firstIn, firstAssigned⟩)
  exact ⟨ideal, consistent key ideal recorded first firstIn firstAssigned,
    consistent key ideal recorded second secondIn secondAssigned⟩

/-- Attempt identity on a run: a call made after a call of the same concrete
attempt, the same call repeated or a declared constituent in either order,
belongs to the earlier call's attempt. -/
theorem Runs.constituent_attempt {tape : Tape} {before after : List (Answered primitive D)}
    {state : simulator.State} {first second : Answered primitive D}
    (runs : simulator.Runs tape (before ++ first :: after) state) (secondIn : second ∈ after)
    (constituents : simulator.Constituents first.query second.query) {key : D}
    (assigned : first.attempt = some key) : second.attempt = some key := by
  have ordered := (Runs.invariant simulator runs).2.2.2
  rw [List.pairwise_append, List.pairwise_cons] at ordered
  exact ordered.2.1.1 second secondIn constituents key assigned

/-- Answer sharing under interleaving and reversal: when a call of a concrete
attempt is followed, after any other calls, by a constituent of it, the same
call repeated or a declared constituent in either order, both are answered from
one ideal answer. -/
theorem Runs.constituents_share {tape : Tape} {before after : List (Answered primitive D)}
    {state : simulator.State} {first second : Answered primitive D}
    (runs : simulator.Runs tape (before ++ first :: after) state) (secondIn : second ∈ after)
    (constituents : simulator.Constituents first.query second.query) {key : D}
    (assigned : first.attempt = some key) :
    ∃ ideal, first.reply = simulator.shared first.query key ideal ∧
      second.reply = simulator.shared second.query key ideal :=
  Runs.shared_answer simulator runs (by simp) (by simp [secondIn]) assigned
    (Runs.constituent_attempt simulator runs secondIn constituents assigned)

/-- Every path of an adversary run against the simulator from a run's state
extends that run. -/
theorem Runs.run {tape : Tape} {α : Type} :
    ∀ (adversary : OracleComp primitive α) (trace : List (Answered primitive D))
      (state : simulator.State), simulator.Runs tape trace state →
        ∀ result ∈ support ((simulateQ simulator.handle adversary).run state),
          ∃ more, simulator.Runs tape (trace ++ more) result.2 := by
  intro adversary
  induction adversary using OracleComp.inductionOn with
  | pure value =>
      intro trace state runs result member
      rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact ⟨[], by simpa using runs⟩
  | query_bind query next ih =>
      intro trace state runs result member
      rw [simulateQ_query_bind, StateT.run_bind, support_bind] at member
      simp only [Set.mem_iUnion] at member
      obtain ⟨step, stepMember, member⟩ := member
      obtain ⟨more, extended⟩ := ih step.1 _ step.2 (Runs.step runs stepMember) result member
      exact ⟨_ :: more, by simpa using extended⟩

/-- The translated program's paths are runs from the tape. -/
theorem translate_runs {α : Type} (adversary : OracleComp primitive α) (tape : Tape) :
    ∀ result ∈ support ((simulateQ simulator.handle adversary).run (simulator.start tape)),
      ∃ trace, simulator.Runs tape trace result.2 := by
  intro result member
  obtain ⟨trace, runs⟩ := Runs.run simulator adversary [] _ Runs.start result member
  exact ⟨trace, by simpa using runs⟩

/-- The translated program for a tape: the adversary run against the simulator,
a deterministic oracle program over the history oracle. -/
def translate {α : Type} (adversary : OracleComp primitive α) (tape : Tape) :
    OracleComp (OracleSpec.ofFn R) α :=
  (simulateQ simulator.handle adversary).run' (simulator.start tape)

variable {Family : Type} [DecidableEq Family] [Fintype Family]

/-- A bound per family on the adversary bounds the translated program's
TranscriptQueries by the budget of the families that carry attempts. -/
theorem run_queryBound (family : ι → Family) (charged : Family → Prop)
    [decidable : DecidablePred charged]
    (carries : ∀ state query key, simulator.attempt state query = some key → charged (family query))
    {α : Type} :
    ∀ (adversary : OracleComp primitive α) (budget : Budget Family) (state : simulator.State),
      FamilyQueryBound family adversary budget →
        IsTotalQueryBound ((simulateQ simulator.handle adversary).run state)
          (chargedBudget charged budget) := by
  intro adversary
  induction adversary using OracleComp.inductionOn with
  | pure value => intro _ _ _; trivial
  | query_bind query next ih =>
      intro budget state bounded
      obtain ⟨positive, rest⟩ := (familyQueryBound_query_bind_iff family).mp bounded
      rw [simulateQ_query_bind, StateT.run_bind]
      have step : IsTotalQueryBound
          ((liftM (simulator.handle query) :
            StateT simulator.State (OracleComp (OracleSpec.ofFn R)) (primitive.Range query)).run state)
          (if (simulator.attempt state query).isSome then 1 else 0) := by
        simpa [OracleComp.liftM_run_StateT, MonadLift.monadLift] using
          simulator.handle_queryBound query state
      have tail : ∀ result : primitive.Range query × simulator.State,
          IsTotalQueryBound ((simulateQ simulator.handle (next result.1)).run result.2)
            (chargedBudget charged
              (Function.update budget (family query) (budget (family query) - 1))) :=
        fun result => ih result.1 _ result.2 (rest result.1)
      refine (isTotalQueryBound_bind step tail).mono ?_
      by_cases inAttempt : (simulator.attempt state query).isSome
      · obtain ⟨key, belongs⟩ := Option.isSome_iff_exists.mp inAttempt
        simp only [inAttempt, ↓reduceIte]
        rw [← chargedBudget_update_charged (carries state query key belongs) positive]
        omega
      · simp only [inAttempt, Bool.false_eq_true, ↓reduceIte, zero_add]
        by_cases carried : charged (family query)
        · exact (Nat.le_succ _).trans
            (chargedBudget_update_charged carried positive).le
        · exact (chargedBudget_update_uncharged carried _).le

theorem translate_queryBound (family : ι → Family) (charged : Family → Prop)
    [decidable : DecidablePred charged]
    (carries : ∀ state query key, simulator.attempt state query = some key → charged (family query))
    {α : Type} (adversary : OracleComp primitive α) (budget : Budget Family)
    (bounded : FamilyQueryBound family adversary budget) (tape : Tape) :
    IsTotalQueryBound (simulator.translate adversary tape) (chargedBudget charged budget) := by
  unfold translate
  rw [StateT.run'_eq, map_eq_bind_pure_comp]
  have composed := isTotalQueryBound_bind (n₂ := 0) (ob := pure ∘ fun result => result.1)
    (simulator.run_queryBound family charged carries adversary budget (simulator.start tape) bounded)
    fun result => (show IsTotalQueryBound (pure result.1 : OracleComp (OracleSpec.ofFn R) α) 0
      from trivial)
  rwa [add_zero] at composed

end Simulator

end Simulators

/-- A provider simulation for one property, one provider and one class of
bounded executions. `concreteFailure A b` is the probability that the property
fails in the concrete experiment, with the adversary `A` calling the primitive
families and the verifier running the provider within the execution bound `b`.
`idealFailure provers b` is the same in the ideal experiment over the history
oracle `OracleSpec.ofFn R`, for a mixture of provers: private randomness drawn
before the oracle computation. -/
structure Simulation {ι D Family ExecBound α : Type} [DecidableEq Family] [Fintype Family]
    (primitive : OracleSpec ι) (family : ι → Family) (R : D → Type)
    (concreteFailure : OracleComp primitive α → ExecBound → ENNReal)
    (idealFailure : ProbComp (OracleComp (OracleSpec.ofFn R) α) → ExecBound → ENNReal) where
  /-- The private tape for adversaries within a budget. -/
  Tape : Budget Family → Type
  tapeSampleable : ∀ budget, SampleableType (Tape budget)
  /-- The simulator for adversaries within a budget. -/
  simulator : (budget : Budget Family) → Simulator primitive R (Tape budget)
  /-- The families whose calls may belong to an attempt. -/
  charged : Family → Prop
  chargedDecidable : DecidablePred charged
  carries : ∀ budget state query key, (simulator budget).attempt state query = some key →
    charged (family query)
  queryCost : QueryCost Family ExecBound
  covers : ∀ budget, (haveI := chargedDecidable; chargedBudget charged budget) ≤ queryCost.cost budget
  bound : ∀ adversary budget executions, FamilyQueryBound family adversary budget →
    concreteFailure adversary executions ≤
      idealFailure (haveI := tapeSampleable budget
        do let tape ← $ᵗ (Tape budget); pure ((simulator budget).translate adversary tape))
        executions + queryCost.loss budget (queryCost.expansion executions)

namespace Simulation
variable {ι D Family ExecBound α : Type} [DecidableEq Family] [Fintype Family]
  {primitive : OracleSpec ι} {family : ι → Family} {R : D → Type}
  {concreteFailure : OracleComp primitive α → ExecBound → ENNReal}
  {idealFailure : ProbComp (OracleComp (OracleSpec.ofFn R) α) → ExecBound → ENNReal}

/-- The translated adversary within a budget: draw the private tape, then run
the adversary against the simulator. -/
def translate (simulation : Simulation primitive family R concreteFailure idealFailure)
    (budget : Budget Family) (adversary : OracleComp primitive α) :
    ProbComp (OracleComp (OracleSpec.ofFn R) α) :=
  haveI := simulation.tapeSampleable budget
  do let tape ← $ᵗ (simulation.Tape budget); pure ((simulation.simulator budget).translate adversary tape)

/-- The simulation's inequality for the translated adversary. -/
theorem bound_translate (simulation : Simulation primitive family R concreteFailure idealFailure)
    (adversary : OracleComp primitive α) (budget : Budget Family) (executions : ExecBound)
    (within : FamilyQueryBound family adversary budget) :
    concreteFailure adversary executions ≤
      idealFailure (simulation.translate budget adversary) executions +
        simulation.queryCost.loss budget (simulation.queryCost.expansion executions) :=
  simulation.bound adversary budget executions within

/-- Every translated program makes at most `cost q` TranscriptQueries on every
path. -/
theorem transport (simulation : Simulation primitive family R concreteFailure idealFailure)
    (adversary : OracleComp primitive α) (budget : Budget Family)
    (within : FamilyQueryBound family adversary budget) :
    ∀ program ∈ support (simulation.translate budget adversary),
      IsTotalQueryBound program (simulation.queryCost.cost budget) := by
  intro program member
  simp only [translate, support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at member
  obtain ⟨tape, _, rfl⟩ := member
  exact ((simulation.simulator budget).translate_queryBound family simulation.charged
    (decidable := simulation.chargedDecidable) (simulation.carries budget) adversary budget within
    tape).mono (simulation.covers budget)

/-- Every translated program's charge on every path, each key weighted at most
`bound`, is at most its TranscriptQuery budget times `bound`: the weighted
budget of the typed engine. -/
theorem weightedBudget [∀ key, Nonempty (R key)]
    (simulation : Simulation primitive family R concreteFailure idealFailure)
    (weight : D → ENNReal) {bound : ENNReal} (bounded : ∀ key, weight key ≤ bound)
    (adversary : OracleComp primitive α) (budget : Budget Family)
    (within : FamilyQueryBound family adversary budget) :
    ∀ program ∈ support (simulation.translate budget adversary),
      WorstCaseCostBound program ⟨weight⟩ (simulation.queryCost.cost budget * bound) :=
  fun program member => Typed.worstCaseCostBound_of_isTotalQueryBound weight bounded _ _
    (simulation.transport adversary budget within program member)

/-- An ideal bound for mixtures of provers, each with at most `queries`
TranscriptQueries on its support, transfers to the concrete experiment with the
loss added. -/
theorem concrete_le (simulation : Simulation primitive family R concreteFailure idealFailure)
    {idealBound : ℕ → ExecBound → ENNReal}
    (ideal : ∀ provers queries executions,
      (∀ program ∈ support provers, IsTotalQueryBound program queries) →
        idealFailure provers executions ≤ idealBound queries executions)
    (adversary : OracleComp primitive α) (budget : Budget Family) (executions : ExecBound)
    (within : FamilyQueryBound family adversary budget) :
    concreteFailure adversary executions ≤
      idealBound (simulation.queryCost.cost budget) executions +
        simulation.queryCost.loss budget (simulation.queryCost.expansion executions) :=
  (simulation.bound_translate adversary budget executions within).trans
    (add_le_add_left (ideal _ _ executions (simulation.transport adversary budget within)) _)

end Simulation

section TypedEngine
variable {I : PIR.Signature} {E P A : Type} {Raw : E → Type} {R : List E → Type} [DecidableEq E]
  [Typed.ReadsByOccurrence R Raw] [∀ key, SampleableType (R key)]
  [∀ event, SampleableType (Raw event)]

/-- The typed engine's fixed-statement bound for a mixture of provers with at
most `queries` TranscriptQueries on every path of every prover in its support:
`(queries + budget) * bound` when every site's error is at most `bound`. -/
theorem randomized_soundness_of_queryBound {absorb : Typed.Interface I E P Raw} {accepts : A → Prop}
    {error : E → ENNReal} (certificate : Typed.Certificate absorb accepts error) {bound : ENNReal}
    (bounded : ∀ event, error event ≤ bound) (validator : PIR.Process I A)
    (doomedValidator : certificate.doomed validator) (budget : ℕ)
    (validatorBound : Typed.QueryBound absorb validator budget) (initial : List E)
    (provers : ProbComp (OracleComp (OracleSpec.ofFn R) (List P))) (queries : ℕ)
    (proverBound : ∀ prover ∈ support provers, IsTotalQueryBound prover queries) :
    Pr{let result ← provers >>= fun prover =>
        (simulateQ randomOracle (Typed.fixedExperiment absorb validator initial prover)).run' ∅}[
      Accepted accepts result.1] ≤ (queries + budget) * bound := by
  have keyBounded : ∀ key, Typed.keyError error key ≤ bound := by
    intro key
    unfold Typed.keyError
    split
    · exact bounded _
    · exact zero_le
  have total := Typed.randomized_soundness_weighted certificate validator doomedValidator
    (budget * bound) (Typed.QueryBound.costBound absorb error bounded validator budget validatorBound)
    initial provers (queries * bound) fun prover member =>
      Typed.worstCaseCostBound_of_isTotalQueryBound _ keyBounded prover queries
        (proverBound prover member)
  rwa [← add_mul] at total

/-- The typed engine's adaptive bound for a mixture of provers, each choosing
its statement after at most `queries` TranscriptQueries on every path:
`(queries + budget) * bound` when every site's error is at most `bound`. With a
simulation whose ideal failure is this experiment's, it is the ideal bound that
`Simulation.concrete_le` takes, at `queries = cost q`. -/
theorem randomized_adaptive_soundness_of_queryBound {Stmt : Type}
    {absorb : Typed.Interface I E P Raw} {accepts : A → Prop} {error : E → ENNReal}
    (certificate : Typed.Certificate absorb accepts error) {bound : ENNReal}
    (bounded : ∀ event, error event ≤ bound) (validator : Stmt → PIR.Process I A)
    (initial : Stmt → List E) (determined : Typed.Determined initial)
    (falseStatement : Stmt → Prop)
    (doomedValidator : ∀ statement, falseStatement statement →
      certificate.doomed (validator statement))
    (budget : ℕ) (validatorBound : ∀ statement, Typed.QueryBound absorb (validator statement) budget)
    (provers : ProbComp (OracleComp (OracleSpec.ofFn R) (Stmt × List P))) (queries : ℕ)
    (proverBound : ∀ prover ∈ support provers, IsTotalQueryBound prover queries) :
    Pr{let result ← provers >>= fun prover =>
        (simulateQ randomOracle (Typed.experiment absorb validator initial prover)).run' ∅}[
      falseStatement result.1 ∧ Accepted accepts result.2.1] ≤ (queries + budget) * bound :=
  prEvent_bind_le_of_forall_le_of_support _ _ _ fun prover drawn =>
    Typed.adaptive_soundness certificate bounded validator initial determined falseStatement
      doomedValidator budget validatorBound prover queries (proverBound prover drawn)

end TypedEngine

end ZkcSecurity.FiatShamir.Provider
