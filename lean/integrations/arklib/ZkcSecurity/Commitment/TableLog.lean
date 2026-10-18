module

public import VCVio.OracleComp.QueryTracking.RandomOracle.FreshQuery
public import VCVio.OracleComp.QueryTracking.LoggingOracle
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic

@[expose] public section

/-! # Runs against a complete answer table

The security argument for committed oracle messages evaluates an oracle computation against a
complete answer table and reads its query log (`OracleComp.tableQueryLog`). This module collects
the facts about such runs that the argument needs.

* `beforeFirst key log` is the part of a log before the first query of `key`. Answering `key`
  differently changes nothing before its first query (`beforeFirst_update`): whatever is computed
  from the record before a query is fixed before that query's answer is sampled. This is the
  extraction checkpoint convention: extraction for a transcript query runs on the record before
  its first query, so it cannot depend on that query's answer.
* Every entry of a table log carries the table's answer at its key (`tableQueryLog_consistent`).
* Logging with `withQueryLog` returns the table log (`evalWithAnswerFn_withQueryLog`) and makes
  no other query (`tableQueryLog_withQueryLog`).
* A total query bound bounds the length of every table log (`tableQueryLog_length_le`).
-/

set_option autoImplicit false

namespace ZkcSecurity.Commitment

open OracleComp OracleSpec

variable {D α β : Type} {R : D → Type}

/-- The entries of a query log strictly before the first query of `key`; the whole log when
`key` is never queried. -/
def beforeFirst [DecidableEq D] (key : D) : List ((d : D) × R d) → List ((d : D) × R d)
  | [] => []
  | entry :: rest => if entry.1 = key then [] else entry :: beforeFirst key rest

section BeforeFirst
variable [DecidableEq D]

@[simp] theorem beforeFirst_nil (key : D) : beforeFirst key ([] : List ((d : D) × R d)) = [] :=
  rfl

theorem beforeFirst_cons (key : D) (entry : (d : D) × R d) (rest : List ((d : D) × R d)) :
    beforeFirst key (entry :: rest) =
      if entry.1 = key then [] else entry :: beforeFirst key rest :=
  rfl

/-- The part before the first query is a prefix of the log. -/
theorem beforeFirst_prefix (key : D) :
    ∀ log : List ((d : D) × R d), beforeFirst key log <+: log
  | [] => List.prefix_rfl
  | entry :: rest => by
      rw [beforeFirst_cons]
      split
      · exact List.nil_prefix
      · exact List.cons_prefix_cons.mpr ⟨rfl, beforeFirst_prefix key rest⟩

/-- No entry before the first query of `key` queries `key`. -/
theorem key_ne_of_mem_beforeFirst (key : D) :
    ∀ (log : List ((d : D) × R d)) (entry : (d : D) × R d),
      entry ∈ beforeFirst key log → entry.1 ≠ key
  | [] => by simp
  | head :: rest => by
      intro entry member
      rw [beforeFirst_cons] at member
      split at member
      · simp at member
      · rcases List.mem_cons.mp member with same | later
        · subst same
          assumption
        · exact key_ne_of_mem_beforeFirst key rest entry later

/-- A log in which `key` is queried is the part before its first query, that query, and the
rest. -/
theorem eq_beforeFirst_append (key : D) :
    ∀ (log : List ((d : D) × R d)), (∃ entry ∈ log, entry.1 = key) →
      ∃ answer rest, log = beforeFirst key log ++ ⟨key, answer⟩ :: rest
  | [] => by simp
  | head :: tail => by
      intro found
      rw [beforeFirst_cons]
      by_cases here : head.1 = key
      · obtain ⟨first, answer⟩ := head
        simp only at here
        subst here
        exact ⟨answer, tail, by simp⟩
      · simp only [here, ↓reduceIte]
        have later : ∃ entry ∈ tail, entry.1 = key := by
          obtain ⟨entry, member, keyed⟩ := found
          rcases List.mem_cons.mp member with same | inTail
          · subst same
            exact absurd keyed here
          · exact ⟨entry, inTail, keyed⟩
        obtain ⟨answer, rest, split⟩ := eq_beforeFirst_append key tail later
        exact ⟨answer, rest, by rw [List.cons_append, ← split]⟩

/-- Answering `key` differently leaves everything before its first query unchanged. -/
theorem beforeFirst_update (key : D) (answer : R key) :
    ∀ (oa : OracleComp (ofFn R) α) (table : (d : D) → R d),
      beforeFirst key (tableQueryLog oa (Function.update table key answer)) =
        beforeFirst key (tableQueryLog oa table) := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure value => intro table; simp
  | query_bind queried next ih =>
      intro table
      rw [tableQueryLog_query_bind, tableQueryLog_query_bind, beforeFirst_cons, beforeFirst_cons]
      by_cases same : queried = key
      · simp only [same, ↓reduceIte]
      · simp only [same, ↓reduceIte]
        rw [Function.update_of_ne same]
        rw [ih (table queried) table]

end BeforeFirst

/-- Every entry of a table log carries the table's answer at its key. -/
theorem tableQueryLog_consistent (table : (d : D) → R d) :
    ∀ (oa : OracleComp (ofFn R) α) (entry : (d : D) × R d),
      entry ∈ tableQueryLog oa table → entry = ⟨entry.1, table entry.1⟩ := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure value => intro entry member; simp at member
  | query_bind queried next ih =>
      intro entry member
      rw [tableQueryLog_query_bind] at member
      rcases List.mem_cons.mp member with same | later
      · subst same
        rfl
      · exact ih (table queried) entry later

/-- Entries of a table log with the same key are equal. -/
theorem tableQueryLog_entry_eq (table : (d : D) → R d) (oa : OracleComp (ofFn R) α)
    {first second : (d : D) × R d} (firstMember : first ∈ tableQueryLog oa table)
    (secondMember : second ∈ tableQueryLog oa table) (sameKey : first.1 = second.1) :
    first = second := by
  rw [tableQueryLog_consistent table oa first firstMember,
    tableQueryLog_consistent table oa second secondMember]
  obtain ⟨key, _⟩ := first
  obtain ⟨other, _⟩ := second
  simp only at sameKey
  subst sameKey
  rfl

/-- Logging returns the table log next to the table run's result. -/
theorem evalWithAnswerFn_withQueryLog (table : (d : D) → R d) :
    ∀ oa : OracleComp (ofFn R) α,
      evalWithAnswerFn (QueryImpl.ofFn table) oa.withQueryLog =
        (evalWithAnswerFn (QueryImpl.ofFn table) oa, tableQueryLog oa table) := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind queried next ih =>
      rw [withQueryLog_bind, withQueryLog_query, bind_assoc, evalWithAnswerFn_bind,
        evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply, pure_bind, evalWithAnswerFn_map,
        ih (table queried), tableQueryLog_query_bind, evalWithAnswerFn_bind,
        evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply]
      rfl

/-- Logging makes no query of its own. -/
theorem tableQueryLog_withQueryLog (table : (d : D) → R d) :
    ∀ oa : OracleComp (ofFn R) α, tableQueryLog oa.withQueryLog table = tableQueryLog oa table := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind queried next ih =>
      rw [withQueryLog_bind, withQueryLog_query, bind_assoc, tableQueryLog_query_bind,
        pure_bind, tableQueryLog_map, ih (table queried), tableQueryLog_query_bind]
where
  tableQueryLog_map {γ δ : Type} (f : γ → δ) (computation : OracleComp (ofFn R) γ)
      (answers : (d : D) → R d) :
      tableQueryLog (f <$> computation) answers = tableQueryLog computation answers := by
    rw [map_eq_bind_pure_comp, tableQueryLog_bind]
    simp

/-- Forgetting the log recovers the computation. -/
theorem fst_map_withQueryLog {ι : Type} {spec : OracleSpec ι} :
    ∀ oa : OracleComp spec α, Prod.fst <$> oa.withQueryLog = oa := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind queried next ih =>
      rw [withQueryLog_bind, withQueryLog_query, bind_assoc, map_bind]
      refine bind_congr fun answer => ?_
      rw [pure_bind, Functor.map_map]
      exact ih answer

/-- Cost instrumentation commutes with mapping the result. -/
theorem costDist_map {ι ω : Type} {spec : OracleSpec ι} [AddCommMonoid ω] (f : α → β)
    (oa : OracleComp spec α) (cm : CostModel spec ω) :
    costDist (f <$> oa) cm = Prod.map f id <$> costDist oa cm := by
  simp only [costDist, instrumentedRun, simulateQ_map, WriterT.run_map']

/-- Mapping the result keeps every pathwise cost. -/
theorem worstCaseCostBound_map_iff {ι ω : Type} {spec : OracleSpec ι} [AddCommMonoid ω]
    [Preorder ω] (f : α → β) (oa : OracleComp spec α) (cm : CostModel spec ω) (bound : ω) :
    WorstCaseCostBound (f <$> oa) cm bound ↔ WorstCaseCostBound oa cm bound := by
  rw [worstCaseCostBound_iff_support_bound, worstCaseCostBound_iff_support_bound, costDist_map,
    support_map]
  constructor
  · intro mapped point member
    exact mapped _ ⟨point, member, rfl⟩
  · rintro original _ ⟨point, member, rfl⟩
    exact original point member

/-- Logging keeps every pathwise cost. -/
theorem worstCaseCostBound_withQueryLog {ι ω : Type} {spec : OracleSpec ι} [AddCommMonoid ω]
    [Preorder ω] (oa : OracleComp spec α) (cm : CostModel spec ω) (bound : ω) :
    WorstCaseCostBound oa.withQueryLog cm bound ↔ WorstCaseCostBound oa cm bound := by
  rw [← worstCaseCostBound_map_iff Prod.fst, fst_map_withQueryLog]

/-- A total query bound bounds the length of every table log. -/
theorem tableQueryLog_length_le (table : (d : D) → R d) :
    ∀ (oa : OracleComp (ofFn R) α) (bound : ℕ), IsTotalQueryBound oa bound →
      (tableQueryLog oa table).length ≤ bound := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure value => intro bound _; simp
  | query_bind queried next ih =>
      intro bound bounded
      rw [isTotalQueryBound_query_bind_iff] at bounded
      rw [tableQueryLog_query_bind, List.length_cons]
      have := ih (table queried) (bound - 1) (bounded.2 _)
      omega

end ZkcSecurity.Commitment
