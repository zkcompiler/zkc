module

public import VCVio.ProgramLogic.Relational.SimulateQ.Basic
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import VCVio.OracleComp.QueryTracking.LoggingOracle
public import ZkcSecurity.VCVio.Deferral

@[expose] public section

/-! # Answering repeated queries from a record

A memoizing front end (`memoImpl`) answers a query from its record when the record holds the key's
answer, and otherwise asks the oracle and records the answer. Against the lazily sampled random
oracle it is transparent (`coupling`): run from a record that equals the oracle's cache, a
computation and its memoized version return the same result and leave the same cache, the front
end's record equals that cache, and the memoized version's query log is the direct log restricted
to keys not seen before, in order (`unseen`). The direct log agrees with the final cache, so a
repeated key carries the answer of its first occurrence.
-/

set_option autoImplicit false
set_option linter.deprecated false

namespace ZkcSecurity.VCVio.Memo
open OracleComp OracleSpec OracleComp.ProgramLogic.Relational

variable {D α : Type} [DecidableEq D] {R : D → Type}

/-- Answer a query from the record when it holds the key's answer; otherwise ask the oracle and
record the answer. -/
def memoImpl : QueryImpl (OracleSpec.ofFn R)
    (StateT (OracleSpec.ofFn R).QueryCache (OracleComp (OracleSpec.ofFn R))) :=
  fun query => StateT.mk fun record =>
    match record query with
    | some answer => pure (answer, record)
    | none => (fun answer => (answer, record.cacheQuery query answer)) <$>
        liftM ((OracleSpec.ofFn R).query query)

/-- The entries of a log whose keys a record has not seen, the first occurrence of each key. -/
def unseen : (OracleSpec.ofFn R).QueryCache → QueryLog (OracleSpec.ofFn R) →
    QueryLog (OracleSpec.ofFn R)
  | _, [] => []
  | record, entry :: rest =>
      if (record entry.1).isSome then unseen record rest
      else entry :: unseen (record.cacheQuery entry.1 entry.2) rest

/-- How a direct run and a memoized run from the record `record` correspond: equal results and
final caches, the front end's record equal to that cache, the memoized log the direct log's unseen
entries, the direct log agreeing with the final cache, and the final cache extending the record. -/
def Coupled (record : (OracleSpec.ofFn R).QueryCache)
    (direct : (α × QueryLog (OracleSpec.ofFn R)) × (OracleSpec.ofFn R).QueryCache)
    (memo : ((α × (OracleSpec.ofFn R).QueryCache) × QueryLog (OracleSpec.ofFn R)) ×
      (OracleSpec.ofFn R).QueryCache) : Prop :=
  memo.1.1.1 = direct.1.1 ∧ memo.1.1.2 = direct.2 ∧ memo.2 = direct.2 ∧
    memo.1.2 = unseen record direct.1.2 ∧
    (∀ entry ∈ direct.1.2, direct.2 entry.1 = some entry.2) ∧
    ∀ key answer, record key = some answer → direct.2 key = some answer

omit [DecidableEq D] in
/-- A query of the direct run: the oracle's answer at the key, logged before the continuation's
log. -/
theorem run_withQueryLog_query_bind {σ : Type}
    (implementation : QueryImpl (OracleSpec.ofFn R) (StateT σ ProbComp)) (key : D)
    (next : R key → OracleComp (OracleSpec.ofFn R) α) (state : σ) :
    (simulateQ implementation (liftM ((OracleSpec.ofFn R).query key) >>= next).withQueryLog).run
        state =
      (implementation key).run state >>= fun step =>
        (fun result => ((result.1.1, (⟨key, step.1⟩ : (t : D) × R t) :: result.1.2), result.2)) <$>
          (simulateQ implementation (next step.1).withQueryLog).run step.2 := by
  rw [withQueryLog_bind, withQueryLog_query]
  simp only [bind_assoc, pure_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    simulateQ_map, StateT.run_map, Prod.map]
  rfl

/-- A memoized query of a key the record holds is answered from the record. -/
theorem memo_query_bind_some (key : D) (next : R key → OracleComp (OracleSpec.ofFn R) α)
    (record : (OracleSpec.ofFn R).QueryCache) {answer : R key} (hit : record key = some answer) :
    (simulateQ memoImpl (liftM ((OracleSpec.ofFn R).query key) >>= next)).run record =
      (simulateQ memoImpl (next answer)).run record := by
  simp [simulateQ_bind, StateT.run_bind, memoImpl, StateT.run_mk, hit]

/-- A memoized query of a key the record lacks asks the oracle and records the answer. -/
theorem memo_query_bind_none (key : D) (next : R key → OracleComp (OracleSpec.ofFn R) α)
    (record : (OracleSpec.ofFn R).QueryCache) (miss : record key = none) :
    (simulateQ memoImpl (liftM ((OracleSpec.ofFn R).query key) >>= next)).run record =
      liftM ((OracleSpec.ofFn R).query key) >>= fun answer =>
        (simulateQ memoImpl (next answer)).run (record.cacheQuery key answer) := by
  simp [simulateQ_bind, StateT.run_bind, memoImpl, StateT.run_mk, miss]

variable [∀ key, SampleableType (R key)]

theorem coupling (adversary : OracleComp (OracleSpec.ofFn R) α) :
    ∀ record : (OracleSpec.ofFn R).QueryCache,
      RelTriple ((simulateQ randomOracle adversary.withQueryLog).run record)
        ((simulateQ randomOracle ((simulateQ memoImpl adversary).run record).withQueryLog).run record)
        (Coupled record) := by
  induction adversary using OracleComp.inductionOn with
  | pure value =>
      intro record
      simp only [withQueryLog_pure, simulateQ_pure, StateT.run_pure]
      exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, by simp, fun _ _ found => found⟩
  | query_bind key next ih =>
      intro record
      rw [run_withQueryLog_query_bind]
      cases hit : record key with
      | some answer =>
          rw [memo_query_bind_some key next record hit, randomOracle.run_eq, hit, pure_bind]
          rw [show ((simulateQ randomOracle
              ((simulateQ memoImpl (next answer)).run record).withQueryLog).run record) =
            id <$> ((simulateQ randomOracle
              ((simulateQ memoImpl (next answer)).run record).withQueryLog).run record) from
                (id_map _).symm]
          refine relTriple_map (relTriple_post_mono (ih answer record) ?_)
          rintro direct memo ⟨result, state, cache, log, agree, grows⟩
          refine ⟨result, state, cache, ?_, ?_, grows⟩
          · simp only [id, log, unseen, hit, Option.isSome_some, ↓reduceIte]
          · intro entry member
            rcases List.mem_cons.mp member with rfl | inner
            · exact grows key answer hit
            · exact agree entry inner
      | none =>
          rw [memo_query_bind_none key next record hit, run_withQueryLog_query_bind]
          refine relTriple_bind (R := fun first second => first = second ∧
            first.2 = record.cacheQuery key first.1) ?_ ?_
          · refine relTriple_refl_of_mem_support _ fun step member => ⟨rfl, ?_⟩
            rw [randomOracle.run_eq, hit] at member
            simp only [mem_support_bind_iff, mem_support_pure_iff] at member
            obtain ⟨answer, _, rfl⟩ := member
            rfl
          · rintro step _ ⟨rfl, cached⟩
            rw [cached]
            refine relTriple_map (relTriple_post_mono (ih step.1 _) ?_)
            rintro direct memo ⟨result, state, cache, log, agree, grows⟩
            refine ⟨result, state, cache, ?_, ?_, ?_⟩
            · simp only [log, unseen, hit, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
            · intro entry member
              rcases List.mem_cons.mp member with rfl | inner
              · exact grows _ _ (QueryCache.cacheQuery_self _ _ _)
              · exact agree entry inner
            · intro other answer found
              refine grows other answer ?_
              have different : other ≠ key := by
                rintro rfl
                rw [hit] at found
                cases found
              rw [QueryCache.cacheQuery_of_ne _ _ different]
              exact found

omit [DecidableEq D] [∀ key, SampleableType (R key)] in
/-- Logging a mapped computation logs the computation and maps its result. -/
theorem withQueryLog_map {β : Type} (map : α → β) (computation : OracleComp (OracleSpec.ofFn R) α) :
    (map <$> computation).withQueryLog = Prod.map map id <$> computation.withQueryLog := by
  rw [map_eq_bind_pure_comp, withQueryLog_bind]
  conv_rhs => rw [map_eq_bind_pure_comp]
  congr 1
  funext run
  simp [withQueryLog_pure, Prod.map]

/-- An experiment that logs a prover and then runs a continuation that reads the prover's result
and places its log in the outcome: run with the memoized prover, it has the same outcomes up to
replacing the prover's log by its unseen entries, and the direct log agrees with a cache, so a
repeated key carries the answer of its first occurrence. -/
theorem experiment_coupling {β γ : Type} (adversary : OracleComp (OracleSpec.ofFn R) α)
    (continuation : α → OracleComp (OracleSpec.ofFn R) β)
    (assemble : α → QueryLog (OracleSpec.ofFn R) → β → γ) :
    RelTriple
      ((simulateQ randomOracle (adversary.withQueryLog >>= fun run =>
        assemble run.1 run.2 <$> continuation run.1)).run' ∅)
      ((simulateQ randomOracle
        ((Prod.fst <$> (simulateQ memoImpl adversary).run ∅).withQueryLog >>= fun run =>
          assemble run.1 run.2 <$> continuation run.1)).run' ∅)
      (fun direct memo => ∃ claim log rest, ∃ cache : (OracleSpec.ofFn R).QueryCache,
        direct = assemble claim log rest ∧ memo = assemble claim (unseen ∅ log) rest ∧
          ∀ entry ∈ log, cache entry.1 = some entry.2) := by
  rw [withQueryLog_map]
  simp only [simulateQ_bind, simulateQ_map, StateT.run'_eq, StateT.run_bind, StateT.run_map,
    map_bind, bind_map_left]
  refine relTriple_bind (coupling adversary ∅) fun direct memo coupled => ?_
  obtain ⟨result, state, cache, log, agree, _⟩ := coupled
  simp only [Prod.map, id, result, cache, log]
  refine relTriple_map (relTriple_map (relTriple_post_mono (relTriple_refl _) ?_))
  rintro first second rfl
  exact ⟨direct.1.1, direct.1.2, first.1, direct.2, rfl, rfl, agree⟩

omit [∀ key, SampleableType (R key)] in
/-- For a predicate false at every recorded answer, the first match after dropping the entries of
keys already seen is the first match of the whole log, when the log agrees with a cache that
extends the record. -/
theorem find?_unseen_append (match? : ((key : D) × R key) → Bool)
    (cache : (OracleSpec.ofFn R).QueryCache) (rest : QueryLog (OracleSpec.ofFn R)) :
    ∀ (log : QueryLog (OracleSpec.ofFn R)) (record : (OracleSpec.ofFn R).QueryCache),
      (∀ key answer, record key = some answer → match? ⟨key, answer⟩ = false) →
      (∀ key answer, record key = some answer → cache key = some answer) →
      (∀ entry ∈ log, cache entry.1 = some entry.2) →
      (unseen record log ++ rest).find? match? = (log ++ rest).find? match?
  | [], _, _, _, _ => rfl
  | entry :: tail, record, unmatched, grows, agree => by
      have tailAgree : ∀ entry ∈ tail, cache entry.1 = some entry.2 :=
        fun other member => agree other (List.mem_cons_of_mem _ member)
      unfold unseen
      by_cases seen : (record entry.1).isSome
      · obtain ⟨answer, recorded⟩ := Option.isSome_iff_exists.mp seen
        have same : answer = entry.2 := Option.some.inj
          ((grows entry.1 answer recorded).symm.trans (agree entry (List.mem_cons_self ..)))
        have skipped : match? entry = false := by
          have := unmatched entry.1 answer recorded
          rwa [same] at this
        rw [if_pos seen, List.cons_append, List.find?_cons, skipped]
        exact find?_unseen_append match? cache rest tail record unmatched grows tailAgree
      · rw [if_neg seen, List.cons_append, List.cons_append, List.find?_cons, List.find?_cons]
        cases matched : match? entry with
        | true => rfl
        | false =>
            refine find?_unseen_append match? cache rest tail _ (fun key answer found => ?_)
              (fun key answer found => ?_) tailAgree
            · by_cases here : key = entry.1
              · subst here
                rw [QueryCache.cacheQuery_self] at found
                cases found
                exact matched
              · rw [QueryCache.cacheQuery_of_ne _ _ here] at found
                exact unmatched key answer found
            · by_cases here : key = entry.1
              · subst here
                rw [QueryCache.cacheQuery_self] at found
                cases found
                exact agree entry (List.mem_cons_self ..)
              · rw [QueryCache.cacheQuery_of_ne _ _ here] at found
                exact grows key answer found

end ZkcSecurity.VCVio.Memo
