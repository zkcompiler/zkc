module

public import ZkcSecurity.Bindings.Oracle.Permutation
public import ZkcSecurity.Transformations.Commitment.Charges
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

@[expose] public section

/-! The permutation read in the existing authenticated commitment experiment.
Authentication consumes the existing opening and may extend the shared hash
cache. It neither resets that cache nor issues a transcript challenge. -/

set_option autoImplicit false
namespace ZkcSecurity.Realizations.Oracle.Permutation

open OracleComp OracleSpec ZkcSecurity.Commitment ZkcSecurity.FiatShamir

variable {J : PIR.Signature} {E P Shape Value Query Y A : Type} {Raw : E → Type} {size : ℕ}

/-- Actual concrete execution, with an arbitrary continuation. The same
history, roots and remaining messages reach the suffix; one opening is consumed
on success. No premise about relation validity is needed. -/
theorem authenticated_read_bind (absorb : Typed.Interface J E P Raw)
    (scheme : Extractable Shape Value Query Y) (permutation : Equiv.Perm (Fin size))
    (handle : ℕ) (index : Fin size) (next : Value → PIR.Process (committed J Shape Value) A)
    (history : List (Absorbed E Shape Y)) (roots : List (Shape × Y))
    (messages : List (Message P Y)) (opening : Opening Value Y) (rest : List (Opening Value Y))
    (shape : Shape) (root : Y) (found : roots[handle]? = some (shape, root)) :
    run absorb scheme ((read permutation handle index).bind next) history roots messages
        (opening :: rest) = (do
      let accepted ← liftHash Raw Shape (scheme.authenticate shape root (permutation index).val opening)
      if accepted then run absorb scheme (next opening.value) history roots messages rest
      else pure (.stopped .reject)) := by
  simp only [read, PIR.Process.bind]
  rw [run.eq_def]
  simp only [found]
  apply bind_congr
  intro accepted
  cases accepted <;> rfl

/-- Concrete access returns only after the selected scheme authenticates it.
This equation exposes hash cost separately from the one positional read. -/
theorem authenticated_read (absorb : Typed.Interface J E P Raw)
    (scheme : Extractable Shape Value Query Y) (permutation : Equiv.Perm (Fin size))
    (handle : ℕ) (index : Fin size)
    (history : List (Absorbed E Shape Y)) (roots : List (Shape × Y))
    (messages : List (Message P Y)) (opening : Opening Value Y) (rest : List (Opening Value Y))
    (shape : Shape) (root : Y) (found : roots[handle]? = some (shape, root)) :
    run absorb scheme (read permutation handle index) history roots messages (opening :: rest) =
      (fun accepted => if accepted then PIR.Outcome.returned opening.value else .stopped .reject) <$>
        liftHash Raw Shape (scheme.authenticate shape root (permutation index).val opening) := by
  unfold read
  rw [run.eq_def]
  simp only [found]
  rw [map_eq_bind_pure_comp]
  apply bind_congr
  intro accepted
  cases accepted <;> rfl

/-- Positional-read count and cryptographic query count are different resources:
the latter inherits the selected authenticator's independently proved bound. -/
theorem authenticated_query_bound (absorb : Typed.Interface J E P Raw)
    (scheme : Extractable Shape Value Query Y) (permutation : Equiv.Perm (Fin size))
    (handle : ℕ) (index : Fin size) (history : List (Absorbed E Shape Y))
    (roots : List (Shape × Y)) (messages : List (Message P Y))
    (opening : Opening Value Y) (rest : List (Opening Value Y)) (shape : Shape) (root : Y)
    (found : roots[handle]? = some (shape, root)) (budget : ℕ)
    (bounded : IsTotalQueryBound
      (scheme.authenticate shape root (permutation index).val opening) budget) :
    IsTotalQueryBound (run absorb scheme (read permutation handle index)
      history roots messages (opening :: rest)) budget := by
  rw [authenticated_read absorb scheme permutation handle index history roots messages opening rest
    shape root found]
  exact (isQueryBound_map_iff _ _ _ _ _).mpr (liftHash_queryBound _ budget bounded)

/-- Authentication queries the hash namespace only. This is a syntactic query
restriction over every typed reply, stronger than leaving cached values equal. -/
theorem liftHash_only_hash_queries {Result : Type}
    (computation : OracleComp (Query →ₒ Y) Result) :
    (liftHash Raw Shape computation).AllQueriesSatisfy (fun key => ∃ query, key = .inr query) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      simp only [liftHash, simulateQ_pure]
      exact allQueriesSatisfy_pure _ _
  | query_bind query next ih =>
      simp only [liftHash, simulateQ_bind, simulateQ_spec_query, hashCall] at ih ⊢
      exact (allQueriesSatisfy_query_bind_iff (spec := joint Raw Shape Y Query)
        (.inr query) _ _).mpr ⟨⟨query, rfl⟩, fun answer => ih answer⟩

theorem authenticated_no_transcript_queries (absorb : Typed.Interface J E P Raw)
    (scheme : Extractable Shape Value Query Y) (permutation : Equiv.Perm (Fin size))
    (handle : ℕ) (index : Fin size) (history : List (Absorbed E Shape Y))
    (roots : List (Shape × Y)) (messages : List (Message P Y))
    (opening : Opening Value Y) (rest : List (Opening Value Y)) (shape : Shape) (root : Y)
    (found : roots[handle]? = some (shape, root)) :
    AllQueriesSatisfy
      (run absorb scheme (read permutation handle index) history roots messages (opening :: rest))
      (fun key => ∃ query, key = .inr query) := by
  rw [authenticated_read absorb scheme permutation handle index history roots messages opening rest
    shape root found]
  rw [allQueriesSatisfy_def, isQueryBound_map_iff, ← allQueriesSatisfy_def]
  exact liftHash_only_hash_queries _

section Cache
variable [DecidableEq E] [DecidableEq Shape] [DecidableEq Y] [DecidableEq Query]
  [∀ event, SampleableType (Raw event)] [SampleableType Y]

/-- A lifted hash computation preserves every transcript cache cell exactly,
including absent cells. The separate query restriction excludes cached queries. -/
theorem liftHash_transcript_frame {Result : Type} (computation : OracleComp (Query →ₒ Y) Result)
    (cache : (joint Raw Shape Y Query).QueryCache)
    (result : Result × (joint Raw Shape Y Query).QueryCache)
    (supported : result ∈ support ((simulateQ (joint Raw Shape Y Query).randomOracle
      (liftHash Raw Shape computation)).run cache)) :
    ∀ key, result.2 (.inl key) = cache (.inl key) := by
  induction computation using OracleComp.inductionOn generalizing cache result with
  | pure value =>
      simp only [liftHash, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at supported
      subst result
      exact fun _ => rfl
  | query_bind query next ih =>
      simp only [liftHash, simulateQ_bind, simulateQ_spec_query,
        StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨answer, intermediate⟩, first, later⟩ := supported
      have queryEq : simulateQ (joint Raw Shape Y Query).randomOracle
          (hashCall Raw Shape query) = (joint Raw Shape Y Query).randomOracle (.inr query) :=
        simulateQ_spec_query _ _
      rw [queryEq] at first
      have step : intermediate = cache.cacheQuery (.inr query) answer :=
        QueryImpl.withCaching_run_eq_cacheQuery uniformSampleImpl first
      intro key
      rw [ih answer intermediate result later key, step]
      exact QueryCache.cacheQuery_of_ne _ _ (by simp)

/-- Actual authenticated access only grows the joint cache, retaining all
previous answers. Hash authentication is allowed to add hash entries. -/
theorem authenticated_cache_extends (absorb : Typed.Interface J E P Raw)
    (scheme : Extractable Shape Value Query Y) (permutation : Equiv.Perm (Fin size))
    (handle : ℕ) (index : Fin size) (history : List (Absorbed E Shape Y))
    (roots : List (Shape × Y)) (messages : List (Message P Y)) (openings : List (Opening Value Y))
    (cache : (joint Raw Shape Y Query).QueryCache)
    (result : PIR.Outcome Value × (joint Raw Shape Y Query).QueryCache)
    (supported : result ∈ support ((simulateQ (joint Raw Shape Y Query).randomOracle
      (run absorb scheme (read permutation handle index) history roots messages openings)).run cache)) :
    cache ≤ result.2 :=
  OracleComp.simulateQ_run_preservesInv (joint Raw Shape Y Query).randomOracle (cache ≤ ·)
    (QueryImpl.PreservesInv.withCaching_le uniformSampleImpl cache)
    (run absorb scheme (read permutation handle index) history roots messages openings)
    cache le_rfl result supported

/-- Successful or rejected authentication leaves all transcript cells unchanged
in the actual shared-cache run. -/
theorem authenticated_transcript_frame (absorb : Typed.Interface J E P Raw)
    (scheme : Extractable Shape Value Query Y) (permutation : Equiv.Perm (Fin size))
    (handle : ℕ) (index : Fin size) (history : List (Absorbed E Shape Y))
    (roots : List (Shape × Y)) (messages : List (Message P Y))
    (opening : Opening Value Y) (rest : List (Opening Value Y)) (shape : Shape) (root : Y)
    (found : roots[handle]? = some (shape, root))
    (cache : (joint Raw Shape Y Query).QueryCache)
    (result : PIR.Outcome Value × (joint Raw Shape Y Query).QueryCache)
    (supported : result ∈ support ((simulateQ (joint Raw Shape Y Query).randomOracle
      (run absorb scheme (read permutation handle index) history roots messages (opening :: rest))).run cache)) :
    ∀ key, result.2 (.inl key) = cache (.inl key) := by
  rw [authenticated_read absorb scheme permutation handle index history roots messages opening rest
    shape root found, simulateQ_map, StateT.run_map, support_map] at supported
  obtain ⟨original, supported, rfl⟩ := supported
  exact liftHash_transcript_frame _ cache original supported

end Cache
end ZkcSecurity.Realizations.Oracle.Permutation
