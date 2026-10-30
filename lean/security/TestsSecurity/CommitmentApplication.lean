import ZkcSecurity.Commitment.AdaptiveOpening

/-! Focused theorem controls for the application-event interpretation and adaptive client.
The small digest below is a deterministic execution fixture, not a secure parameter choice. -/

set_option autoImplicit false

namespace TestsSecurity.CommitmentApplication

open OracleComp OracleSpec ZkcSecurity.FiatShamir ZkcSecurity.Commitment
open ZkcSecurity.Commitment.AdaptiveOpening
open ZkcSecurity.Examples.CommittedOpeningBridge (Event absorb words initial scheme)

abbrev HashQuery := Bool ⊕ (Bool × Bool)

def model : LeafHashing Bool HashQuery Bool where
  leaf := Sum.inl
  node left right := .inr (left, right)
  leafRow
    | .inl row => some row
    | .inr _ => none
  children
    | .inl _ => none
    | .inr pair => some pair
  leafRow_leaf _ := rfl
  children_node _ _ := rfl

def next (row : Bool) : Fin (2 ^ 1) := if row then 1 else 0

/-- The second position is genuinely selected by the first reply. -/
theorem reply_changes_next_position : next false ≠ next true := by decide

theorem two_read_process :
    walk 1 next id 1 0 = .call (.read 0 0) fun first =>
      .call (.read 0 (next first).val) fun second => .done second := rfl

/-- A fixed table can give different results at different starts after two adaptive reads. -/
def alternating (index : Fin (2 ^ 1)) : Bool := index.val == 0

theorem adaptive_path_results :
    pathResult 1 next id alternating 1 0 = false ∧
      pathResult 1 next id alternating 1 1 = true := by decide

theorem ideal_walk_agrees :
    withTables (words 1 false) [(words 1 false).toTable () alternating]
        (walk 1 next id 1 0) = .done false :=
  withTables_walk 1 next id false alternating 1 0

abbrev Joint := joint (fun _ : Event Bool => Fin (2 ^ 1)) Unit Bool HashQuery

/-- Hash answers chosen only to exercise the actual authentication and run computations. -/
def answers : JointTable (fun _ : Event Bool => Fin (2 ^ 1)) Unit Bool HashQuery
  | .inl _ => (0 : Fin (2 ^ 1))
  | .inr (.inl row) => row
  | .inr (.inr _) => true

def twoOpenings : Proof (List Bool) Bool Bool :=
  ⟨[], [⟨true, [false]⟩, ⟨false, [true]⟩]⟩

theorem actual_two_read_run :
    evalWithAnswerFn (QueryImpl.ofFn answers)
      (run (absorb 1) (scheme model 1) (verifier 1 1 next id) (initial true) [((), true)]
        twoOpenings.messages twoOpenings.openings) = .returned false := by
  simp [verifier, walk, run.eq_def, absorb, twoOpenings, liftHash, hashCall,
    scheme, Extractable.comap, LeafHashing.scheme, LeafHashing.authenticate,
    LeafHashing.climb, LeafHashing.parent, model, answers, next]
  rfl

theorem missing_second_opening_refuses :
    evalWithAnswerFn (QueryImpl.ofFn answers)
      (run (absorb 1) (scheme model 1) (verifier 1 1 next id) (initial true) [((), true)]
        [] [⟨true, [false]⟩]) = .stopped .refused := by
  simp [verifier, walk, run.eq_def, absorb, liftHash, hashCall,
    scheme, Extractable.comap, LeafHashing.scheme, LeafHashing.authenticate,
    LeafHashing.climb, LeafHashing.parent, model, answers, next]
  rfl

theorem malformed_path_rejects :
    evalWithAnswerFn (QueryImpl.ofFn answers)
      (run (absorb 1) (scheme model 1) (verifier 1 1 next id) (initial true) [((), true)]
        [] [⟨true, []⟩, ⟨true, [true]⟩]) = .stopped .reject := by
  simp [verifier, walk, run.eq_def, absorb, liftHash, hashCall,
    scheme, Extractable.comap, LeafHashing.scheme, LeafHashing.authenticate]

theorem two_read_query_bound (root : Bool) (proof : Proof (List Bool) Bool Bool) :
    IsTotalQueryBound (run (absorb 1) (scheme model 1) (verifier 1 1 next id)
      (initial root) [((), root)] proof.messages proof.openings) 5 :=
  verifier_queryBound model 1 1 next id root proof

/-- These are tables of this actual client, not an abstract Bool quantifier counterexample. -/
theorem existential_bad_table_is_insufficient :
    (∃ rows : Fin (2 ^ 1) → Bool, FarPaths 1 1 next id 1 rows) ∧
      ¬ FarPaths 1 1 next id 1 (fun _ => true) := by
  constructor
  · exact ⟨fun _ => false, by simp [FarPaths, pathResult]⟩
  · norm_num [FarPaths, pathResult]

abbrev Result := JointRun Bool (List Bool) Bool Bool Bool (QueryLog Joint)

/-- The fixed completion policy is visible even when no row has been extracted. -/
theorem empty_extraction_uses_default (default root : Bool) :
    pinnedRows model 1 default [] root = fun _ => default := by
  funext index
  simp [pinnedRows, words, scheme, Extractable.comap, LeafHashing.scheme, LeafHashing.extract,
    LeafHashing.extractLabel, LeafHashing.findChildren, beforeFirst, hashEntries]

def queryFreeAccepted : Result := ⟨true, ⟨[], []⟩, .returned true, [], []⟩

/-- Acceptance and a bad requested table cannot make an absent query appear. This synthetic
result satisfies the application error but is outside the real client's execution support. -/
theorem query_free_accepted_is_not_covered :
    ApplicationError model 1 1 next id 1 false queryFreeAccepted ∧
      ¬ FalseAcceptance (words 1 false) (scheme model 1) (fun root => [((), root)])
        (FalseTable 1 1 next id 1 false) (· = true) queryFreeAccepted := by
  constructor
  · change true = true ∧ FarPaths 1 1 next id 1 (pinnedRows model 1 false [] true)
    rw [empty_extraction_uses_default]
    exact ⟨rfl, by simp [FarPaths, pathResult]⟩
  · exact Application.no_query_excludes_falseAcceptance _ _ _ _ _ queryFreeAccepted rfl

theorem real_client_excludes_query_free_result
    (prover : OracleComp Joint (Bool × Proof (List Bool) Bool Bool)) :
    queryFreeAccepted ∉ support (experiment (absorb 1) (scheme model 1)
      (fun _ => verifier 1 1 next id) initial (fun root => [((), root)]) prover) := by
  intro member
  obtain ⟨entry, present, _⟩ := experiment_queries_start model 1 1 next id prover
    queryFreeAccepted member
  exact List.not_mem_nil present

/-- A prover's early query freezes the requested table before the verifier reaches it. -/
theorem early_prover_query_freezes (root : Bool) (later : QueryLog Joint) :
    pinnedRows model 1 false ([⟨.inl (startKey 1 root), (0 : Fin (2 ^ 1))⟩] ++ later) root =
      pinnedRows model 1 false [⟨.inl (startKey 1 root), (0 : Fin (2 ^ 1))⟩] root :=
  pinnedRows_append model 1 false _ later root ⟨_, List.mem_cons_self, rfl⟩

/-- The event respects deduplication only under cache agreement, at the same pinned table. -/
theorem cache_consistent_repeats (result : Result) (cache : Joint.QueryCache)
    (agree : ∀ entry ∈ result.proverLog, cache entry.1 = some entry.2) :
    ApplicationError model 1 1 next id 1 false
        {result with proverLog := ZkcSecurity.VCVio.Memo.unseen ∅ result.proverLog} ↔
      ApplicationError model 1 1 next id 1 false result :=
  applicationError_unseen model 1 1 next id 1 false result cache agree

#print axioms Application.first_query_logged
#print axioms certificate
#print axioms checkpointTables_eq_pinned
#print axioms experiment_queries_start
#print axioms applicationError_implies_checkpoint
#print axioms applicationError_unseen
#print axioms ZkcSecurity.Commitment.AdaptiveOpening.soundness
#print axioms query_free_accepted_is_not_covered
#print axioms existential_bad_table_is_insufficient
#print axioms actual_two_read_run

end TestsSecurity.CommitmentApplication
