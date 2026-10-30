module

public import ZkcSecurity.Commitment.Application
public import ZkcSecurity.Commitment.Opening
public import ZkcSecurity.Commitment.Cost
public import ZkcSecurity.Commitment.Repeats

@[expose] public section

/-! # Authenticated adaptive pointer walks

The client draws one starting position and authenticates a nonempty sequence of rows of the same
committed table. Every later position is computed from the preceding authenticated reply. The
application error is acceptance when a specified fraction of starting positions reject on the
table pinned at the first challenge's checkpoint. Missing extracted rows are completed with the
fixed default, exactly as in the existing committed-opening bridge. The security theorem applies
that bridge's joint hash/transcript bound once; it introduces no independent Fiat–Shamir loss.
-/

set_option autoImplicit false

namespace ZkcSecurity.Commitment.AdaptiveOpening

open OracleComp OracleSpec ZkcSecurity.FiatShamir
open ZkcSecurity.Examples.CommittedOpeningBridge
  (Op signature Event absorb words initial initial_determined error scheme carries)

variable {Row Query Digest : Type}

/-- A pointer walk of `additional + 1` reads. Even the last read is authenticated. -/
def walk (depth : ℕ) (next : Row → Fin (2 ^ depth)) (accepts : Row → Bool) :
    ℕ → Fin (2 ^ depth) → PIR.Process (committed (signature Row depth) Unit Row) Bool
  | 0, index => .call (.read 0 index.val) fun row => .done (accepts row)
  | additional + 1, index => .call (.read 0 index.val) fun row =>
      walk depth next accepts additional (next row)

/-- The mathematical pointer-walk result on one fixed total table. -/
def pathResult (depth : ℕ) (next : Row → Fin (2 ^ depth)) (accepts : Row → Bool)
    (rows : Fin (2 ^ depth) → Row) : ℕ → Fin (2 ^ depth) → Bool
  | 0, index => accepts (rows index)
  | additional + 1, index => pathResult depth next accepts rows additional (next (rows index))

/-- A challenge is required syntactically, before any read, on every execution path. -/
def verifier (depth additional : ℕ) (next : Row → Fin (2 ^ depth)) (accepts : Row → Bool) :
    PIR.Process (committed (signature Row depth) Unit Row) Bool :=
  .call (.base .index) fun index => walk depth next accepts additional index

/-- At least `fraction` of starting positions reject after the specified number of reads. This
is a property of the pinned table, not an existential choice of a different bad table. -/
def FarPaths (depth additional : ℕ) (next : Row → Fin (2 ^ depth)) (accepts : Row → Bool)
    (fraction : ENNReal) (rows : Fin (2 ^ depth) → Row) : Prop :=
  fraction * 2 ^ depth ≤ ((Finset.univ.filter fun index =>
    pathResult depth next accepts rows additional index = false).card : ENNReal)

/-- The relation used by the ideal certificate, on the bridge's normalized table carrier. -/
def FalseTable (depth additional : ℕ) (next : Row → Fin (2 ^ depth)) (accepts : Row → Bool)
    (fraction : ENNReal) (default : Row) (_root : Digest) (tables : List (Table Row)) : Prop :=
  ∃ rows, tables = [(words depth default).toTable () rows] ∧
    FarPaths depth additional next accepts fraction rows

theorem withTables_walk (depth : ℕ) (next : Row → Fin (2 ^ depth)) (accepts : Row → Bool)
    (default : Row) (rows : Fin (2 ^ depth) → Row) (additional : ℕ)
    (index : Fin (2 ^ depth)) :
    withTables (words depth default) [(words depth default).toTable () rows]
        (walk depth next accepts additional index) =
      .done (pathResult depth next accepts rows additional index) := by
  induction additional generalizing index with
  | zero =>
      rw [walk, withTables]
      have found : lookup [(words depth default).toTable () rows] 0 index.val =
          some (rows index) := by simp [lookup, words, index.isLt]
      rw [found]
      rfl
  | succ additional ih =>
      rw [walk, withTables]
      have found : lookup [(words depth default).toTable () rows] 0 index.val =
          some (rows index) := by simp [lookup, words, index.isLt]
      rw [found]
      exact ih (next (rows index))

theorem withTables_verifier (depth additional : ℕ) (next : Row → Fin (2 ^ depth))
    (accepts : Row → Bool) (default : Row) (rows : Fin (2 ^ depth) → Row) :
    withTables (words depth default) [(words depth default).toTable () rows]
        (verifier depth additional next accepts) =
      .call Op.index fun index => .done (pathResult depth next accepts rows additional index) := by
  simp only [verifier, withTables]
  congr 1
  funext index
  exact withTables_walk depth next accepts default rows additional index

/-- Only the initial draw can escape this ideal certificate: all adaptive reads have already
been evaluated on the same fixed table by `withTables_walk`. -/
def Doomed (depth additional : ℕ) (next : Row → Fin (2 ^ depth)) (accepts : Row → Bool)
    (fraction : ENNReal) (default : Row) (process : PIR.Process (signature Row depth) Bool) : Prop :=
  process = .done false ∨ (∃ stop, process = .halt stop) ∨
    ∃ rows, FarPaths depth additional next accepts fraction rows ∧
      process = withTables (words depth default) [(words depth default).toTable () rows]
        (verifier depth additional next accepts)

theorem accepted_fraction_le (depth additional : ℕ) (next : Row → Fin (2 ^ depth))
    (accepts : Row → Bool) (fraction : ENNReal) (rows : Fin (2 ^ depth) → Row)
    (far : FarPaths depth additional next accepts fraction rows) :
    ((Finset.univ.filter fun index =>
      pathResult depth next accepts rows additional index = true).card : ENNReal) /
        (2 ^ depth : ℕ) ≤ 1 - fraction :=
  ZkcSecurity.Examples.CommittedOpeningBridge.accepted_fraction_le
    (fun index => pathResult depth next accepts rows additional index) depth fraction id far

/-- A proved ideal certificate for arbitrarily many adaptive reads, with one challenge charge. -/
def certificate (depth additional : ℕ) (next : Row → Fin (2 ^ depth)) (accepts : Row → Bool)
    (fraction : ENNReal) (default : Row) :
    Typed.Certificate (absorb (Row := Row) depth) (· = true) (error fraction) where
  doomed := Doomed depth additional next accepts fraction default
  step process doomed := by
    rcases doomed with rfl | ⟨stop, rfl⟩ | ⟨rows, far, rfl⟩
    · show ¬ (false = true)
      simp
    · trivial
    · rw [withTables_verifier]
      change Pr{let raw ← $ᵗ (Fin (2 ^ depth))}[∃ value, some raw = some value ∧
        ¬ Doomed depth additional next accepts fraction default
          (.done (pathResult depth next accepts rows additional value))] ≤ 1 - fraction
      refine (prEvent_mono _ _ (fun raw =>
        pathResult depth next accepts rows additional raw = true) fun raw escaping => ?_).trans ?_
      · obtain ⟨value, same, outside⟩ := escaping
        cases Option.some.inj same
        by_contra rejected
        exact outside (Or.inl (by simpa using rejected))
      · rw [SampleableType.prEvent_uniformSample, Fintype.card_fin]
        exact_mod_cast accepted_fraction_le depth additional next accepts fraction rows far

theorem walk_commitBound (depth : ℕ) (next : Row → Fin (2 ^ depth)) (accepts : Row → Bool)
    (additional : ℕ) (index : Fin (2 ^ depth)) :
    CommitBound (walk depth next accepts additional index) 0 := by
  induction additional generalizing index with
  | zero => intro row; trivial
  | succ additional ih => exact fun row => ih (next row)

theorem verifier_commitBound (depth additional : ℕ) (next : Row → Fin (2 ^ depth))
    (accepts : Row → Bool) : CommitBound (verifier depth additional next accepts) 0 :=
  fun index => walk_commitBound depth next accepts additional index

/-- Read charges are shared by the natural-number query bound and the ENNReal security cost.
All replies, including repeats and cycles, are covered by the structural induction. -/
theorem walk_charged {Cost : Type} [AddCommMonoid Cost] [Preorder Cost]
    (depth : ℕ) (next : Row → Fin (2 ^ depth)) (accepts : Row → Bool)
    (charge : Event Row → Cost) (readCharge : Cost) (additional : ℕ) (index : Fin (2 ^ depth)) :
    Charged (absorb depth) (fun _ : Unit => True) charge readCharge
      (walk depth next accepts additional index) ((additional + 1) • readCharge) := by
  induction additional generalizing index with
  | zero => exact ⟨0, by simp, fun _ => trivial⟩
  | succ additional ih =>
      exact ⟨(additional + 1) • readCharge, by simp [succ_nsmul'], fun row => ih (next row)⟩

theorem verifier_charged {Cost : Type} [AddCommMonoid Cost] [Preorder Cost]
    (depth additional : ℕ) (next : Row → Fin (2 ^ depth)) (accepts : Row → Bool)
    (charge : Event Row → Cost) (readCharge : Cost) :
    Charged (absorb depth) (fun _ : Unit => True) charge readCharge
      (verifier depth additional next accepts) (charge .index + (additional + 1) • readCharge) :=
  ⟨_, le_rfl, fun index => walk_charged depth next accepts charge readCharge additional index⟩

/-- The exact challenge key of this application. Reads add no transcript events. -/
def startKey (_depth : ℕ) (root : Digest) : TranscriptKey (Event Row) Unit Digest :=
  (initial root, .index)

section Extraction
variable [DecidableEq Row] [DecidableEq Query] [DecidableEq Digest]

/-- The requested table: extraction strictly before the first query of `startKey`, by anyone,
completed with `default` on the finite domain. This fixes the root, handle, domain and policy. -/
def pinnedRows (model : LeafHashing Row Query Digest) (depth : ℕ) (default : Row)
    (log : QueryLog (joint (fun _ : Event Row => Fin (2 ^ depth)) Unit Digest Query))
    (root : Digest) : Fin (2 ^ depth) → Row :=
  (words depth default).ofTable () ((scheme model depth).extract
    (hashEntries (beforeFirst (.inl (startKey depth root)) log)) () root)

/-- Exact requested-table agreement, with the bridge's normalization. No arbitrary witness
search, whole-log extraction, or independently selected bad table occurs here. -/
theorem checkpointTables_eq_pinned (model : LeafHashing Row Query Digest) (depth : ℕ)
    (default : Row)
    (log : QueryLog (joint (fun _ : Event Row => Fin (2 ^ depth)) Unit Digest Query))
    (root : Digest) :
    checkpointTables (words depth default) (scheme model depth) (fun root => [((), root)]) log
        (startKey depth root) root =
      [(words depth default).toTable () (pinnedRows model depth default log root)] := rfl

/-- The application's error is about its specified extracted pointer table and the mathematical
fraction of rejecting starts. It does not include a query-coverage hypothesis. -/
def ApplicationError (model : LeafHashing Row Query Digest) (depth additional : ℕ)
    (next : Row → Fin (2 ^ depth)) (accepts : Row → Bool) (fraction : ENNReal) (default : Row)
    (result : JointRun Digest (List Row) Row Digest Bool
      (QueryLog (joint (fun _ : Event Row => Fin (2 ^ depth)) Unit Digest Query))) : Prop :=
  Accepted (· = true) result.outcome ∧ FarPaths depth additional next accepts fraction
    (pinnedRows model depth default (result.proverLog ++ result.verifierLog) result.statement)

theorem applicationError_iff_pinnedFailure (model : LeafHashing Row Query Digest)
    (depth additional : ℕ) (next : Row → Fin (2 ^ depth)) (accepts : Row → Bool)
    (fraction : ENNReal) (default : Row)
    (result : JointRun Digest (List Row) Row Digest Bool
      (QueryLog (joint (fun _ : Event Row => Fin (2 ^ depth)) Unit Digest Query))) :
    ApplicationError model depth additional next accepts fraction default result ↔
      Application.PinnedFailure (words depth default) (scheme model depth)
        (fun root => [((), root)]) (startKey depth)
        (FalseTable depth additional next accepts fraction default) (· = true) result := by
  rw [Application.PinnedFailure, checkpointTables_eq_pinned]
  constructor
  · rintro ⟨accepted, far⟩
    exact ⟨accepted, _, rfl, far⟩
  · rintro ⟨accepted, rows, same, far⟩
    have agree : rows = pinnedRows model depth default
        (result.proverLog ++ result.verifierLog) result.statement := by
      funext index
      have entry := congrFun (List.cons.inj same).1 index.val
      simpa [words, index.isLt] using entry.symm
    exact ⟨accepted, agree ▸ far⟩

end Extraction

section Coverage

/-- Coverage follows from the real `run` computation, for every proof and all structural oracle
answers. In particular no successful execution can omit the initial challenge. -/
theorem verifier_queries_start (model : LeafHashing Row Query Digest) [DecidableEq Digest]
    (depth additional : ℕ) (next : Row → Fin (2 ^ depth)) (accepts : Row → Bool)
    (root : Digest) (proof : Proof (List Row) Row Digest)
    (result : PIR.Outcome Bool ×
      QueryLog (joint (fun _ : Event Row => Fin (2 ^ depth)) Unit Digest Query))
    (member : result ∈ support (run (absorb depth) (scheme model depth)
      (verifier depth additional next accepts) (initial root) [((), root)]
        proof.messages proof.openings).withQueryLog) :
    ∃ entry ∈ result.2, entry.1 = .inl (startKey depth root) := by
  rw [verifier, run.eq_def] at member
  simp only [absorb] at member
  exact Application.first_query_logged _ _ result member

theorem experiment_queries_start (model : LeafHashing Row Query Digest) [DecidableEq Digest]
    (depth additional : ℕ) (next : Row → Fin (2 ^ depth)) (accepts : Row → Bool)
    (prover : OracleComp (joint (fun _ : Event Row => Fin (2 ^ depth)) Unit Digest Query)
      (Digest × Proof (List Row) Row Digest))
    (result : JointRun Digest (List Row) Row Digest Bool
      (QueryLog (joint (fun _ : Event Row => Fin (2 ^ depth)) Unit Digest Query)))
    (member : result ∈ support (experiment (absorb depth) (scheme model depth)
      (fun _ => verifier depth additional next accepts) initial (fun root => [((), root)]) prover)) :
    ∃ entry ∈ result.verifierLog, entry.1 = .inl (startKey depth result.statement) := by
  simp only [experiment, support_bind, Set.mem_iUnion, exists_prop, support_pure,
    Set.mem_singleton_iff] at member
  obtain ⟨claim, -, checked, checkedMember, rfl⟩ := member
  exact verifier_queries_start model depth additional next accepts claim.1.1 claim.1.2 checked
    checkedMember

end Coverage

section Security
variable [DecidableEq Row] [DecidableEq Query] [DecidableEq Digest]
variable (model : LeafHashing Row Query Digest)

/-- The specified checkpoint is frozen after its first query, including a prover's early query. -/
theorem pinnedRows_append (depth : ℕ) (default : Row)
    (log later : QueryLog (joint (fun _ : Event Row => Fin (2 ^ depth)) Unit Digest Query))
    (root : Digest) (queried : ∃ entry ∈ log, entry.1 = .inl (startKey depth root)) :
    pinnedRows model depth default (log ++ later) root = pinnedRows model depth default log root := by
  simp only [pinnedRows, beforeFirst_append_of_mem _ later log queried]
  rfl

/-- Deduplicating cache-consistent prover queries preserves this application's event. This uses
the existing hashed-leaf first-match extractor, including normalization and the same root. -/
theorem applicationError_unseen (depth additional : ℕ) (next : Row → Fin (2 ^ depth))
    (accepts : Row → Bool) (fraction : ENNReal) (default : Row)
    (result : JointRun Digest (List Row) Row Digest Bool
      (QueryLog (joint (fun _ : Event Row => Fin (2 ^ depth)) Unit Digest Query)))
    (cache : (joint (fun _ : Event Row => Fin (2 ^ depth)) Unit Digest Query).QueryCache)
    (agree : ∀ entry ∈ result.proverLog, cache entry.1 = some entry.2) :
    ApplicationError model depth additional next accepts fraction default
        {result with proverLog := ZkcSecurity.VCVio.Memo.unseen ∅ result.proverLog} ↔
      ApplicationError model depth additional next accepts fraction default result := by
  rw [applicationError_iff_pinnedFailure, applicationError_iff_pinnedFailure]
  unfold Application.PinnedFailure
  simp only [checkpointTables_unseen (words depth default) (scheme model depth)
    (fun root => [((), root)]) (Extractable.comap_firstMatch model.scheme model.scheme_firstMatch
      (fun _ : Unit => depth)) result.proverLog result.verifierLog cache agree]

theorem applicationError_implies_checkpoint (depth additional : ℕ)
    (next : Row → Fin (2 ^ depth)) (accepts : Row → Bool) (fraction : ENNReal) (default : Row)
    (prover : OracleComp (joint (fun _ : Event Row => Fin (2 ^ depth)) Unit Digest Query)
      (Digest × Proof (List Row) Row Digest))
    (result : JointRun Digest (List Row) Row Digest Bool
      (QueryLog (joint (fun _ : Event Row => Fin (2 ^ depth)) Unit Digest Query)))
    (member : result ∈ support (experiment (absorb depth) (scheme model depth)
      (fun _ => verifier depth additional next accepts) initial (fun root => [((), root)]) prover))
    (failure : ApplicationError model depth additional next accepts fraction default result) :
    FalseAcceptance (words depth default) (scheme model depth) (fun root => [((), root)])
      (FalseTable depth additional next accepts fraction default) (· = true) result :=
  Application.pinned_implies_falseAcceptance _ _ _ _ _ _ result
    (experiment_queries_start model depth additional next accepts prover result member)
    ((applicationError_iff_pinnedFailure model depth additional next accepts fraction default
      result).mp failure)

/-- Worst-case total oracle calls: one challenge and `additional + 1` authentications, each of
at most `depth + 1` calls. Cache hits and repeated positions are counted as calls. -/
def verifierQueries (depth additional : ℕ) : ℕ := 1 + (additional + 1) * (depth + 1)

omit [DecidableEq Row] [DecidableEq Query] in
theorem verifier_queryBound (depth additional : ℕ) (next : Row → Fin (2 ^ depth))
    (accepts : Row → Bool) (root : Digest) (proof : Proof (List Row) Row Digest) :
    IsTotalQueryBound (run (absorb depth) (scheme model depth)
      (verifier depth additional next accepts) (initial root) [((), root)]
        proof.messages proof.openings) (verifierQueries depth additional) := by
  simpa only [verifierQueries, nsmul_eq_mul, Nat.cast_id] using
    run_queryBound (absorb depth) (fun _ : Unit => True) (scheme model depth) (depth + 1)
      (fun _ _ root position opening =>
        LeafHashing.authenticate_queryBound model depth root position opening)
      _ _ (verifier_charged depth additional next accepts (fun _ => 1) (depth + 1))
      (initial root) [((), root)] proof.messages proof.openings (fun _ _ => trivial)

omit [DecidableEq Row] [DecidableEq Query] in
theorem verifier_costBound (depth additional : ℕ) (next : Row → Fin (2 ^ depth))
    (accepts : Row → Bool) (fraction hashError : ENNReal) (root : Digest)
    (proof : Proof (List Row) Row Digest) :
    WorstCaseCostBound (run (absorb depth) (scheme model depth)
      (verifier depth additional next accepts) (initial root) [((), root)]
        proof.messages proof.openings)
      ⟨jointError (error fraction) hashError⟩
      ((1 - fraction) + (additional + 1 : ℕ) * ((depth + 1 : ℕ) * hashError)) := by
  simpa only [nsmul_eq_mul, error] using
    run_costBound (absorb depth) (fun _ : Unit => True) (scheme model depth) (error fraction)
      hashError (depth + 1)
      (fun _ _ root position opening =>
        LeafHashing.authenticate_queryBound model depth root position opening)
      _ _ (verifier_charged depth additional next accepts (error fraction)
        ((depth + 1 : ℕ) * hashError))
      (initial root) [((), root)] proof.messages proof.openings (fun _ _ => trivial)

/-- One joint charge for hash collision/drift targets: one root and at most two input labels. -/
noncomputable def hashError [Fintype Digest] (depth additional queries : ℕ) : ENNReal :=
  (((4 * (queries + verifierQueries depth additional) : ℕ) : ENNReal) / Fintype.card Digest)

/-- The existing commitment bound, with this client's certificate and every verifier-side
condition discharged. The prover is arbitrary and adaptive subject only to its total call bound. -/
theorem checkpoint_soundness [SampleableType Digest] [Fintype Digest]
    (depth additional : ℕ) (next : Row → Fin (2 ^ depth)) (accepts : Row → Bool)
    (fraction : ENNReal) (default : Row)
    (prover : OracleComp (joint (fun _ : Event Row => Fin (2 ^ depth)) Unit Digest Query)
      (Digest × Proof (List Row) Row Digest))
    (queries : ℕ) (bounded : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle (experiment (absorb depth) (scheme model depth)
      (fun _ => verifier depth additional next accepts) initial (fun root => [((), root)])
        prover)).run' ∅}[
      FalseAcceptance (words depth default) (scheme model depth) (fun root => [((), root)])
        (FalseTable depth additional next accepts fraction default) (· = true) result] ≤
      queries * ((1 - fraction) + hashError (Digest := Digest) depth additional queries) +
        ((1 - fraction) + (additional + 1 : ℕ) *
          ((depth + 1 : ℕ) * hashError (Digest := Digest) depth additional queries)) := by
  apply ZkcSecurity.Commitment.soundness (absorb depth) (words depth default) (scheme model depth)
    (fun _ => verifier depth additional next accepts) initial (fun root => [((), root)]) prover
    (certificate depth additional next accepts fraction default) (fun _ => ⟨_, _, rfl⟩)
    (carries model depth default) initial_determined (fun _ => rfl) 1 (fun _ => le_rfl)
    (fun _ => verifier_commitBound depth additional next accepts)
    (FalseTable depth additional next accepts fraction default)
    (fun _ _ falseTable => by
      obtain ⟨rows, rfl, far⟩ := falseTable
      exact Or.inr (Or.inr ⟨rows, far, rfl⟩))
    2 (fun query => LeafHashing.inputs_length model query) queries
    (verifierQueries depth additional) bounded
    (fun root proof => verifier_queryBound model depth additional next accepts root proof)
  · exact Typed.worstCaseCostBound_of_isTotalQueryBound _ (fun key => by
      cases key with
      | inl key =>
          change error fraction key.2 ≤ _
          cases key.2 with
          | table _ => exact zero_le
          | index => exact le_self_add
      | inr _ => exact le_add_self) prover queries bounded
  · exact fun root proof => verifier_costBound model depth additional next accepts fraction _
      root proof

/-- Application security for at least two adaptive reads (`additional + 2` in total). The event
is the mathematical error on the specified pinned table, with no assumed event implication or
query coverage. Both hash calls and challenge grinding are charged by the existing joint bound. -/
theorem soundness [SampleableType Digest] [Fintype Digest]
    (depth additional : ℕ) (next : Row → Fin (2 ^ depth)) (accepts : Row → Bool)
    (fraction : ENNReal) (default : Row)
    (prover : OracleComp (joint (fun _ : Event Row => Fin (2 ^ depth)) Unit Digest Query)
      (Digest × Proof (List Row) Row Digest))
    (queries : ℕ) (bounded : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle (experiment (absorb depth) (scheme model depth)
      (fun _ => verifier depth (additional + 1) next accepts) initial (fun root => [((), root)])
        prover)).run' ∅}[
      ApplicationError model depth (additional + 1) next accepts fraction default result] ≤
      queries * ((1 - fraction) + hashError (Digest := Digest) depth (additional + 1) queries) +
        ((1 - fraction) + (additional + 2 : ℕ) *
          ((depth + 1 : ℕ) * hashError (Digest := Digest) depth (additional + 1) queries)) := by
  refine (prEvent_mono_of_support _ _ _ fun result member failure =>
    applicationError_implies_checkpoint model depth (additional + 1) next accepts fraction default
      prover result (support_simulateQ_run'_subset randomOracle _ ∅ member) failure).trans ?_
  exact checkpoint_soundness model depth (additional + 1) next accepts fraction default prover
    queries bounded

end Security

end ZkcSecurity.Commitment.AdaptiveOpening
