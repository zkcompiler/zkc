module

public import ZkcSecurity.Commitment.Replay
public import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

@[expose] public section

/-! # The joint experiment for verifiers that see roots and openings

The joint experiment (`experiment`) shares one lazily sampled random oracle on transcript keys and
hash calls (`joint`). A prover makes arbitrary adaptive queries to both families and outputs a
statement and a concrete proof: messages, committed roots and openings. The concrete reading of
the statement's verifier (`run`) then absorbs the roots, asks the transcript oracle at every query
and authenticates every read against its root with hash calls. Both runs are logged.

**Checkpoints.** The table committed by a root is extracted from the record of hash calls before
the first query, by anyone, of a transcript key containing that root (`checkpointTables`): the
extraction is fixed before that key's answer is sampled, and repeated queries of the key reuse it.
A false statement is a statement whose committed tables, extracted at the checkpoint of a
transcript query of the verifier, are false (`FalseAcceptance`). The event asks for some query of
the verifier, so it contains the event for the verifier's first query; it is empty for a verifier
that makes no transcript query. Different checkpoints of one root may extract different tables;
they agree outside the drift event, which the bound charges, so the false statement is fixed up to
that event.

**Bad keys.** A transcript key is bad when replaying a statement's verifier along it, with every
root read as its checkpoint extraction, reaches a doomed query whose answer at the key escapes; a
hash call is bad when its answer hits a target of the record before its first query (`Bad`). The
first `rootBound` roots of every transcript key in the record are targets, whoever queried the key:
the adversary's keys are not bounded, and the verifier's keys carry at most `rootBound` roots. The
charge of a transcript key is the error of its occurrence, and every hash call is charged one
`hashError` (`jointError`). The record before a key's first query does not depend on that key's
answer (`beforeFirstKey_update`), so neither do the checkpoint extraction and the targets
(`hashLog_update_inl`, `targets_update_inr`).
-/

set_option autoImplicit false

namespace ZkcSecurity.Commitment

open OracleComp OracleSpec ZkcSecurity.FiatShamir

variable {J : PIR.Signature} {E P Shape Value Query Y A Stmt : Type} {R : List E → Type}

/-- The hash calls of a joint log. -/
def hashEntries (log : QueryLog (joint R Shape Y Query)) : HashLog Query Y :=
  log.filterMap fun entry =>
    match entry with
    | ⟨.inr query, answer⟩ => some ⟨query, answer⟩
    | ⟨.inl _, _⟩ => none

section Logs
variable [DecidableEq E] [DecidableEq Shape] [DecidableEq Y] [DecidableEq Query]

theorem map_fst_beforeFirst (key : JointKey E Shape Y Query) :
    ∀ log : QueryLog (joint R Shape Y Query),
      (beforeFirst key log).map Sigma.fst = beforeFirstKey key (log.map Sigma.fst)
  | [] => rfl
  | entry :: rest => by
      rw [beforeFirst_cons, List.map_cons, beforeFirstKey, List.takeWhile_cons]
      by_cases same : entry.1 = key
      · simp [same]
      · simp only [same, ↓reduceIte, List.map_cons, ne_eq, not_false_eq_true, decide_true]
        exact congrArg _ (map_fst_beforeFirst key rest)

omit [DecidableEq E] [DecidableEq Shape] [DecidableEq Y] [DecidableEq Query] in
/-- The hash calls of a table log are the hash log of its keys. -/
theorem hashEntries_eq (table : JointTable R Shape Y Query) :
    ∀ log : QueryLog (joint R Shape Y Query),
      (∀ entry ∈ log, entry = ⟨entry.1, table entry.1⟩) →
      hashEntries log = hashLog table (log.map Sigma.fst)
  | [] => fun _ => rfl
  | ⟨key, answer⟩ :: rest => fun consistent => by
      have head := consistent _ List.mem_cons_self
      have tail := hashEntries_eq table rest
        fun entry member => consistent entry (List.mem_cons_of_mem _ member)
      simp only at head
      cases key with
      | inl transcript =>
          change hashEntries rest = hashLog table ([.inl transcript] ++ rest.map Sigma.fst)
          rw [hashLog_append, hashLog_singleton_inl, List.nil_append]
          exact tail
      | inr query =>
          simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at head
          subst head
          change ⟨query, table (.inr query)⟩ :: hashEntries rest =
            hashLog table ([.inr query] ++ rest.map Sigma.fst)
          rw [hashLog_append, hashLog_singleton_inr, tail]
          rfl

theorem not_mem_beforeFirstKey (key : JointKey E Shape Y Query) :
    ∀ keys : List (JointKey E Shape Y Query), key ∉ beforeFirstKey key keys
  | [] => by simp [beforeFirstKey]
  | head :: tail => by
      by_cases same : head = key
      · simp [beforeFirstKey, same]
      · simp only [beforeFirstKey, List.takeWhile_cons, ne_eq, same, not_false_eq_true,
          decide_true, ↓reduceIte, List.mem_cons, not_or]
        exact ⟨Ne.symm same, not_mem_beforeFirstKey key tail⟩

theorem beforeFirstKey_update {α : Type} (game : OracleComp (joint R Shape Y Query) α)
    (table : JointTable R Shape Y Query) (key : JointKey E Shape Y Query)
    (answer : JointRange R Shape Y Query key) :
    beforeFirstKey key ((tableQueryLog game (Function.update table key answer)).map Sigma.fst) =
      beforeFirstKey key ((tableQueryLog game table).map Sigma.fst) := by
  rw [← map_fst_beforeFirst, ← map_fst_beforeFirst, beforeFirst_update]

theorem hashLog_update_inl (table : JointTable R Shape Y Query) (key : TranscriptKey E Shape Y)
    (answer : JointRange R Shape Y Query (.inl key)) (keys : List (JointKey E Shape Y Query)) :
    hashLog (Function.update table (.inl key) answer) keys = hashLog table keys := by
  unfold hashLog
  congr 1

theorem targets_update_inr (scheme : Extractable Shape Value Query Y) (bound : ℕ)
    (table : JointTable R Shape Y Query) (query : Query)
    (answer : JointRange R Shape Y Query (.inr query)) :
    ∀ keys : List (JointKey E Shape Y Query), (.inr query : JointKey E Shape Y Query) ∉ keys →
      targets scheme bound (Function.update table (.inr query) answer) keys =
        targets scheme bound table keys
  | [] => fun _ => rfl
  | key :: rest => fun absent => by
      have later := targets_update_inr scheme bound table query answer rest
        fun member => absent (List.mem_cons_of_mem _ member)
      have here : key ≠ .inr query := fun same => absent (same ▸ List.mem_cons_self)
      rw [show key :: rest = [key] ++ rest from rfl, targets_append, targets_append, later]
      congr 1
      cases key with
      | inl _ => rfl
      | inr other =>
          simp only [targets, List.flatMap_cons, List.flatMap_nil, List.append_nil, keyTargets]
          rw [Function.update_of_ne here]

end Logs

/-- At most `bound` labels per key in the targets of a record. -/
theorem targets_length_le (scheme : Extractable Shape Value Query Y) (bound inputBound : ℕ)
    (inputs : ∀ query, (scheme.inputs query).length ≤ inputBound)
    (table : JointTable R Shape Y Query) :
    ∀ keys : List (JointKey E Shape Y Query),
      (targets scheme bound table keys).length ≤ (bound + inputBound + 1) * keys.length
  | [] => by simp [targets]
  | key :: rest => by
      have later := targets_length_le scheme bound inputBound inputs table rest
      rw [show key :: rest = [key] ++ rest from rfl, targets_append, List.length_append]
      have here : (targets scheme bound table [key]).length ≤ bound + inputBound + 1 := by
        cases key with
        | inl transcript =>
            simp only [targets, List.flatMap_cons, List.flatMap_nil, List.append_nil, keyTargets,
              keyRoots, List.length_take]
            omega
        | inr query =>
            simp only [targets, List.flatMap_cons, List.flatMap_nil, List.append_nil, keyTargets]
            show (scheme.inputs query).length + 1 ≤ bound + inputBound + 1
            have := inputs query
            omega
      simp only [List.length_append, List.length_cons, List.length_nil] at later ⊢
      nlinarith

/-- A uniform hash answer lands in a list of labels with probability at most its length over the
number of hash values. -/
theorem prEvent_mem_le [SampleableType Y] [Fintype Y] (labels : List Y) :
    Pr{let answer ← $ᵗ Y}[answer ∈ labels] ≤ (labels.length : ENNReal) / Fintype.card Y := by
  classical
  rw [SampleableType.prEvent_uniformSample]
  apply ENNReal.div_le_div_right
  exact_mod_cast (Finset.card_le_card (fun answer member => by
    simpa using member : Finset.univ.filter (· ∈ labels) ⊆ labels.toFinset)).trans
    (List.toFinset_card_le labels)

section Experiment
variable (absorb : Typed.Interface J E P R) (words : Words J Shape Value)
  (scheme : Extractable Shape Value Query Y)

/-- The logged runs of the joint experiment: the prover's claim, the verifier's outcome, and the
prover's and verifier's query logs. -/
structure JointRun (Stmt P Value Y A Log : Type) where
  statement : Stmt
  proof : Proof P Value Y
  outcome : PIR.Outcome A
  proverLog : Log
  verifierLog : Log

/-- The joint experiment: the prover, then the concrete reading of its statement's verifier on
its proof, on one shared oracle, both logged. -/
def experiment (verifier : Stmt → PIR.Proc (committed J Shape Value) A)
    (initial : Stmt → List (Absorbed E Shape Y)) (statementRoots : Stmt → List (Shape × Y))
    (prover : OracleComp (joint R Shape Y Query) (Stmt × Proof P Value Y)) :
    OracleComp (joint R Shape Y Query)
      (JointRun Stmt P Value Y A (QueryLog (joint R Shape Y Query))) :=
  prover.withQueryLog >>= fun proverRun =>
    (run absorb scheme (verifier proverRun.1.1) (initial proverRun.1.1)
      (statementRoots proverRun.1.1) proverRun.1.2.messages proverRun.1.2.openings).withQueryLog
      >>= fun verifierRun =>
    pure { statement := proverRun.1.1, proof := proverRun.1.2, outcome := verifierRun.1,
           proverLog := proverRun.2, verifierLog := verifierRun.2 }

/-- The statement's tables extracted at the checkpoint of a transcript key. -/
def checkpointTables [DecidableEq E] [DecidableEq Shape] [DecidableEq Y] [DecidableEq Query]
    (statementRoots : Stmt → List (Shape × Y)) (log : QueryLog (joint R Shape Y Query))
    (key : TranscriptKey E Shape Y) (statement : Stmt) : List (Table Value) :=
  (statementRoots statement).map fun pair =>
    normalized words (scheme.extract (hashEntries (beforeFirst (.inl key) log))) pair.1 pair.2

/-- The verifier accepts, and the statement is false for its tables extracted at the checkpoint
of one of the verifier's transcript queries. -/
def FalseAcceptance [DecidableEq E] [DecidableEq Shape] [DecidableEq Y] [DecidableEq Query]
    (statementRoots : Stmt → List (Shape × Y)) (falseStatement : Stmt → List (Table Value) → Prop)
    (accepts : A → Prop) (result : JointRun Stmt P Value Y A (QueryLog (joint R Shape Y Query))) :
    Prop :=
  Accepted accepts result.outcome ∧
    ∃ entry ∈ result.verifierLog, ∃ key, entry.1 = .inl key ∧
      falseStatement result.statement (checkpointTables words scheme statementRoots
        (result.proverLog ++ result.verifierLog) key result.statement)

variable (verifier : Stmt → PIR.Proc (committed J Shape Value) A)
  (initial : Stmt → List (Absorbed E Shape Y)) (statementRoots : Stmt → List (Shape × Y))
  (prover : OracleComp (joint R Shape Y Query) (Stmt × Proof P Value Y))

theorem evalWithAnswerFn_experiment (table : JointTable R Shape Y Query) :
    evalWithAnswerFn (QueryImpl.ofFn table)
        (experiment absorb scheme verifier initial statementRoots prover) =
      { statement := (evalWithAnswerFn (QueryImpl.ofFn table) prover).1
        proof := (evalWithAnswerFn (QueryImpl.ofFn table) prover).2
        outcome := evalWithAnswerFn (QueryImpl.ofFn table) (run absorb scheme
          (verifier (evalWithAnswerFn (QueryImpl.ofFn table) prover).1)
          (initial (evalWithAnswerFn (QueryImpl.ofFn table) prover).1)
          (statementRoots (evalWithAnswerFn (QueryImpl.ofFn table) prover).1)
          (evalWithAnswerFn (QueryImpl.ofFn table) prover).2.messages
          (evalWithAnswerFn (QueryImpl.ofFn table) prover).2.openings)
        proverLog := tableQueryLog prover table
        verifierLog := tableQueryLog (run absorb scheme
          (verifier (evalWithAnswerFn (QueryImpl.ofFn table) prover).1)
          (initial (evalWithAnswerFn (QueryImpl.ofFn table) prover).1)
          (statementRoots (evalWithAnswerFn (QueryImpl.ofFn table) prover).1)
          (evalWithAnswerFn (QueryImpl.ofFn table) prover).2.messages
          (evalWithAnswerFn (QueryImpl.ofFn table) prover).2.openings) table } := by
  simp only [experiment, evalWithAnswerFn_bind, evalWithAnswerFn_withQueryLog,
    evalWithAnswerFn_pure]

theorem tableQueryLog_experiment (table : JointTable R Shape Y Query) :
    tableQueryLog (experiment absorb scheme verifier initial statementRoots prover) table =
      tableQueryLog prover table ++ tableQueryLog (run absorb scheme
          (verifier (evalWithAnswerFn (QueryImpl.ofFn table) prover).1)
          (initial (evalWithAnswerFn (QueryImpl.ofFn table) prover).1)
          (statementRoots (evalWithAnswerFn (QueryImpl.ofFn table) prover).1)
          (evalWithAnswerFn (QueryImpl.ofFn table) prover).2.messages
          (evalWithAnswerFn (QueryImpl.ofFn table) prover).2.openings) table := by
  simp only [experiment, tableQueryLog_bind, tableQueryLog_withQueryLog,
    evalWithAnswerFn_withQueryLog, tableQueryLog_pure, List.append_nil]

end Experiment

section Bad
variable [DecidableEq E] [DecidableEq Shape] [DecidableEq Y] [DecidableEq Query]
variable (absorb : Typed.Interface J E P R) (words : Words J Shape Value)
  (scheme : Extractable Shape Value Query Y)

/-- The extraction at the checkpoint of a transcript key: from the hash calls before the key's
first query in the table run of `game`. -/
def checkpointExtract {α : Type} (game : OracleComp (joint R Shape Y Query) α)
    (table : JointTable R Shape Y Query) (key : TranscriptKey E Shape Y) : Shape → Y → Table Value :=
  scheme.extract (hashLog table (beforeFirstKey (.inl key) ((tableQueryLog game table).map Sigma.fst)))

/-- Bad keys of the joint table run of `game`. A transcript key is bad when replaying a
statement's verifier along it, with every root read as its checkpoint extraction, reaches a doomed
query whose answer at the key escapes. A hash call is bad when its answer hits a target of the
record before its first query. -/
def Bad {α : Type} (game : OracleComp (joint R Shape Y Query) α) (doomed : PIR.Proc J A → Prop)
    (verifier : Stmt → PIR.Proc (committed J Shape Value) A)
    (initial : Stmt → List (Absorbed E Shape Y)) (statementRoots : Stmt → List (Shape × Y))
    (bound : ℕ) : (key : JointKey E Shape Y Query) → JointTable R Shape Y Query → Prop
  | .inl key, table =>
      ∃ statement events residual tables, key.1 = initial statement ++ events ∧
        replay absorb words (checkpointExtract scheme game table key)
            (fun other => table (.inl other)) (verifier statement)
            ((statementRoots statement).map fun pair =>
              normalized words (checkpointExtract scheme game table key) pair.1 pair.2)
            (initial statement) events = some (residual, tables) ∧
          Escapes absorb words doomed residual tables key.2 (table (.inl key))
  | .inr query, table =>
      table (.inr query) ∈ targets scheme bound table
        (beforeFirstKey (.inr query) ((tableQueryLog game table).map Sigma.fst))

/-- The charge of a joint key: a transcript key is charged the error of its occurrence, a hash
call `hashError`. -/
def jointError (error : E → ENNReal) (hashError : ENNReal) : JointKey E Shape Y Query → ENNReal
  | .inl key => error key.2
  | .inr _ => hashError

end Bad

end ZkcSecurity.Commitment
