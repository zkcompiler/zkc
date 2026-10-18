module

public import ZkcSecurity.Commitment.Escape

@[expose] public section

/-! # Soundness of verifiers that see roots and openings

`soundness_weighted` turns a typed Fiat–Shamir certificate for the ideal reading of a verifier
with committed tables (`withTables`: every committed table received in the clear) into a bound for
its concrete reading (`run`), which sees only roots and openings, in the joint experiment
(`experiment`): one lazily sampled random oracle shared by the transcript keys and the hash calls,
with the prover querying both families adaptively.

The verifier accepts a false statement (`FalseAcceptance`: the statement is false for its tables
extracted at the checkpoint of one of the verifier's transcript queries) with probability at most
the prover's charge plus the verifier's charge, where every transcript key is charged the error of
its query's occurrence in the certificate, as in the ideal reading's Fiat–Shamir bound
(`ZkcSecurity.FiatShamir.Typed.adaptive_soundness_weighted`), and every hash call is charged
`targetBound / |Y|`. `targetBound` bounds the targets of every record of the experiment: earlier
hash answers (collisions), earlier input labels and the roots of earlier transcript keys (hits that
change a checkpoint's extraction, that is, drift). `soundness` instantiates it from query counts:
`(rootBound + inputBound + 1) · (proverQueries + verifierQueries)`.

The verifier's premises are structural:
- commitments are received through word operations that the ideal reading receives
  (`commitReceives`), and a statement's committed roots are the roots of its initial history
  (`initialRoots`), at most `rootBound` roots in every transcript key the verifier queries
  (`statementBound`, `commitBound`);
- the ideal reading's words carry every extracted entry (`carries`);
- a false statement's ideal reading is doomed (`doomedValidator`).

The proof is one application of VCVio's weighted bad-query bound to the joint oracle
(`prEvent_randomOracle_le_of_bad_queries_weighted`): `bad_transcript_resample` and
`bad_hash_resample` bound the resampling of each key, and `trace` shows that a false acceptance
queries a bad key.
-/

set_option autoImplicit false

namespace ZkcSecurity.Commitment

open OracleComp OracleSpec ZkcSecurity.FiatShamir

variable {J : PIR.Signature} {E P Shape Value Query Y A Stmt : Type} {R : List E → Type}
variable [DecidableEq E] [DecidableEq Shape] [DecidableEq Y] [DecidableEq Query]
variable [∀ key, SampleableType (R key)]
variable (absorb : Typed.Interface J E P R) (words : Words J Shape Value)
  (scheme : Extractable Shape Value Query Y)

/-- Resampling a transcript key's answer makes it bad with probability at most the error of its
occurrence: its checkpoint extraction and the replay before it are fixed before the answer. -/
theorem bad_transcript_resample [SampleableType Y] {accepts : A → Prop} {error : E → ENNReal}
    (certificate : Typed.Certificate absorb accepts error) {α : Type}
    (game : OracleComp (joint R Shape Y Query) α)
    (verifier : Stmt → PIR.Proc (committed J Shape Value) A)
    (initial : Stmt → List (Absorbed E Shape Y)) (determined : Typed.Determined initial)
    (statementRoots : Stmt → List (Shape × Y)) (bound : ℕ) (key : TranscriptKey E Shape Y)
    (table : JointTable R Shape Y Query) :
    Pr{let answer ← $ᵗ (JointRange R Shape Y Query (.inl key))}[
      Bad absorb words scheme game certificate.doomed verifier initial statementRoots bound (.inl key)
        (Function.update table (.inl key) answer)] ≤ error key.2 := by
  have frozen : ∀ answer : JointRange R Shape Y Query (.inl key),
      checkpointExtract scheme game (Function.update table (.inl key) answer) key =
        checkpointExtract scheme game table key := by
    intro answer
    unfold checkpointExtract
    rw [beforeFirstKey_update, hashLog_update_inl]
  set extract := checkpointExtract scheme game table key
  have shorter : ∀ (answer : JointRange R Shape Y Query (.inl key)) (statement : Stmt)
      (events : List (Absorbed E Shape Y)), key.1 = initial statement ++ events →
      replay absorb words extract (fun other => Function.update table (.inl key) answer (.inl other))
          (verifier statement) ((statementRoots statement).map fun pair =>
            normalized words extract pair.1 pair.2) (initial statement) events =
        replay absorb words extract (fun other => table (.inl other)) (verifier statement)
          ((statementRoots statement).map fun pair => normalized words extract pair.1 pair.2)
          (initial statement) events := by
    intro answer statement events shape
    refine replay_congr_answers absorb words extract _ events _ _ _ fun other length => ?_
    have different : (.inl other : JointKey E Shape Y Query) ≠ .inl key := by
      intro same
      simp only [Sum.inl.injEq] at same
      subst same
      rw [shape, List.length_append] at length
      omega
    exact Function.update_of_ne different _ _
  by_cases found : ∃ statement events residual tables, key.1 = initial statement ++ events ∧
      replay absorb words extract (fun other => table (.inl other)) (verifier statement)
        ((statementRoots statement).map fun pair => normalized words extract pair.1 pair.2)
        (initial statement) events = some (residual, tables)
  · obtain ⟨statement, events, residual, tables, shape, replayed⟩ := found
    have reduced : ∀ answer : JointRange R Shape Y Query (.inl key),
        Bad absorb words scheme game certificate.doomed verifier initial statementRoots bound
            (.inl key) (Function.update table (.inl key) answer) →
          Escapes absorb words certificate.doomed residual tables key.2 answer := by
      intro answer bad
      obtain ⟨statement', events', residual', tables', shape', replayed', escapes⟩ := bad
      have same : statement = statement' :=
        determined _ _ events events' (shape.symm.trans shape')
      subst same
      have sameEvents : events = events' := List.append_cancel_left (shape.symm.trans shape')
      subst sameEvents
      rw [frozen, shorter answer statement events shape, replayed] at replayed'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj replayed')
      simpa only [Function.update_self] using escapes
    exact (prEvent_mono _ _ (fun answer => Escapes absorb words certificate.doomed residual tables
      key.2 answer) fun answer bad => reduced answer bad).trans
      (escapes_le absorb words certificate residual tables key.2)
  · have never : ∀ answer : JointRange R Shape Y Query (.inl key),
        ¬ Bad absorb words scheme game certificate.doomed verifier initial statementRoots bound
          (.inl key) (Function.update table (.inl key) answer) := by
      intro answer bad
      obtain ⟨statement, events, residual, tables, shape, replayed, _⟩ := bad
      rw [frozen, shorter answer statement events shape] at replayed
      exact found ⟨statement, events, residual, tables, shape, replayed⟩
    exact (prEvent_eq_zero_of_forall_not _ _ never).trans_le zero_le

/-- Resampling a hash call's answer makes it bad with probability at most the number of targets
over the number of hash values: the targets are fixed before the call's first query. -/
theorem bad_hash_resample [SampleableType Y] [Fintype Y] {α : Type}
    (game : OracleComp (joint R Shape Y Query) α) (doomed : PIR.Proc J A → Prop)
    (verifier : Stmt → PIR.Proc (committed J Shape Value) A)
    (initial : Stmt → List (Absorbed E Shape Y)) (statementRoots : Stmt → List (Shape × Y))
    (bound targetBound : ℕ)
    (targetsBounded : ∀ table : JointTable R Shape Y Query,
      (targets scheme bound table ((tableQueryLog game table).map Sigma.fst)).length ≤ targetBound)
    (query : Query) (table : JointTable R Shape Y Query) :
    Pr{let answer ← $ᵗ (JointRange R Shape Y Query (.inr query))}[
      Bad absorb words scheme game doomed verifier initial statementRoots bound (.inr query)
        (Function.update table (.inr query) answer)] ≤
      (targetBound : ENNReal) / Fintype.card Y := by
  set before := beforeFirstKey (.inr query) ((tableQueryLog game table).map Sigma.fst)
  have fixed : ∀ answer : JointRange R Shape Y Query (.inr query),
      Bad absorb words scheme game doomed verifier initial statementRoots bound (.inr query)
          (Function.update table (.inr query) answer) ↔
        (answer : Y) ∈ targets scheme bound table before := by
    intro answer
    change Function.update table (.inr query) answer (.inr query) ∈ targets scheme bound
      (Function.update table (.inr query) answer) (beforeFirstKey (.inr query)
        ((tableQueryLog game (Function.update table (.inr query) answer)).map Sigma.fst)) ↔ _
    rw [beforeFirstKey_update, Function.update_self,
      targets_update_inr scheme bound table query answer before
        (not_mem_beforeFirstKey (.inr query) _)]
  have length : (targets scheme bound table before).length ≤ targetBound := by
    refine le_trans ?_ (targetsBounded table)
    have split := List.takeWhile_append_dropWhile (p := fun other =>
      decide (other ≠ (.inr query : JointKey E Shape Y Query)))
      (l := (tableQueryLog game table).map Sigma.fst)
    conv_rhs => rw [← split]
    rw [targets_append, List.length_append]
    exact Nat.le_add_right _ _
  calc Pr{let answer ← $ᵗ (JointRange R Shape Y Query (.inr query))}[
          Bad absorb words scheme game doomed verifier initial statementRoots bound (.inr query)
            (Function.update table (.inr query) answer)]
      = Pr{let answer ← $ᵗ Y}[answer ∈ targets scheme bound table before] :=
        prEvent_congr _ _ _ fun answer => fixed answer
    _ ≤ ((targets scheme bound table before).length : ENNReal) / Fintype.card Y :=
        prEvent_mem_le _
    _ ≤ (targetBound : ENNReal) / Fintype.card Y :=
        ENNReal.div_le_div_right (by exact_mod_cast length) _

section Trace
variable (verifier : Stmt → PIR.Proc (committed J Shape Value) A)
  (initial : Stmt → List (Absorbed E Shape Y)) (statementRoots : Stmt → List (Shape × Y))
  (prover : OracleComp (joint R Shape Y Query) (Stmt × Proof P Value Y))

omit [DecidableEq E] [DecidableEq Shape] [DecidableEq Y] [DecidableEq Query]
  [∀ key, SampleableType (R key)] in
/-- A transcript key whose history starts with a statement's initial history keeps the
statement's roots among its first `bound` roots. -/
theorem statement_mem_keyRoots {bound : ℕ} {statementRoots : List (Shape × Y)}
    {initial : List (Absorbed E Shape Y)}
    (initialRoots : initial.filterMap Absorbed.committed = statementRoots)
    (statementBound : statementRoots.length ≤ bound) {key : TranscriptKey E Shape Y}
    (extends_ : initial <+: key.1) {pair : Shape × Y} (member : pair ∈ statementRoots) :
    pair.2 ∈ keyRoots bound key := by
  obtain ⟨rest, shape⟩ := extends_
  unfold keyRoots
  rw [← shape, List.filterMap_append, initialRoots, List.map_append,
    List.take_append, List.take_of_length_le (by simpa using statementBound)]
  exact List.mem_append_left _ (List.mem_map_of_mem member)

omit [DecidableEq E] [DecidableEq Shape] [DecidableEq Y] [DecidableEq Query]
  [∀ key, SampleableType (R key)] in
/-- A history whose committed roots are the statement's roots followed by at most
`bound - |statement roots|` more roots keeps all of them among its first `bound`. -/
theorem mem_keyRoots {bound : ℕ} {statementRoots : List (Shape × Y)}
    {initial events : List (Absorbed E Shape Y)} (occurrence : E)
    (initialRoots : initial.filterMap Absorbed.committed = statementRoots)
    (counted : statementRoots.length + (events.filterMap Absorbed.committed).length ≤ bound)
    {pair : Shape × Y}
    (member : pair ∈ statementRoots ∨ Absorbed.root pair.1 pair.2 ∈ events) :
    pair.2 ∈ keyRoots bound (initial ++ events, occurrence) := by
  unfold keyRoots
  simp only [List.filterMap_append, initialRoots]
  rw [List.take_of_length_le (by simpa using counted)]
  rw [List.map_append, List.mem_append]
  rcases member with statementMember | eventMember
  · exact Or.inl (List.mem_map_of_mem statementMember)
  · refine Or.inr (List.mem_map.mpr ⟨pair, ?_, rfl⟩)
    exact List.mem_filterMap.mpr ⟨_, eventMember, rfl⟩

/-- A false acceptance queries a bad key: if no hash call is bad, the record is good, the
checkpoint extractions and every accepted opening agree with the extraction from the whole
record, and the accepting run escapes the doomed ideal reading at one of its own transcript
queries. -/
theorem trace {accepts : A → Prop} {error : E → ENNReal}
    (certificate : Typed.Certificate absorb accepts error)
    (commitReceives : ∀ shape, ∃ event recover, absorb (words.word shape) = .receive event recover)
    (carries : ∀ log shape root position value, scheme.extract log shape root position = some value →
      normalized words (scheme.extract log) shape root position = some value)
    (initialRoots : ∀ statement,
      (initial statement).filterMap Absorbed.committed = statementRoots statement)
    (rootBound : ℕ)
    (statementBound : ∀ statement, (statementRoots statement).length ≤ rootBound)
    (commitBound : ∀ statement,
      CommitBound (verifier statement) (rootBound - (statementRoots statement).length))
    (falseStatement : Stmt → List (Table Value) → Prop)
    (doomedValidator : ∀ statement tables, falseStatement statement tables →
      certificate.doomed (withTables words tables (verifier statement)))
    (table : JointTable R Shape Y Query)
    (event : FalseAcceptance words scheme statementRoots falseStatement accepts
      (evalWithAnswerFn (QueryImpl.ofFn table)
        (experiment absorb scheme verifier initial statementRoots prover))) :
    ∃ entry ∈ tableQueryLog (experiment absorb scheme verifier initial statementRoots prover) table,
      Bad absorb words scheme (experiment absorb scheme verifier initial statementRoots prover)
        certificate.doomed verifier initial statementRoots rootBound entry.1 table := by
  rw [evalWithAnswerFn_experiment] at event
  set game := experiment absorb scheme verifier initial statementRoots prover
  set claim := evalWithAnswerFn (QueryImpl.ofFn table) prover
  set verifierRun := run absorb scheme (verifier claim.1) (initial claim.1) (statementRoots claim.1)
    claim.2.messages claim.2.openings
  have fullLog : tableQueryLog game table =
      tableQueryLog prover table ++ tableQueryLog verifierRun table :=
    tableQueryLog_experiment absorb scheme verifier initial statementRoots prover table
  set keys := (tableQueryLog game table).map Sigma.fst
  have consistent : ∀ entry ∈ tableQueryLog game table, entry = ⟨entry.1, table entry.1⟩ :=
    tableQueryLog_consistent table game
  have runKeys := run_table absorb scheme table (verifier claim.1) (initial claim.1)
    (statementRoots claim.1) claim.2.messages claim.2.openings
  have inKeys : ∀ entry ∈ tableQueryLog verifierRun table, entry ∈ tableQueryLog game table :=
    fun entry member => by rw [fullLog]; exact List.mem_append_right _ member
  have runInKeys : ∀ key ∈ (runTable absorb scheme table (verifier claim.1) (initial claim.1)
      (statementRoots claim.1) claim.2.messages claim.2.openings).2, key ∈ keys := by
    intro key member
    rw [← runKeys.2, List.mem_map] at member
    obtain ⟨entry, entryMember, rfl⟩ := member
    exact List.mem_map_of_mem (inKeys entry entryMember)
  have entryOf : ∀ key : JointKey E Shape Y Query, key ∈ keys →
      (⟨key, table key⟩ : (key : JointKey E Shape Y Query) × JointRange R Shape Y Query key) ∈
        tableQueryLog game table := by
    intro key member
    obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
    rw [← consistent entry entryMember]
    exact entryMember
  -- A bad hash call in the record finishes the proof.
  by_cases someBad : ∃ query, (.inr query : JointKey E Shape Y Query) ∈ keys ∧
      Bad absorb words scheme game certificate.doomed verifier initial statementRoots rootBound
        (.inr query) table
  · obtain ⟨query, member, bad⟩ := someBad
    exact ⟨_, entryOf _ member, bad⟩
  have good : GoodFrom scheme rootBound table [] keys :=
    good_of_forall_not_bad scheme rootBound table [] keys fun query member _ hit =>
      someBad ⟨query, member, by simp only [List.nil_append] at hit; exact hit⟩
  have injective : MerkleTreeExtractor.ResponseInjectiveOn (hashLog table keys) := by
    simpa using responseInjective_of_good scheme rootBound table [] keys
      (fun _ member => by simp at member) good
  set extracted := scheme.extract (hashLog table keys)
  -- The event's statement and its checkpoint.
  obtain ⟨accepted, entry, entryMember, key, entryKey, falseAt⟩ := event
  change Accepted accepts (evalWithAnswerFn (QueryImpl.ofFn table) verifierRun) at accepted
  change entry ∈ tableQueryLog verifierRun table at entryMember
  change falseStatement claim.1 (checkpointTables words scheme statementRoots
    (tableQueryLog prover table ++ tableQueryLog verifierRun table) key claim.1) at falseAt
  have keyRun : (.inl key : JointKey E Shape Y Query) ∈ (runTable absorb scheme table
      (verifier claim.1) (initial claim.1) (statementRoots claim.1) claim.2.messages
      claim.2.openings).2 := by
    rw [← runKeys.2]
    exact List.mem_map.mpr ⟨entry, entryMember, entryKey⟩
  have keyMember : (.inl key : JointKey E Shape Y Query) ∈ keys := runInKeys _ keyRun
  have statementTables : checkpointTables words scheme statementRoots
      (tableQueryLog prover table ++ tableQueryLog verifierRun table) key claim.1 =
      rootTables words extracted (statementRoots claim.1) := by
    unfold checkpointTables rootTables
    rw [← fullLog, hashEntries_eq table _ (fun entry member =>
      consistent entry ((beforeFirst_prefix _ _).subset member)), map_fst_beforeFirst]
    refine List.map_congr_left fun pair member => ?_
    simp only [normalized]
    rw [extract_checkpoint_eq scheme rootBound table keys good key keyMember pair.1
      (statement_mem_keyRoots (initialRoots claim.1) (statementBound claim.1)
        (runTable_history absorb scheme table _ _ _ _ _ key keyRun) member)]
  rw [statementTables] at falseAt
  -- The accepting run escapes at one of its own transcript queries.
  have agrees : ∀ shape root position opening,
      (∀ entry ∈ tableQueryLog (scheme.authenticate shape root position opening)
        (hashAnswers table), (.inr entry.1 : JointKey E Shape Y Query) ∈ keys) →
      evalWithAnswerFn (QueryImpl.ofFn (hashAnswers table))
        (scheme.authenticate shape root position opening) = true →
      extracted shape root position = some opening.value := by
    intro shape root position opening recorded authenticated
    refine scheme.opening_agrees (hashAnswers table) (hashLog table keys) shape root position
      opening injective (fun entry member => ?_) authenticated
    rw [tableQueryLog_consistent (hashAnswers table) _ entry member]
    exact mem_hashLog table (recorded entry member)
  obtain ⟨escapeKey, escapeMember, events, residual, tables, escapeShape, replayed, escapes⟩ :=
    runTable_escape absorb words scheme table extracted certificate commitReceives
      (fun shape root position value found => carries _ shape root position value found)
      keys agrees (verifier claim.1) (rootTables words extracted (statementRoots claim.1))
      (initial claim.1) (verifier claim.1) [] (initial claim.1) (statementRoots claim.1)
      claim.2.messages claim.2.openings (replay_nil ..) (by simp)
      (doomedValidator claim.1 _ falseAt) runInKeys (by rw [← runKeys.1]; exact accepted)
  -- The escaping key is bad: its checkpoint extraction agrees with the whole record's.
  have rootCount : (statementRoots claim.1).length +
      (events.filterMap Absorbed.committed).length ≤ rootBound := by
    have counted := replay_committed_le absorb words extracted (fun key => table (.inl key))
      events (verifier claim.1) _ _ _ _ (commitBound claim.1) replayed
    have := statementBound claim.1
    omega
  have escapeKeyMember : (.inl escapeKey : JointKey E Shape Y Query) ∈ keys :=
    runInKeys _ escapeMember
  have agreeAt : ∀ pair : Shape × Y,
      (pair ∈ statementRoots claim.1 ∨ Absorbed.root pair.1 pair.2 ∈ events) →
      checkpointExtract scheme game table escapeKey pair.1 pair.2 = extracted pair.1 pair.2 := by
    intro pair member
    unfold checkpointExtract
    refine extract_checkpoint_eq scheme rootBound table keys good escapeKey escapeKeyMember
      pair.1 ?_
    have rooted := mem_keyRoots escapeKey.2 (initialRoots claim.1) rootCount member
    rwa [← escapeShape] at rooted
  refine ⟨_, entryOf _ escapeKeyMember, claim.1, events, residual, tables, escapeShape, ?_,
    escapes⟩
  have sameTables : ((statementRoots claim.1).map fun pair =>
      normalized words (checkpointExtract scheme game table escapeKey) pair.1 pair.2) =
      rootTables words extracted (statementRoots claim.1) := by
    unfold rootTables
    refine List.map_congr_left fun pair member => ?_
    simp only [normalized, agreeAt pair (Or.inl member)]
  rw [sameTables]
  exact (replay_congr_extracted absorb words _ _ events _ _ _ fun shape root member =>
    agreeAt (shape, root) (Or.inr member)).trans replayed

end Trace

section Main
variable [SampleableType Y] [Fintype Y]
variable (verifier : Stmt → PIR.Proc (committed J Shape Value) A)
  (initial : Stmt → List (Absorbed E Shape Y)) (statementRoots : Stmt → List (Shape × Y))
  (prover : OracleComp (joint R Shape Y Query) (Stmt × Proof P Value Y))

omit [DecidableEq E] [DecidableEq Shape] [DecidableEq Y] [DecidableEq Query]
  [∀ key, SampleableType (R key)] [SampleableType Y] [Fintype Y] in
/-- The experiment charges the prover's cost plus the verifier's. -/
theorem experiment_costBound (cost : CostModel (joint R Shape Y Query) ENNReal)
    (proverCost verifierCost : ENNReal) (proverBound : WorstCaseCostBound prover cost proverCost)
    (verifierBound : ∀ statement (proof : Proof P Value Y), WorstCaseCostBound
      (run absorb scheme (verifier statement) (initial statement) (statementRoots statement)
        proof.messages proof.openings) cost verifierCost) :
    WorstCaseCostBound (experiment absorb scheme verifier initial statementRoots prover) cost
      (proverCost + verifierCost) := by
  unfold experiment
  refine WorstCaseCostBound.bind ((worstCaseCostBound_withQueryLog prover cost proverCost).mpr
    proverBound) fun proverRun => ?_
  rw [← add_zero verifierCost]
  exact WorstCaseCostBound.bind ((worstCaseCostBound_withQueryLog _ cost verifierCost).mpr
    (verifierBound proverRun.1.1 proverRun.1.2))
    fun _ => (worstCaseCostBound_pure _ cost (0 : ENNReal)).mpr le_rfl

omit [DecidableEq E] [DecidableEq Shape] [DecidableEq Y] [DecidableEq Query]
  [∀ key, SampleableType (R key)] [SampleableType Y] [Fintype Y] in
/-- The experiment makes at most the prover's queries plus the verifier's. -/
theorem experiment_queryBound (proverQueries verifierQueries : ℕ)
    (proverCount : IsTotalQueryBound prover proverQueries)
    (verifierCount : ∀ statement (proof : Proof P Value Y), IsTotalQueryBound
      (run absorb scheme (verifier statement) (initial statement) (statementRoots statement)
        proof.messages proof.openings) verifierQueries) :
    IsTotalQueryBound (experiment absorb scheme verifier initial statementRoots prover)
      (proverQueries + verifierQueries) := by
  unfold experiment
  rw [← add_zero verifierQueries]
  refine isTotalQueryBound_bind ((isTotalQueryBound_withQueryLog_iff prover _).mpr
    proverCount) fun proverRun => ?_
  refine isTotalQueryBound_bind ((isTotalQueryBound_withQueryLog_iff _ _).mpr
    (verifierCount proverRun.1.1 proverRun.1.2)) fun _ => ?_
  trivial

/-- Soundness of a verifier that sees roots and openings, with a charge per joint key. In the
joint experiment, the verifier accepts while the statement is false for its tables extracted at
the checkpoint of one of its transcript queries with probability at most the prover's charge plus
the verifier's, where a transcript key is charged the error of its occurrence in the ideal
reading's typed certificate and a hash call `targetBound / |Y|`. -/
theorem soundness_weighted {accepts : A → Prop} {error : E → ENNReal}
    (certificate : Typed.Certificate absorb accepts error)
    (commitReceives : ∀ shape, ∃ event recover, absorb (words.word shape) = .receive event recover)
    (carries : ∀ log shape root position value, scheme.extract log shape root position = some value →
      normalized words (scheme.extract log) shape root position = some value)
    (determined : Typed.Determined initial)
    (initialRoots : ∀ statement,
      (initial statement).filterMap Absorbed.committed = statementRoots statement)
    (rootBound : ℕ)
    (statementBound : ∀ statement, (statementRoots statement).length ≤ rootBound)
    (commitBound : ∀ statement,
      CommitBound (verifier statement) (rootBound - (statementRoots statement).length))
    (falseStatement : Stmt → List (Table Value) → Prop)
    (doomedValidator : ∀ statement tables, falseStatement statement tables →
      certificate.doomed (withTables words tables (verifier statement)))
    (targetBound : ℕ)
    (targetsBounded : ∀ table : JointTable R Shape Y Query,
      (targets scheme rootBound table ((tableQueryLog
        (experiment absorb scheme verifier initial statementRoots prover) table).map
          Sigma.fst)).length ≤ targetBound)
    (proverCost verifierCost : ENNReal)
    (proverBound : WorstCaseCostBound prover
      ⟨jointError error ((targetBound : ENNReal) / Fintype.card Y)⟩ proverCost)
    (verifierBound : ∀ statement (proof : Proof P Value Y), WorstCaseCostBound
      (run absorb scheme (verifier statement) (initial statement) (statementRoots statement)
        proof.messages proof.openings)
      ⟨jointError error ((targetBound : ENNReal) / Fintype.card Y)⟩ verifierCost) :
    Pr{let result ← (simulateQ randomOracle
        (experiment absorb scheme verifier initial statementRoots prover)).run' ∅}[
      FalseAcceptance words scheme statementRoots falseStatement accepts result] ≤
      proverCost + verifierCost :=
  prEvent_randomOracle_le_of_bad_queries_weighted
    (experiment absorb scheme verifier initial statementRoots prover)
    (jointError error ((targetBound : ENNReal) / Fintype.card Y)) (proverCost + verifierCost)
    (experiment_costBound absorb scheme verifier initial statementRoots prover _ proverCost
      verifierCost proverBound verifierBound)
    (FalseAcceptance words scheme statementRoots falseStatement accepts)
    (Bad absorb words scheme (experiment absorb scheme verifier initial statementRoots prover)
      certificate.doomed verifier initial statementRoots rootBound)
    (by
      intro key table
      cases key with
      | inl key =>
          exact bad_transcript_resample absorb words scheme certificate _ verifier initial
            determined statementRoots rootBound key table
      | inr query =>
          exact bad_hash_resample absorb words scheme _ certificate.doomed verifier initial
            statementRoots rootBound targetBound targetsBounded query table)
    (fun table event => trace absorb words scheme verifier initial statementRoots prover
      certificate commitReceives carries initialRoots rootBound statementBound commitBound
      falseStatement doomedValidator table event)

/-- Soundness of a verifier that sees roots and openings, with the hash charge computed from
query counts: every hash call is charged `(rootBound + inputBound + 1) · (proverQueries +
verifierQueries) / |Y|`, where `inputBound` bounds the input labels of one hash call. -/
theorem soundness {accepts : A → Prop} {error : E → ENNReal}
    (certificate : Typed.Certificate absorb accepts error)
    (commitReceives : ∀ shape, ∃ event recover, absorb (words.word shape) = .receive event recover)
    (carries : ∀ log shape root position value, scheme.extract log shape root position = some value →
      normalized words (scheme.extract log) shape root position = some value)
    (determined : Typed.Determined initial)
    (initialRoots : ∀ statement,
      (initial statement).filterMap Absorbed.committed = statementRoots statement)
    (rootBound : ℕ)
    (statementBound : ∀ statement, (statementRoots statement).length ≤ rootBound)
    (commitBound : ∀ statement,
      CommitBound (verifier statement) (rootBound - (statementRoots statement).length))
    (falseStatement : Stmt → List (Table Value) → Prop)
    (doomedValidator : ∀ statement tables, falseStatement statement tables →
      certificate.doomed (withTables words tables (verifier statement)))
    (inputBound : ℕ) (inputs : ∀ query, (scheme.inputs query).length ≤ inputBound)
    (proverQueries verifierQueries : ℕ) (proverCount : IsTotalQueryBound prover proverQueries)
    (verifierCount : ∀ statement (proof : Proof P Value Y), IsTotalQueryBound
      (run absorb scheme (verifier statement) (initial statement) (statementRoots statement)
        proof.messages proof.openings) verifierQueries)
    (proverCost verifierCost : ENNReal)
    (proverBound : WorstCaseCostBound prover
      ⟨jointError error ((((rootBound + inputBound + 1) * (proverQueries + verifierQueries) : ℕ) :
        ENNReal) / Fintype.card Y)⟩ proverCost)
    (verifierBound : ∀ statement (proof : Proof P Value Y), WorstCaseCostBound
      (run absorb scheme (verifier statement) (initial statement) (statementRoots statement)
        proof.messages proof.openings)
      ⟨jointError error ((((rootBound + inputBound + 1) * (proverQueries + verifierQueries) : ℕ) :
        ENNReal) / Fintype.card Y)⟩ verifierCost) :
    Pr{let result ← (simulateQ randomOracle
        (experiment absorb scheme verifier initial statementRoots prover)).run' ∅}[
      FalseAcceptance words scheme statementRoots falseStatement accepts result] ≤
      proverCost + verifierCost :=
  soundness_weighted absorb words scheme verifier initial statementRoots prover certificate
    commitReceives carries determined initialRoots rootBound statementBound commitBound
    falseStatement doomedValidator _ (fun table =>
      (targets_length_le scheme rootBound inputBound inputs table _).trans
        (Nat.mul_le_mul_left _ (by
          rw [List.length_map]
          exact tableQueryLog_length_le table _ _ (experiment_queryBound absorb scheme verifier
            initial statementRoots prover proverQueries verifierQueries proverCount
            verifierCount))))
    proverCost verifierCost proverBound verifierBound

end Main

end ZkcSecurity.Commitment
