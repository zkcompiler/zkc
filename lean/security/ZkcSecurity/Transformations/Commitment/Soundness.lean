module

public import ZkcSecurity.Transformations.Commitment.Escape

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

The proof is one application of the keyed endpoint
(`ZkcSecurity.FiatShamir.KeyedCertificate.soundness`, VCVio's weighted bad-query bound) to the
keyed certificate of the joint experiment (`keyed`): `bad_transcript_resample_charged` and
`bad_hash_resampleAt` bound the resampling of each key, and `traceAt` shows that a false
acceptance queries a bad key.

**Charged certificates.** `soundness_charged` takes a charged certificate of the ideal reading,
whose doomed set and charge are indexed by the ideal reading's absorbed history. That history
contains tables where the concrete history contains roots: an `IdealHistory` reads a concrete
history through an extraction, and the premise `CommitDoomed` keeps the doomed set across a
commitment. A transcript key is charged a concrete-key charge that dominates the ideal charge at
the key's history read through every extraction (`dominates`); since the checkpoint extraction is
fixed before the key's answer, resampling the answer stays bounded by the charge at the frozen
extraction, the all-table resampling bound of the per-event case. `soundness_weighted` is its case
for a per-event certificate, whose doomed set ignores the history (`IdealHistory.events`).
-/

set_option autoImplicit false

namespace ZkcSecurity.Commitment

open OracleComp OracleSpec ZkcSecurity.FiatShamir

variable {J : PIR.Signature} {E P Shape Value Query Y A Stmt : Type} {Raw : E → Type}
variable [DecidableEq E] [DecidableEq Shape] [DecidableEq Y] [DecidableEq Query]
variable [∀ key, SampleableType (Raw key)]
variable (absorb : Typed.Interface J E P Raw) (words : Words J Shape Value)
  (scheme : Extractable Shape Value Query Y)

/-- Resampling a transcript key's answer makes it bad with probability at most its concrete-key
charge: its checkpoint extraction, the replay before it and the ideal history read through that
extraction are fixed before the answer, and the concrete-key charge dominates the ideal charge at
the key's history read through every extraction. -/
theorem bad_transcript_resample_charged [SampleableType Y] {accepts : A → Prop}
    {charge : List E → E → ENNReal} (certificate : Typed.ChargedCertificate absorb accepts charge)
    (ideal : IdealHistory E Shape Y Value) (concreteCharge : List (Absorbed E Shape Y) → E → ENNReal)
    (dominates : ∀ extracted history occurrence,
      charge (ideal.read extracted history) occurrence ≤ concreteCharge history occurrence)
    {α : Type} (game : OracleComp (joint Raw Shape Y Query) α)
    (verifier : Stmt → PIR.Process (committed J Shape Value) A)
    (initial : Stmt → List (Absorbed E Shape Y)) (determined : Typed.Determined initial)
    (statementRoots : Stmt → List (Shape × Y)) (bound : ℕ) (key : TranscriptKey E Shape Y)
    (table : JointTable Raw Shape Y Query) :
    Pr{let answer ← $ᵗ (JointRange Raw Shape Y Query (.inl key))}[
      BadAt absorb words scheme game certificate.doomed ideal verifier initial statementRoots bound
        (.inl key) (Function.update table (.inl key) answer)] ≤ concreteCharge key.1 key.2 := by
  have frozen : ∀ answer : JointRange Raw Shape Y Query (.inl key),
      checkpointExtract scheme game (Function.update table (.inl key) answer) key =
        checkpointExtract scheme game table key := by
    intro answer
    unfold checkpointExtract
    rw [beforeFirstKey_update, hashLog_update_inl]
  set extract := checkpointExtract scheme game table key
  have shorter : ∀ (answer : JointRange Raw Shape Y Query (.inl key)) (statement : Stmt)
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
    have reduced : ∀ answer : JointRange Raw Shape Y Query (.inl key),
        BadAt absorb words scheme game certificate.doomed ideal verifier initial statementRoots
            bound (.inl key) (Function.update table (.inl key) answer) →
          EscapesAt absorb words certificate.doomed residual tables (ideal.read extract key.1)
            key.2 answer := by
      intro answer bad
      obtain ⟨statement', events', residual', tables', shape', replayed', escapes⟩ := bad
      have same : statement = statement' :=
        determined _ _ events events' (shape.symm.trans shape')
      subst same
      have sameEvents : events = events' := List.append_cancel_left (shape.symm.trans shape')
      subst sameEvents
      rw [frozen, shorter answer statement events shape, replayed] at replayed'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj replayed')
      rw [frozen] at escapes
      simpa only [Function.update_self] using escapes
    exact (prEvent_mono _ _ (fun answer => EscapesAt absorb words certificate.doomed residual
      tables (ideal.read extract key.1) key.2 answer) fun answer bad => reduced answer bad).trans
      ((escapesAt_le absorb words certificate residual tables _ key.2).trans
        (dominates extract key.1 key.2))
  · have never : ∀ answer : JointRange Raw Shape Y Query (.inl key),
        ¬ BadAt absorb words scheme game certificate.doomed ideal verifier initial statementRoots
          bound (.inl key) (Function.update table (.inl key) answer) := by
      intro answer bad
      obtain ⟨statement, events, residual, tables, shape, replayed, _⟩ := bad
      rw [frozen, shorter answer statement events shape] at replayed
      exact found ⟨statement, events, residual, tables, shape, replayed⟩
    exact (prEvent_eq_zero_of_forall_not _ _ never).trans_le zero_le

/-- Resampling a transcript key's answer makes it bad with probability at most the error of its
occurrence: its checkpoint extraction and the replay before it are fixed before the answer. -/
theorem bad_transcript_resample [SampleableType Y] {accepts : A → Prop} {error : E → ENNReal}
    (certificate : Typed.Certificate absorb accepts error) {α : Type}
    (game : OracleComp (joint Raw Shape Y Query) α)
    (verifier : Stmt → PIR.Process (committed J Shape Value) A)
    (initial : Stmt → List (Absorbed E Shape Y)) (determined : Typed.Determined initial)
    (statementRoots : Stmt → List (Shape × Y)) (bound : ℕ) (key : TranscriptKey E Shape Y)
    (table : JointTable Raw Shape Y Query) :
    Pr{let answer ← $ᵗ (JointRange Raw Shape Y Query (.inl key))}[
      Bad absorb words scheme game certificate.doomed verifier initial statementRoots bound (.inl key)
        (Function.update table (.inl key) answer)] ≤ error key.2 :=
  (le_of_eq (prEvent_congr _ _ _ fun _ =>
    (badAt_const absorb words scheme game certificate.doomed IdealHistory.events verifier initial
      statementRoots bound _ _).symm)).trans
    (bad_transcript_resample_charged absorb words scheme (Typed.Certificate.charged absorb certificate)
      IdealHistory.events (fun _ event => error event) (fun _ _ _ => le_rfl) game verifier initial
      determined statementRoots bound key table)

/-- Resampling a hash call's answer makes it bad with probability at most the number of targets
over the number of hash values: the targets are fixed before the call's first query. -/
theorem bad_hash_resampleAt [SampleableType Y] [Fintype Y] {α : Type}
    (game : OracleComp (joint Raw Shape Y Query) α) (doomed : List E → PIR.Process J A → Prop)
    (ideal : IdealHistory E Shape Y Value)
    (verifier : Stmt → PIR.Process (committed J Shape Value) A)
    (initial : Stmt → List (Absorbed E Shape Y)) (statementRoots : Stmt → List (Shape × Y))
    (bound targetBound : ℕ)
    (targetsBounded : ∀ table : JointTable Raw Shape Y Query,
      (targets scheme bound table ((tableQueryLog game table).map Sigma.fst)).length ≤ targetBound)
    (query : Query) (table : JointTable Raw Shape Y Query) :
    Pr{let answer ← $ᵗ (JointRange Raw Shape Y Query (.inr query))}[
      BadAt absorb words scheme game doomed ideal verifier initial statementRoots bound (.inr query)
        (Function.update table (.inr query) answer)] ≤
      (targetBound : ENNReal) / Fintype.card Y := by
  set before := beforeFirstKey (.inr query) ((tableQueryLog game table).map Sigma.fst)
  have fixed : ∀ answer : JointRange Raw Shape Y Query (.inr query),
      BadAt absorb words scheme game doomed ideal verifier initial statementRoots bound (.inr query)
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
  calc Pr{let answer ← $ᵗ (JointRange Raw Shape Y Query (.inr query))}[
          BadAt absorb words scheme game doomed ideal verifier initial statementRoots bound (.inr query)
            (Function.update table (.inr query) answer)]
      = Pr{let answer ← $ᵗ Y}[answer ∈ targets scheme bound table before] :=
        prEvent_congr _ _ _ fun answer => fixed answer
    _ ≤ ((targets scheme bound table before).length : ENNReal) / Fintype.card Y :=
        prEvent_mem_le _
    _ ≤ (targetBound : ENNReal) / Fintype.card Y :=
        ENNReal.div_le_div_right (by exact_mod_cast length) _

section Trace
variable (verifier : Stmt → PIR.Process (committed J Shape Value) A)
  (initial : Stmt → List (Absorbed E Shape Y)) (statementRoots : Stmt → List (Shape × Y))
  (prover : OracleComp (joint Raw Shape Y Query) (Stmt × Proof P Value Y))

/-- Resampling a hash call's answer makes it bad with probability at most the number of targets
over the number of hash values: the targets are fixed before the call's first query. -/
theorem bad_hash_resample [SampleableType Y] [Fintype Y] {α : Type}
    (game : OracleComp (joint Raw Shape Y Query) α) (doomed : PIR.Process J A → Prop)
    (verifier : Stmt → PIR.Process (committed J Shape Value) A)
    (initial : Stmt → List (Absorbed E Shape Y)) (statementRoots : Stmt → List (Shape × Y))
    (bound targetBound : ℕ)
    (targetsBounded : ∀ table : JointTable Raw Shape Y Query,
      (targets scheme bound table ((tableQueryLog game table).map Sigma.fst)).length ≤ targetBound)
    (query : Query) (table : JointTable Raw Shape Y Query) :
    Pr{let answer ← $ᵗ (JointRange Raw Shape Y Query (.inr query))}[
      Bad absorb words scheme game doomed verifier initial statementRoots bound (.inr query)
        (Function.update table (.inr query) answer)] ≤
      (targetBound : ENNReal) / Fintype.card Y :=
  bad_hash_resampleAt absorb words scheme game (fun _ process => doomed process)
    IdealHistory.events verifier initial statementRoots bound targetBound targetsBounded query table

omit [DecidableEq E] [DecidableEq Shape] [DecidableEq Y] [DecidableEq Query]
  [∀ key, SampleableType (Raw key)] in
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
  [∀ key, SampleableType (Raw key)] in
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

/-- A false acceptance queries a bad key, for a charged certificate whose doomed set is indexed by
the ideal history: if no hash call is bad, the record is good, the checkpoint extractions and every
accepted opening agree with the extraction from the whole record, and the accepting run escapes the
doomed ideal reading at one of its own transcript queries, at that query's history read through
the extraction. -/
theorem traceAt {accepts : A → Prop} {charge : List E → E → ENNReal}
    (certificate : Typed.ChargedCertificate absorb accepts charge)
    (ideal : IdealHistory E Shape Y Value) (commitDoomed : CommitDoomed words ideal certificate.doomed)
    (carries : ∀ log shape root position value, scheme.extract log shape root position = some value →
      normalized words (scheme.extract log) shape root position = some value)
    (initialRoots : ∀ statement,
      (initial statement).filterMap Absorbed.committed = statementRoots statement)
    (rootBound : ℕ)
    (statementBound : ∀ statement, (statementRoots statement).length ≤ rootBound)
    (commitBound : ∀ statement,
      CommitBound (verifier statement) (rootBound - (statementRoots statement).length))
    (falseStatement : Stmt → List (Table Value) → Prop)
    (doomedValidator : ∀ statement (extracted : Shape → Y → Table Value),
      falseStatement statement (rootTables words extracted (statementRoots statement)) →
        certificate.doomed (ideal.read extracted (initial statement))
          (withTables words (rootTables words extracted (statementRoots statement))
            (verifier statement)))
    (table : JointTable Raw Shape Y Query)
    (event : FalseAcceptance words scheme statementRoots falseStatement accepts
      (evalWithAnswerFn (QueryImpl.ofFn table)
        (experiment absorb scheme verifier initial statementRoots prover))) :
    ∃ entry ∈ tableQueryLog (experiment absorb scheme verifier initial statementRoots prover) table,
      BadAt absorb words scheme (experiment absorb scheme verifier initial statementRoots prover)
        certificate.doomed ideal verifier initial statementRoots rootBound entry.1 table := by
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
      (⟨key, table key⟩ : (key : JointKey E Shape Y Query) × JointRange Raw Shape Y Query key) ∈
        tableQueryLog game table := by
    intro key member
    obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
    rw [← consistent entry entryMember]
    exact entryMember
  -- A bad hash call in the record finishes the proof.
  by_cases someBad : ∃ query, (.inr query : JointKey E Shape Y Query) ∈ keys ∧
      BadAt absorb words scheme game certificate.doomed ideal verifier initial statementRoots
        rootBound (.inr query) table
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
    runTable_escapeAt absorb words scheme table extracted certificate ideal commitDoomed
      (fun shape root position value found => carries _ shape root position value found)
      keys agrees (verifier claim.1) (rootTables words extracted (statementRoots claim.1))
      (initial claim.1) (verifier claim.1) [] (initial claim.1) (statementRoots claim.1)
      claim.2.messages claim.2.openings (replay_nil ..) (by simp)
      (doomedValidator claim.1 extracted falseAt) runInKeys (by rw [← runKeys.1]; exact accepted)
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
  refine ⟨_, entryOf _ escapeKeyMember, claim.1, events, residual, tables, escapeShape, ?_⟩
  have sameTables : ((statementRoots claim.1).map fun pair =>
      normalized words (checkpointExtract scheme game table escapeKey) pair.1 pair.2) =
      rootTables words extracted (statementRoots claim.1) := by
    unfold rootTables
    refine List.map_congr_left fun pair member => ?_
    simp only [normalized, agreeAt pair (Or.inl member)]
  rw [sameTables]
  refine ⟨(replay_congr_extracted absorb words _ _ events _ _ _ fun shape root member =>
    agreeAt (shape, root) (Or.inr member)).trans replayed, ?_⟩
  rw [ideal.read_congr (checkpointExtract scheme game table escapeKey) extracted escapeKey.1
    fun shape root member => ?_]
  · exact escapes
  · rw [escapeShape, List.mem_append] at member
    rcases member with initialMember | eventMember
    · refine agreeAt (shape, root) (Or.inl ?_)
      rw [← initialRoots claim.1]
      exact List.mem_filterMap.mpr ⟨_, initialMember, rfl⟩
    · exact agreeAt (shape, root) (Or.inr eventMember)


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
    (table : JointTable Raw Shape Y Query)
    (event : FalseAcceptance words scheme statementRoots falseStatement accepts
      (evalWithAnswerFn (QueryImpl.ofFn table)
        (experiment absorb scheme verifier initial statementRoots prover))) :
    ∃ entry ∈ tableQueryLog (experiment absorb scheme verifier initial statementRoots prover) table,
      Bad absorb words scheme (experiment absorb scheme verifier initial statementRoots prover)
        certificate.doomed verifier initial statementRoots rootBound entry.1 table := by
  obtain ⟨entry, member, bad⟩ := traceAt absorb words scheme verifier initial statementRoots prover
    (Typed.Certificate.charged absorb certificate) IdealHistory.events
    (commitDoomed_events certificate commitReceives) carries initialRoots rootBound statementBound
    commitBound falseStatement (fun statement _ falseAt => doomedValidator statement _ falseAt)
    table event
  exact ⟨entry, member, (badAt_const absorb words scheme _ certificate.doomed IdealHistory.events
    verifier initial statementRoots rootBound _ _).mp bad⟩

end Trace

section Main
variable [SampleableType Y] [Fintype Y]
variable (verifier : Stmt → PIR.Process (committed J Shape Value) A)
  (initial : Stmt → List (Absorbed E Shape Y)) (statementRoots : Stmt → List (Shape × Y))
  (prover : OracleComp (joint Raw Shape Y Query) (Stmt × Proof P Value Y))

omit [DecidableEq E] [DecidableEq Shape] [DecidableEq Y] [DecidableEq Query]
  [∀ key, SampleableType (Raw key)] [SampleableType Y] [Fintype Y] in
/-- The experiment charges the prover's cost plus the verifier's. -/
theorem experiment_costBound (cost : CostModel (joint Raw Shape Y Query) ENNReal)
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
  [∀ key, SampleableType (Raw key)] [SampleableType Y] [Fintype Y] in
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

/-- The keyed certificate of the joint experiment that a charged certificate of the ideal reading
gives: a transcript key is charged a concrete-key charge that dominates the ideal charge at the
key's history read through every extraction, a hash call `targetBound / |Y|`; a key is bad as in
`BadAt`. -/
noncomputable def keyed {accepts : A → Prop} {charge : List E → E → ENNReal}
    (certificate : Typed.ChargedCertificate absorb accepts charge)
    (ideal : IdealHistory E Shape Y Value) (commitDoomed : CommitDoomed words ideal certificate.doomed)
    (concreteCharge : List (Absorbed E Shape Y) → E → ENNReal)
    (dominates : ∀ extracted history occurrence,
      charge (ideal.read extracted history) occurrence ≤ concreteCharge history occurrence)
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
    (doomedValidator : ∀ statement (extracted : Shape → Y → Table Value),
      falseStatement statement (rootTables words extracted (statementRoots statement)) →
        certificate.doomed (ideal.read extracted (initial statement))
          (withTables words (rootTables words extracted (statementRoots statement))
            (verifier statement)))
    (targetBound : ℕ)
    (targetsBounded : ∀ table : JointTable Raw Shape Y Query,
      (targets scheme rootBound table ((tableQueryLog
        (experiment absorb scheme verifier initial statementRoots prover) table).map
          Sigma.fst)).length ≤ targetBound) :
    KeyedCertificate (JointRange Raw Shape Y Query)
      (experiment absorb scheme verifier initial statementRoots prover)
      (FalseAcceptance words scheme statementRoots falseStatement accepts) where
  charge := jointCharge concreteCharge ((targetBound : ENNReal) / Fintype.card Y)
  bad := BadAt absorb words scheme (experiment absorb scheme verifier initial statementRoots prover)
    certificate.doomed ideal verifier initial statementRoots rootBound
  resample key table := by
    cases key with
    | inl key =>
        exact bad_transcript_resample_charged absorb words scheme certificate ideal concreteCharge
          dominates _ verifier initial determined statementRoots rootBound key table
    | inr query =>
        exact bad_hash_resampleAt absorb words scheme _ certificate.doomed ideal verifier initial
          statementRoots rootBound targetBound targetsBounded query table
  trace table event := traceAt absorb words scheme verifier initial statementRoots prover certificate
    ideal commitDoomed carries initialRoots rootBound statementBound commitBound falseStatement
    doomedValidator table event

/-- Soundness of a verifier that sees roots and openings, with a charged certificate of its ideal
reading. In the joint experiment, the verifier accepts while the statement is false for its tables
extracted at the checkpoint of one of its transcript queries with probability at most the prover's
charge plus the verifier's, where a transcript key is charged a concrete-key charge that dominates
the certificate's charge at the key's history read as an ideal history through every extraction,
and a hash call `targetBound / |Y|`. The all-table resampling bound is that of the keyed
certificate (`keyed`). -/
theorem soundness_charged {accepts : A → Prop} {charge : List E → E → ENNReal}
    (certificate : Typed.ChargedCertificate absorb accepts charge)
    (ideal : IdealHistory E Shape Y Value) (commitDoomed : CommitDoomed words ideal certificate.doomed)
    (concreteCharge : List (Absorbed E Shape Y) → E → ENNReal)
    (dominates : ∀ extracted history occurrence,
      charge (ideal.read extracted history) occurrence ≤ concreteCharge history occurrence)
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
    (doomedValidator : ∀ statement (extracted : Shape → Y → Table Value),
      falseStatement statement (rootTables words extracted (statementRoots statement)) →
        certificate.doomed (ideal.read extracted (initial statement))
          (withTables words (rootTables words extracted (statementRoots statement))
            (verifier statement)))
    (targetBound : ℕ)
    (targetsBounded : ∀ table : JointTable Raw Shape Y Query,
      (targets scheme rootBound table ((tableQueryLog
        (experiment absorb scheme verifier initial statementRoots prover) table).map
          Sigma.fst)).length ≤ targetBound)
    (proverCost verifierCost : ENNReal)
    (proverBound : WorstCaseCostBound prover
      ⟨jointCharge concreteCharge ((targetBound : ENNReal) / Fintype.card Y)⟩ proverCost)
    (verifierBound : ∀ statement (proof : Proof P Value Y), WorstCaseCostBound
      (run absorb scheme (verifier statement) (initial statement) (statementRoots statement)
        proof.messages proof.openings)
      ⟨jointCharge concreteCharge ((targetBound : ENNReal) / Fintype.card Y)⟩ verifierCost) :
    Pr{let result ← (simulateQ randomOracle
        (experiment absorb scheme verifier initial statementRoots prover)).run' ∅}[
      FalseAcceptance words scheme statementRoots falseStatement accepts result] ≤
      proverCost + verifierCost :=
  (keyed absorb words scheme verifier initial statementRoots prover certificate ideal commitDoomed
    concreteCharge dominates carries determined initialRoots rootBound statementBound commitBound
    falseStatement doomedValidator targetBound targetsBounded).soundness
    (experiment_costBound absorb scheme verifier initial statementRoots prover _ proverCost
      verifierCost proverBound verifierBound)

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
    (targetsBounded : ∀ table : JointTable Raw Shape Y Query,
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
      proverCost + verifierCost := by
  rw [jointError_eq] at proverBound
  simp only [jointError_eq] at verifierBound
  exact soundness_charged absorb words scheme verifier initial statementRoots prover
    (Typed.Certificate.charged absorb certificate) IdealHistory.events
    (commitDoomed_events certificate commitReceives) (fun _ event => error event)
    (fun _ _ _ => le_rfl) carries determined initialRoots rootBound statementBound commitBound
    falseStatement (fun statement _ falseAt => doomedValidator statement _ falseAt) targetBound
    targetsBounded proverCost verifierCost proverBound verifierBound

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
