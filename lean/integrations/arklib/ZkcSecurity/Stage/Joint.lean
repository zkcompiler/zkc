module

public import ZkcSecurity.Stage.Commitment
public import ZkcSecurity.Stage.Provider
public import ZkcSecurity.Oracle.Keys

@[expose] public section

/-! # The joint stage of a commitment and a transcript provider

A verifier that sees roots and openings, and a transcript provider that realizes the history
oracle with primitive calls, may share one primitive: the commitment's hash calls and the
provider's chain calls are then calls of the same function. This module states the contract a
composition of the two stages needs, and proves that the contract composes.

**Oracle namespaces and adversary access** (`Namespaces`). The commitment's hash calls and the
provider's chain calls are encoded as inputs of the shared primitive, which the adversary may call
on any input. Namespace separation is an obligation, not an assumption that cells are fresh: the
two encodings are jointly injective (`Namespaces.separated`), so no hash call is read as a chain
call and conversely (`Namespaces.hash_ne_chain`).

**Statement and history interpretation** (`Checkpoint`, `Contract.checkpointed`,
`Contract.implies`). A checkpoint extraction for a key reads only the log entries strictly before
the first entry that queries the key (`Checkpoint.factors`), so it is fixed before that query is
answered and frozen afterwards (`Checkpoint.frozen`). The joint game is the oracle game of a
prover experiment whose event is the checkpoint event (`Contract.checkpointed`): for one of the
verifier's transcript keys, the result is false at the key's extraction. The bridge's event is of
this form (`falseAcceptance_iff_checkpoint`, with `bridgeCheckpoint`). An intended application
event, such as acceptance of a statement that is false for the tables the prover committed to,
enters the bound only through the implication `Contract.implies` into the concrete game's
failure. The implication is a required field: the checkpoint event needs a transcript query of the
verifier and is false for a query-free verifier
(`ZkcSecurity.Stage.not_falseAcceptance_of_verifierLog_nil`).

**Adversary translation, verifier expansion, budgets and losses** (`Contract.provider`). The
provider stage is a stage relation from the joint game, in which transcript keys and hash calls
are cells of one lazily sampled oracle, to the concrete game on the primitive: it translates
adversaries, transports budgets, and its loss includes the verifier's expansion, initialization
included.

**Composition** (`Contract.relation`, `Contract.bounded`). The commitment stage, the provider
stage and the interpretation compose through `Relation.comp`: the intended event of a concrete
adversary admissible at `b` has probability at most `provider.loss b + commitment.loss
(provider.budget b)`, the commitment stage's loss evaluated at the transported budget.

**The provider frame** (`Frame`). A provider stage over the joint oracle comes from a provider
simulation whose simulator answers the commitment's hash calls from their own ideal cells and
realizes the transcript cells by the provider. `Frame` records such a simulation with the
obligations it must meet: the simulator uses the namespaces' own encodings (`passThrough`,
`separated`, `chainOnly`); a hash call's reply is its cell's answer through a fixed range
equivalence (`hashRange`, `hashAnswer`); recording a hash answer leaves the provider-state
projection unchanged (`recordHash`), and every other call reads the state only through that
projection and moves the projection as a function of it and the call's inputs (`attemptChain`,
`recordedChain`, `respondChain`, `recordTranscript`, `respondState`), so every handler step of
such a call is a function of the projection (`Frame.handle_chain`, `Frame.handle_hash`); and the
loss is charged over the joint trace and the joint budget (`joint`). A frame's contract
(`Frame.contract`) takes its namespaces from the frame, so the namespaces the contract records are
the ones the simulator uses. When the ideal failure of a mixture of provers is that of a
random-oracle experiment after drawing the prover (`oracleMixture`), the frame's simulation is a
provider stage from that experiment's oracle game (`Frame.oracleRelation`).

**Key forms.** A renaming of oracle cells is a zero-loss stage (`Relation.ofRenaming`); the
renamings between the commitment bridge's joint keys and history keys, with sampling, budget and
checkpoint transport, are in `ZkcSecurity.Commitment.HistoryKeys`.
-/

set_option autoImplicit false

namespace ZkcSecurity.Stage
open OracleComp OracleSpec ZkcSecurity.FiatShamir ZkcSecurity.Commitment

section Keys
variable {D D' α : Type} [DecidableEq D] [DecidableEq D'] {R : D → Type} {R' : D' → Type}
  [∀ key, SampleableType (R key)] [∀ key, SampleableType (R' key)]

/-- The random-oracle game of adversaries on the oracle `OracleSpec.ofFn R` that output a result,
admissible at their total query count, with the bad event `event` of the result. -/
noncomputable def keyedGame (R : D → Type) [∀ key, SampleableType (R key)] (α : Type)
    (event : α → Prop) : Game :=
  oracleGame R (OracleComp (OracleSpec.ofFn R) α) ℕ
    (fun queries adversary => IsTotalQueryBound adversary queries) (fun adversary => adversary) event

/-- A renaming of oracle cells is a zero-loss stage: an adversary on the source keys runs against
the target oracle through the renaming with the same law of results, and its query budget is
unchanged. -/
noncomputable def Relation.ofRenaming (keys : Oracle.Renaming R R') (event : α → Prop) :
    Relation (keyedGame R' α event) (keyedGame R α event) :=
  Relation.ofLe (S := keyedGame R' α event) (T := keyedGame R α event) keys.translate
    (fun queries => queries) (fun queries adversary bounded =>
      keys.translate_queryBound adversary queries bounded)
    fun _ adversary _ => le_of_eq (keys.prEvent_translate adversary event).symm

end Keys

namespace Joint

/-- The encodings of the commitment's hash calls and the provider's chain calls as inputs of the
shared primitive. Namespace separation is an obligation: the encodings are jointly injective. -/
structure Namespaces (HashCall ChainCall Input : Type) where
  hash : HashCall → Input
  chain : ChainCall → Input
  separated : Function.Injective (Sum.elim hash chain)

namespace Namespaces
variable {HashCall ChainCall Input : Type} (namespaces : Namespaces HashCall ChainCall Input)

theorem hash_injective : Function.Injective namespaces.hash :=
  fun first second same => Sum.inl_injective (@namespaces.separated (.inl first) (.inl second) same)

theorem chain_injective : Function.Injective namespaces.chain :=
  fun first second same => Sum.inr_injective (@namespaces.separated (.inr first) (.inr second) same)

/-- No hash call is encoded as a chain call. -/
theorem hash_ne_chain (call : HashCall) (other : ChainCall) :
    namespaces.hash call ≠ namespaces.chain other :=
  fun same => Sum.inl_ne_inr (@namespaces.separated (.inl call) (.inr other) same)

end Namespaces

/-- The entries of a log strictly before the first entry that queries `key`; the whole log when no
entry does. -/
def before {Key Entry : Type} (queries : Entry → Key → Bool) (key : Key) (log : List Entry) :
    List Entry :=
  log.takeWhile fun entry => !queries entry key

theorem before_append {Key Entry : Type} (queries : Entry → Key → Bool) (key : Key) :
    ∀ (log later : List Entry), (∃ entry ∈ log, queries entry key = true) →
      before queries key (log ++ later) = before queries key log
  | [], _, ⟨_, member, _⟩ => absurd member (List.not_mem_nil)
  | head :: tail, later, ⟨entry, member, hit⟩ => by
      unfold before
      rw [List.cons_append, List.takeWhile_cons, List.takeWhile_cons]
      by_cases here : queries head key = true
      · simp [here]
      · have inTail : ∃ entry ∈ tail, queries entry key = true := by
          rcases List.mem_cons.mp member with same | inTail
          · subst same
            exact absurd hit here
          · exact ⟨entry, inTail, hit⟩
        have rest := before_append queries key tail later inTail
        unfold before at rest
        simp [here, rest]

theorem before_before {Key Entry : Type} (queries : Entry → Key → Bool) (key : Key)
    (log : List Entry) : before queries key (before queries key log) = before queries key log := by
  unfold before
  induction log with
  | nil => rfl
  | cons head tail ih =>
      by_cases here : queries head key = true
      · simp [here]
      · simp [here, ih]

/-- A checkpoint extraction: the extraction for a key from a log of entries reads only the entries
strictly before the first entry that queries the key (`factors`), so it cannot depend on that
query or anything after it. -/
structure Checkpoint (Key Entry Extraction : Type) where
  queries : Entry → Key → Bool
  extract : Key → List Entry → Extraction
  factors : ∀ key log, extract key log = extract key (before queries key log)

/-- Once the key is queried, later entries leave its extraction unchanged. -/
theorem Checkpoint.frozen {Key Entry Extraction : Type} (checkpoint : Checkpoint Key Entry Extraction)
    (key : Key) (log later : List Entry) (queried : ∃ entry ∈ log, checkpoint.queries entry key = true) :
    checkpoint.extract key (log ++ later) = checkpoint.extract key log := by
  rw [checkpoint.factors key (log ++ later), checkpoint.factors key log,
    before_append _ key log later queried]

section Bridge
variable {J : PIR.Signature} {E Shape Value Query Y Stmt A P : Type} {Raw : E → Type}
  [DecidableEq E] [DecidableEq Shape] [DecidableEq Y] [DecidableEq Query]

/-- The bridge's log entries that query a transcript key. -/
def queriesKey (entry : (key : JointKey E Shape Y Query) × JointRange Raw Shape Y Query key)
    (key : TranscriptKey E Shape Y) : Bool :=
  decide (entry.1 = .inl key)

theorem beforeFirst_eq_before (key : TranscriptKey E Shape Y) :
    ∀ log : List ((key : JointKey E Shape Y Query) × JointRange Raw Shape Y Query key),
      beforeFirst (.inl key) log = before queriesKey key log
  | [] => rfl
  | head :: tail => by
      rw [beforeFirst_cons]
      unfold before
      rw [List.takeWhile_cons]
      by_cases here : head.1 = .inl key
      · simp [here, queriesKey]
      · have rest := beforeFirst_eq_before key tail
        unfold before at rest
        simp [here, queriesKey, rest]

/-- The commitment bridge's checkpoint extraction: a statement's tables extracted from the hash
calls strictly before the first query of a transcript key. -/
def bridgeCheckpoint (words : Words J Shape Value) (scheme : Extractable Shape Value Query Y)
    (statementRoots : Stmt → List (Shape × Y)) :
    Checkpoint (TranscriptKey E Shape Y)
      ((key : JointKey E Shape Y Query) × JointRange Raw Shape Y Query key)
      (Stmt → List (Table Value)) where
  queries := queriesKey
  extract key log statement := checkpointTables words scheme statementRoots log key statement
  factors key log := by
    funext statement
    simp only [checkpointTables, beforeFirst_eq_before key log,
      beforeFirst_eq_before key (before queriesKey key log), before_before]

/-- The transcript keys of a joint log. -/
def transcriptKeys (log : List ((key : JointKey E Shape Y Query) × JointRange Raw Shape Y Query key)) :
    List (TranscriptKey E Shape Y) :=
  log.filterMap fun entry =>
    match entry.1 with
    | .inl key => some key
    | .inr _ => none

omit [DecidableEq E] [DecidableEq Shape] [DecidableEq Y] [DecidableEq Query] in
theorem mem_transcriptKeys (log : List ((key : JointKey E Shape Y Query) × JointRange Raw Shape Y Query key))
    (key : TranscriptKey E Shape Y) :
    key ∈ transcriptKeys log ↔ ∃ entry ∈ log, entry.1 = .inl key := by
  unfold transcriptKeys
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨entry, member, found⟩
    refine ⟨entry, member, ?_⟩
    revert found
    rcases entry with ⟨first | _, _⟩ <;> simp
  · rintro ⟨entry, member, same⟩
    exact ⟨entry, member, by rw [same]⟩

/-- The bridge's event is its checkpoint event: the verifier accepts and the statement is false
for its tables extracted at the checkpoint of one of the verifier's transcript keys, from the
prover's and the verifier's log. -/
theorem falseAcceptance_iff_checkpoint (words : Words J Shape Value)
    (scheme : Extractable Shape Value Query Y) (statementRoots : Stmt → List (Shape × Y))
    (falseStatement : Stmt → List (Table Value) → Prop) (accepts : A → Prop)
    (result : JointRun Stmt P Value Y A (QueryLog (joint Raw Shape Y Query))) :
    FalseAcceptance words scheme statementRoots falseStatement accepts result ↔
      ∃ key ∈ transcriptKeys result.verifierLog,
        Accepted accepts result.outcome ∧ falseStatement result.statement
          ((bridgeCheckpoint words scheme statementRoots).extract key
            (result.proverLog ++ result.verifierLog) result.statement) := by
  unfold FalseAcceptance
  simp only [mem_transcriptKeys, bridgeCheckpoint]
  constructor
  · rintro ⟨accepted, entry, member, key, same, falseAt⟩
    exact ⟨key, ⟨entry, member, same⟩, accepted, falseAt⟩
  · rintro ⟨key, ⟨entry, member, same⟩, accepted, falseAt⟩
    exact ⟨accepted, entry, member, key, same, falseAt⟩

end Bridge

/-- The contract of a joint stage over the joint oracle `OracleSpec.ofFn R` to the concrete game
`Concrete`. The joint game is the oracle game of a prover experiment whose event is a checkpoint
event (`checkpointed`): the event holds exactly when, for one of the verifier's transcript keys,
the result is false at the key's checkpoint extraction from the result's log. The contract also
carries namespace separation of the shared primitive's inputs, the provider stage from the joint
game, and an intended application event of concrete adversaries with its required implication
into the concrete game's failure. -/
structure Contract {D : Type} [DecidableEq D] (R : D → Type) [∀ key, SampleableType (R key)]
    (Prover Budget Result : Type) (Concrete : Game)
    (HashCall ChainCall Input Key Entry Extraction : Type) where
  namespaces : Namespaces HashCall ChainCall Input
  checkpoint : Checkpoint Key Entry Extraction
  admissible : Budget → Prover → Prop
  experiment : Prover → OracleComp (OracleSpec.ofFn R) Result
  event : Result → Prop
  /-- The verifier's transcript keys in a result. -/
  verifierKeys : Result → List Key
  /-- The log a result's checkpoints are extracted from. -/
  log : Result → List Entry
  /-- The result is false at an extraction. -/
  falseAt : Result → Extraction → Prop
  checkpointed : ∀ result, event result ↔
    ∃ key ∈ verifierKeys result, falseAt result (checkpoint.extract key (log result))
  /-- The provider stage: adversary translation, transported budgets, and the loss with the
  verifier's expansion, initialization included. -/
  provider : Relation (oracleGame R Prover Budget admissible experiment event) Concrete
  /-- The probability of the intended application event for each concrete adversary. -/
  intended : Concrete.Adversary → ENNReal
  /-- The intended event implies the concrete game's failure. -/
  implies : ∀ adversary, intended adversary ≤ Concrete.bad adversary

namespace Contract
variable {D : Type} [DecidableEq D] {R : D → Type} [∀ key, SampleableType (R key)]
  {Prover Budget Result : Type} {Concrete : Game}
  {HashCall ChainCall Input Key Entry Extraction : Type}
  (contract : Contract R Prover Budget Result Concrete HashCall ChainCall Input Key Entry Extraction)

/-- The joint game: the oracle game of the contract's experiment and checkpoint event. -/
noncomputable def jointGame : Game :=
  oracleGame R Prover Budget contract.admissible contract.experiment contract.event

/-- The concrete game with the intended application event as its bad event. -/
def intendedGame : Game where
  Adversary := Concrete.Adversary
  Budget := Concrete.Budget
  Admissible := Concrete.Admissible
  bad := contract.intended

/-- The implication of the concrete failure by the intended event, as a zero-loss stage. -/
def interpretation : Relation Concrete contract.intendedGame :=
  Relation.ofLe (S := Concrete) (T := contract.intendedGame) (fun adversary => adversary)
    (fun budget => budget) (fun _ _ holds => holds) fun _ adversary _ => contract.implies adversary

/-- The commitment stage, the provider stage and the interpretation, composed. -/
noncomputable def relation (commitment : Relation Game.trivial contract.jointGame) :
    Relation Game.trivial contract.intendedGame :=
  (commitment.comp contract.provider).comp contract.interpretation

/-- The composed loss is the provider's loss plus the commitment stage's loss at the transported
budget. -/
theorem relation_loss (commitment : Relation Game.trivial contract.jointGame)
    (budget : Concrete.Budget) :
    (contract.relation commitment).loss budget =
      contract.provider.loss budget + commitment.loss (contract.provider.budget budget) := by
  exact zero_add _

/-- The intended event of a concrete adversary admissible at `b` has probability at most the
provider's loss at `b` plus the commitment stage's loss at the transported budget. -/
theorem bounded (commitment : Relation Game.trivial contract.jointGame) :
    contract.intendedGame.Bounded fun budget =>
      contract.provider.loss budget + commitment.loss (contract.provider.budget budget) := by
  intro budget adversary holds
  exact ((contract.relation commitment).bounded budget adversary holds).trans
    (le_of_eq (relation_loss contract commitment budget))

end Contract

section Frame
variable {ι TranscriptKey HashCall ChainCall Family ExecBound α β : Type} [DecidableEq Family]
  [Fintype Family] {primitive : OracleSpec ι} {family : ι → Family}
  {R : TranscriptKey ⊕ HashCall → Type}
  {concreteFailure : OracleComp primitive α → ExecBound → ENNReal}

/-- A provider simulation over a joint oracle of transcript cells and hash cells, with the
obligations of the frame.

* **Namespaces.** The primitive's inputs encode the commitment's hash calls and the provider's
  chain calls with jointly injective encodings (`namespaces`), and these are the encodings the
  simulator uses: every hash call belongs to its own ideal cell in every state (`passThrough`),
  only that call realizes the cell (`separated`), and only chain calls realize transcript cells
  (`chainOnly`).
* **Hash answers.** A hash call's reply is its ideal cell's answer read through a fixed range
  equivalence (`hashRange`, `hashAnswer`).
* **State separation.** The simulator's state has a provider-state projection (`chainState`).
  Recording a hash answer leaves it unchanged (`recordHash`). Every call that is not a hash call
  reads the state only through it: the attempt it belongs to (`attemptChain`), the recorded
  answer of a transcript cell (`recordedChain`) and a private reply (`respondChain`). Every such
  call also moves it as a function of it and the call's own inputs: the projection after recording
  a transcript answer (`recordTranscript`) and after a private reply (`respondState`). Together
  these make each handler step of a call that is not a hash call, answer and successor
  projection, a function of the projection (`handle_chain`), and each hash call's step leave the
  projection unchanged (`handle_hash`): no hash answer becomes provider state, now or at a later
  call.
* **Joint loss.** The loss is charged over the joint trace and the joint budget: every call to the
  shared primitive, the adversary's in every family and the verifier's expansion, counts towards
  one total (`joint`). -/
structure Frame (primitive : OracleSpec ι) (family : ι → Family) (R : TranscriptKey ⊕ HashCall → Type)
    (ChainCall : Type) (concreteFailure : OracleComp primitive α → ExecBound → ENNReal)
    (idealFailure : ProbComp (OracleComp (OracleSpec.ofFn R) α) → ExecBound → ENNReal) where
  simulation : Provider.Simulation primitive family R concreteFailure idealFailure
  namespaces : Namespaces HashCall ChainCall ι
  passThrough : ∀ budget state call,
    (simulation.simulator budget).attempt state (namespaces.hash call) = some (.inr call)
  separated : ∀ budget state query call,
    (simulation.simulator budget).attempt state query = some (.inr call) →
      query = namespaces.hash call
  chainOnly : ∀ budget state query key,
    (simulation.simulator budget).attempt state query = some (.inl key) →
      ∃ chain, query = namespaces.chain chain
  hashRange : (call : HashCall) → R (.inr call) ≃ primitive.Range (namespaces.hash call)
  hashAnswer : ∀ budget call ideal,
    (simulation.simulator budget).shared (namespaces.hash call) (.inr call) ideal =
      hashRange call ideal
  ChainState : Provider.Budget Family → Type
  chainState : (budget : Provider.Budget Family) → (simulation.simulator budget).State →
    ChainState budget
  recordHash : ∀ budget state call ideal,
    chainState budget ((simulation.simulator budget).record state (.inr call) ideal) =
      chainState budget state
  attemptChain : ∀ budget state other query, chainState budget state = chainState budget other →
    (∀ call, query ≠ namespaces.hash call) →
      (simulation.simulator budget).attempt state query =
        (simulation.simulator budget).attempt other query
  recordedChain : ∀ budget state other key, chainState budget state = chainState budget other →
    (simulation.simulator budget).recorded state (.inl key) =
      (simulation.simulator budget).recorded other (.inl key)
  recordTranscript : ∀ budget state other key ideal,
    chainState budget state = chainState budget other →
      chainState budget ((simulation.simulator budget).record state (.inl key) ideal) =
        chainState budget ((simulation.simulator budget).record other (.inl key) ideal)
  respondChain : ∀ budget state other query, chainState budget state = chainState budget other →
    ((simulation.simulator budget).respond state query).1 =
      ((simulation.simulator budget).respond other query).1
  respondState : ∀ budget state other query, chainState budget state = chainState budget other →
    chainState budget ((simulation.simulator budget).respond state query).2 =
      chainState budget ((simulation.simulator budget).respond other query).2
  jointLoss : ℕ → ENNReal
  joint : ∀ budget expansion,
    simulation.queryCost.loss budget expansion ≤ jointLoss ((∑ each, budget each) + expansion)

variable {idealFailure : ProbComp (OracleComp (OracleSpec.ofFn R) α) → ExecBound → ENNReal}

/-- A hash call's handler step leaves the provider-state projection unchanged in every outcome,
whether the call's answer was recorded or is asked now. -/
theorem Frame.handle_hash (frame : Frame primitive family R ChainCall concreteFailure idealFailure)
    (budget : Provider.Budget Family) (call : HashCall) (state : (frame.simulation.simulator budget).State) :
    ∀ result ∈ support (((frame.simulation.simulator budget).handle
        (frame.namespaces.hash call)).run state),
      frame.chainState budget result.2 = frame.chainState budget state := by
  have assigned := frame.passThrough budget state call
  cases recorded : (frame.simulation.simulator budget).recorded state (.inr call) with
  | some ideal =>
      rw [(frame.simulation.simulator budget).handle_recorded assigned recorded]
      intro result member
      rw [support_pure, Set.mem_singleton_iff] at member
      rw [member]
  | none =>
      rw [(frame.simulation.simulator budget).handle_fresh assigned recorded]
      intro result member
      rw [support_map] at member
      obtain ⟨ideal, -, rfl⟩ := member
      exact frame.recordHash budget state call ideal

/-- The handler step of a call that is not a hash call is a function of the provider-state
projection: from two states with the same projection the call's answer and successor projection
have the same distribution. With `Frame.handle_hash`, no hash answer reaches provider state at
this call or any later one. -/
theorem Frame.handle_chain (frame : Frame primitive family R ChainCall concreteFailure idealFailure)
    (budget : Provider.Budget Family) {state other : (frame.simulation.simulator budget).State}
    {query : ι} (same : frame.chainState budget state = frame.chainState budget other)
    (notHash : ∀ call, query ≠ frame.namespaces.hash call) :
    (fun result => (result.1, frame.chainState budget result.2)) <$>
        ((frame.simulation.simulator budget).handle query).run state =
      (fun result => (result.1, frame.chainState budget result.2)) <$>
        ((frame.simulation.simulator budget).handle query).run other := by
  have attempt := frame.attemptChain budget state other query same notHash
  cases assigned : (frame.simulation.simulator budget).attempt other query with
  | none =>
      rw [(frame.simulation.simulator budget).handle_private (attempt.trans assigned),
        (frame.simulation.simulator budget).handle_private assigned, map_pure, map_pure,
        frame.respondChain budget state other query same,
        frame.respondState budget state other query same]
  | some key =>
      cases key with
      | inr call => exact absurd (frame.separated budget other query call assigned) (notHash call)
      | inl key =>
          have recorded := frame.recordedChain budget state other key same
          cases fresh : (frame.simulation.simulator budget).recorded other (.inl key) with
          | some ideal =>
              rw [(frame.simulation.simulator budget).handle_recorded (attempt.trans assigned)
                  (recorded.trans fresh),
                (frame.simulation.simulator budget).handle_recorded assigned fresh, map_pure,
                map_pure, same]
          | none =>
              rw [(frame.simulation.simulator budget).handle_fresh (attempt.trans assigned)
                  (recorded.trans fresh),
                (frame.simulation.simulator budget).handle_fresh assigned fresh]
              simp only [Functor.map_map,
                fun ideal => frame.recordTranscript budget state other key ideal same]

/-- The frame's simulation as a provider stage at one execution bound. -/
noncomputable def Frame.toRelation
    (frame : Frame primitive family R ChainCall concreteFailure idealFailure) (executions : ExecBound)
    (mixes : Provider.Mixes idealFailure executions) :
    Relation (Provider.idealGame R idealFailure executions)
      (Provider.concreteGame primitive family concreteFailure executions) :=
  frame.simulation.toRelation executions mixes

variable [DecidableEq TranscriptKey] [DecidableEq HashCall] [∀ key, SampleableType (R key)]

/-- The failure of a mixture of provers in a random-oracle experiment: draw the prover, then run
its experiment against the lazily sampled oracle from the empty cache. -/
noncomputable def oracleMixture (experiment : OracleComp (OracleSpec.ofFn R) α →
      OracleComp (OracleSpec.ofFn R) β) (event : β → Prop)
    (provers : ProbComp (OracleComp (OracleSpec.ofFn R) α)) : ENNReal :=
  Pr{let prover ← provers; let result ← (simulateQ randomOracle (experiment prover)).run' ∅}[
    event result]

/-- The failure of a mixture is at most that of its worst prover. -/
theorem oracleMixture_mixes (experiment : OracleComp (OracleSpec.ofFn R) α →
      OracleComp (OracleSpec.ofFn R) β) (event : β → Prop) (executions : ExecBound) :
    Provider.Mixes (fun provers (_ : ExecBound) => oracleMixture experiment event provers)
      executions := by
  intro provers
  have bound := prEvent_bind_le_of_forall_le_of_support provers
    (fun prover => (simulateQ randomOracle (experiment prover)).run' ∅) event
    (ε := ⨆ prover ∈ support provers, oracleMixture experiment event (pure prover))
    fun prover member => le_trans (le_of_eq (by simp only [oracleMixture, pure_bind]))
      (le_iSup₂ (f := fun prover (_ : prover ∈ support provers) =>
        oracleMixture experiment event (pure prover)) prover member)
  simpa only [oracleMixture, bind_assoc] using bound

/-- With the ideal failure of an oracle experiment's mixtures, the frame's simulation is a
provider stage from the oracle game of that experiment, at one execution bound. -/
noncomputable def Frame.oracleRelation
    (experiment : OracleComp (OracleSpec.ofFn R) α → OracleComp (OracleSpec.ofFn R) β)
    (event : β → Prop)
    (frame : Frame primitive family R ChainCall concreteFailure
      (fun provers _ => oracleMixture experiment event provers))
    (executions : ExecBound) :
    Relation (oracleGame R (OracleComp (OracleSpec.ofFn R) α) ℕ
        (fun queries prover => IsTotalQueryBound prover queries) experiment event)
      (Provider.concreteGame primitive family concreteFailure executions) :=
  (Relation.ofLe (S := oracleGame R (OracleComp (OracleSpec.ofFn R) α) ℕ
      (fun queries prover => IsTotalQueryBound prover queries) experiment event)
    (T := Provider.idealGame R (fun provers _ => oracleMixture experiment event provers) executions)
    (fun prover => prover) (fun queries => queries) (fun _ _ holds => holds)
    fun _ prover _ => le_of_eq (by simp only [Provider.idealGame, oracleMixture]; rfl)).comp
    (frame.toRelation executions (oracleMixture_mixes experiment event executions))

/-- The contract of a frame: its namespaces are the frame's own, and its provider stage is the
frame's simulation from the oracle game of the experiment whose mixtures give the ideal
failure. -/
noncomputable def Frame.contract {Key Entry Extraction : Type}
    (experiment : OracleComp (OracleSpec.ofFn R) α → OracleComp (OracleSpec.ofFn R) β)
    (event : β → Prop)
    (frame : Frame primitive family R ChainCall concreteFailure
      (fun provers _ => oracleMixture experiment event provers))
    (checkpoint : Checkpoint Key Entry Extraction) (verifierKeys : β → List Key)
    (log : β → List Entry) (falseAt : β → Extraction → Prop)
    (checkpointed : ∀ result, event result ↔
      ∃ key ∈ verifierKeys result, falseAt result (checkpoint.extract key (log result)))
    (executions : ExecBound) (intended : OracleComp primitive α → ENNReal)
    (implies : ∀ adversary, intended adversary ≤ concreteFailure adversary executions) :
    Contract R (OracleComp (OracleSpec.ofFn R) α) ℕ β
      (Provider.concreteGame primitive family concreteFailure executions) HashCall ChainCall ι
      Key Entry Extraction where
  namespaces := frame.namespaces
  checkpoint := checkpoint
  admissible queries prover := IsTotalQueryBound prover queries
  experiment := experiment
  event := event
  verifierKeys := verifierKeys
  log := log
  falseAt := falseAt
  checkpointed := checkpointed
  provider := frame.oracleRelation experiment event executions
  intended := intended
  implies := implies

end Frame

end Joint

end ZkcSecurity.Stage
