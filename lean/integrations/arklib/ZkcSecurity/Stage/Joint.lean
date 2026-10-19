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

**Statement and history interpretation** (`Checkpoint`, `Contract.implies`). The commitment
stage bounds a checkpoint event: the statement is read through the extraction from the hash calls
before the first query of one of the verifier's transcript keys, and that extraction is frozen
once the key is queried (`Checkpoint.frozen`; the bridge's extraction satisfies it,
`bridgeCheckpoint`). An intended application event, such as acceptance of a statement that is
false for the tables the prover committed to, enters the bound only through the implication
`Contract.implies`. The implication is a required field: the checkpoint event needs a transcript
query of the verifier and is false for a query-free verifier
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
obligations under which it is expected to hold: pass-through hash calls answered from their own
cells (`Frame.passThrough`); tag separation, no other call realizing a hash cell
(`Frame.separated`); and the loss charged over the joint trace and the joint budget, every call to
the shared primitive counting towards one total (`Frame.joint`). The frame is not constructed here
for any provider; a joint provider theorem has to establish these fields. The remaining
obligation, transport between the commitment's pair keys and the provider's history keys, is a
zero-loss stage for every renaming of oracle cells (`Relation.ofRenaming`, with
`ZkcSecurity.Oracle.pairToHistory` and `ZkcSecurity.Oracle.historyToPair`). When the ideal failure
of a mixture of provers is that of a random-oracle experiment after drawing the prover
(`oracleMixture`), the frame's simulation is a provider stage from that experiment's oracle game
(`Frame.oracleRelation`).
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

/-- A checkpoint extraction: the extraction for a key from a log of entries, frozen once an entry
of the log queries the key. -/
structure Checkpoint (Key Entry Extraction : Type) where
  queries : Entry → Key → Prop
  extract : Key → List Entry → Extraction
  frozen : ∀ key log later, (∃ entry ∈ log, queries entry key) →
    extract key (log ++ later) = extract key log

section Bridge
variable {J : PIR.Signature} {E Shape Value Query Y Stmt : Type} {Raw : E → Type}
  [DecidableEq E] [DecidableEq Shape] [DecidableEq Y] [DecidableEq Query]

/-- The commitment bridge's checkpoint extraction: a statement's tables extracted from the hash
calls before the first query of a transcript key. -/
def bridgeCheckpoint (words : Words J Shape Value) (scheme : Extractable Shape Value Query Y)
    (statementRoots : Stmt → List (Shape × Y)) :
    Checkpoint (TranscriptKey E Shape Y)
      ((key : JointKey E Shape Y Query) × JointRange Raw Shape Y Query key)
      (Stmt → List (Table Value)) where
  queries entry key := entry.1 = .inl key
  extract key log statement := checkpointTables words scheme statementRoots log key statement
  frozen key log later queried := funext fun statement =>
    checkpointTables_append words scheme statementRoots log later key statement queried

end Bridge

/-- The contract of a joint stage from the joint game `Joint` to the concrete game `Concrete`:
namespace separation of the shared primitive's inputs, the checkpoint extraction, the provider
stage, and an intended application event of concrete adversaries with its required implication
into the concrete game's checkpoint event. -/
structure Contract (Joint Concrete : Game) (HashCall ChainCall Input Key Entry Extraction : Type) where
  namespaces : Namespaces HashCall ChainCall Input
  checkpoint : Checkpoint Key Entry Extraction
  /-- The provider stage: adversary translation, transported budgets, and the loss with the
  verifier's expansion, initialization included. -/
  provider : Relation Joint Concrete
  /-- The probability of the intended application event for each concrete adversary. -/
  intended : Concrete.Adversary → ENNReal
  /-- The intended event implies the checkpoint event the stages bound. -/
  implies : ∀ adversary, intended adversary ≤ Concrete.bad adversary

namespace Contract
variable {Joint Concrete : Game} {HashCall ChainCall Input Key Entry Extraction : Type}
  (contract : Contract Joint Concrete HashCall ChainCall Input Key Entry Extraction)

/-- The concrete game with the intended application event as its bad event. -/
def intendedGame : Game where
  Adversary := Concrete.Adversary
  Budget := Concrete.Budget
  Admissible := Concrete.Admissible
  bad := contract.intended

/-- The implication of the checkpoint event by the intended event, as a zero-loss stage. -/
def interpretation : Relation Concrete contract.intendedGame :=
  Relation.ofLe (S := Concrete) (T := contract.intendedGame) (fun adversary => adversary)
    (fun budget => budget) (fun _ _ holds => holds) fun _ adversary _ => contract.implies adversary

/-- The commitment stage, the provider stage and the interpretation, composed. -/
def relation (commitment : Relation Game.trivial Joint) : Relation Game.trivial contract.intendedGame :=
  (commitment.comp contract.provider).comp contract.interpretation

/-- The composed loss is the provider's loss plus the commitment stage's loss at the transported
budget. -/
theorem relation_loss (commitment : Relation Game.trivial Joint) (budget : Concrete.Budget) :
    (contract.relation commitment).loss budget =
      contract.provider.loss budget + commitment.loss (contract.provider.budget budget) := by
  exact zero_add _

/-- The intended event of a concrete adversary admissible at `b` has probability at most the
provider's loss at `b` plus the commitment stage's loss at the transported budget. -/
theorem bounded (commitment : Relation Game.trivial Joint) :
    contract.intendedGame.Bounded fun budget =>
      contract.provider.loss budget + commitment.loss (contract.provider.budget budget) := by
  intro budget adversary holds
  exact ((contract.relation commitment).bounded budget adversary holds).trans
    (le_of_eq (relation_loss contract commitment budget))

end Contract

section Frame
variable {ι TranscriptKey HashCall Family ExecBound α β : Type} [DecidableEq Family] [Fintype Family]
  {primitive : OracleSpec ι} {family : ι → Family} {R : TranscriptKey ⊕ HashCall → Type}
  {concreteFailure : OracleComp primitive α → ExecBound → ENNReal}

/-- A provider simulation over a joint oracle of transcript cells and hash cells, with the
obligations of the frame: every hash call is answered from its own ideal cell, no other call
realizes a hash cell, and the loss is charged over the joint trace and the joint budget. -/
structure Frame (primitive : OracleSpec ι) (family : ι → Family) (R : TranscriptKey ⊕ HashCall → Type)
    (concreteFailure : OracleComp primitive α → ExecBound → ENNReal)
    (idealFailure : ProbComp (OracleComp (OracleSpec.ofFn R) α) → ExecBound → ENNReal) where
  simulation : Provider.Simulation primitive family R concreteFailure idealFailure
  /-- The primitive call of each hash call. -/
  hashCall : HashCall → ι
  /-- Pass-through: a hash call belongs to its own ideal cell in every state. -/
  passThrough : ∀ budget state call,
    (simulation.simulator budget).attempt state (hashCall call) = some (.inr call)
  /-- Tag separation: a call that realizes a hash cell is that hash call, so no chain call is
  answered from a hash cell and no hash answer becomes a chain state. -/
  separated : ∀ budget state query call,
    (simulation.simulator budget).attempt state query = some (.inr call) → query = hashCall call
  /-- The loss as a function of the joint trace: all calls to the shared primitive, the
  adversary's in every family and the verifier's expansion, counted together. -/
  jointLoss : ℕ → ENNReal
  joint : ∀ budget expansion,
    simulation.queryCost.loss budget expansion ≤ jointLoss ((∑ each, budget each) + expansion)

variable {idealFailure : ProbComp (OracleComp (OracleSpec.ofFn R) α) → ExecBound → ENNReal}

/-- The frame's simulation as a provider stage at one execution bound. -/
noncomputable def Frame.toRelation
    (frame : Frame primitive family R concreteFailure idealFailure) (executions : ExecBound)
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
    (frame : Frame primitive family R concreteFailure
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

end Frame

end Joint

end ZkcSecurity.Stage
