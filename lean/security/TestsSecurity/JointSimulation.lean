import TestsSecurity.StageComposition
import ZkcSecurity.Transformations.Commitment.Repeats
import ZkcTools.DeclarationAudit

/-! A constructed frame: a tagged provider for the joint oracle, composed with the committed
verifier through the joint-stage contract.

The provider's primitive is a random function on tagged inputs: a transcript key with the
transcript tag and a hash call with the hash tag (`namespaces`; here the tags are the summands of
the joint key). Its simulator (`taggedSimulator`) assigns every input to the ideal cell its tag
names and answers a repeated input from its record; a hash call is passed through to its own cell
with its answer unchanged, and the provider-state projection, the record of transcript cells, does
not see hash answers. The simulator is the memoizing front end of `ZkcSecurity.VCVio.Memo`.

The concrete experiment runs the committed verifier against the primitive. A simulation must
bound its false acceptance by that of the translated prover, whose log keeps one entry per key;
for Merkle trees with hashed leaves the extraction reads first matches, so the repeated entries
do not change the event (`ZkcSecurity.Commitment.falseAcceptance_le_memo`), and the simulation is
exact (`simulation`, loss zero, cost the total budget). Its frame (`frame`) meets every obligation
of `ZkcSecurity.Stage.Joint.Frame`, and composing it with the commitment stage through the contract
bounds the concrete false acceptance of an adversary within a per-family budget by the commitment
stage's loss at the total budget (`tagged_soundness`).

The tags here are the joint key's own summands, so the provider realizes each transcript query
by one primitive call and has no chain state to collide: the content is that the frame's fields
are satisfiable together by a constructed simulation and that the contract composes it with the
bridge. A provider that encodes tags in bytes composes with this one through
`ZkcSecurity.Stage.Relation.ofRenaming`.

The delayed-transfer controls (`transfer_no_frame`, `keptFrame`) check the frame's state
obligations: a simulator that copies a recorded hash answer into provider state at a private reply
or at recording a transcript answer meets every read obligation, yet a later private reply exposes
the hash answer, and no frame has its simulation; the same simulator without the copy has one. -/

namespace TestsSecurity.JointSimulation
open OracleComp OracleSpec
open ZkcSecurity.FiatShamir ZkcSecurity.Commitment ZkcSecurity.Stage
open ZkcSecurity.Examples.CommittedOpeningBridge
open scoped ENNReal

section Tagged
variable {D : Type} [DecidableEq D] (R : D → Type) [∀ key, SampleableType (R key)]

/-- The tagged provider's simulator: every input is assigned to its own cell, a repeated input is
answered from the record, and no input is answered privately. -/
noncomputable def taggedSimulator : Provider.Simulator (OracleSpec.ofFn R) R Unit where
  State := (OracleSpec.ofFn R).QueryCache
  start _ := ∅
  attempt _ query := some query
  recorded state key := state key
  record state key answer := state.cacheQuery key answer
  shared query key ideal := if same : key = query then same ▸ ideal else Classical.arbitrary _
  respond state _ := (Classical.arbitrary _, state)
  together := Eq
  recorded_start _ _ := rfl
  recorded_record state key answer := QueryCache.cacheQuery_self _ _ _
  recorded_record_of_ne state key other answer different :=
    QueryCache.cacheQuery_of_ne _ _ different
  recorded_respond _ _ _ := rfl
  attempt_record _ _ _ _ _ assigned := assigned
  attempt_respond _ _ _ _ assigned := assigned
  attempt_together _ _ _ same := by rw [same]

theorem taggedSimulator_shared (query : D) (ideal : R query) :
    (taggedSimulator R).shared query query ideal = ideal := by
  simp [taggedSimulator]

theorem taggedSimulator_handle :
    (taggedSimulator R).handle = ZkcSecurity.VCVio.Memo.memoImpl := by
  funext query
  apply StateT.ext
  intro state
  change (match (state : (OracleSpec.ofFn R).QueryCache).toFn query with
      | some ideal => pure ((taggedSimulator R).shared query query ideal, state)
      | none => (fun ideal => ((taggedSimulator R).shared query query ideal,
          (state : (OracleSpec.ofFn R).QueryCache).cacheQuery query ideal)) <$>
            liftM ((OracleSpec.ofFn R).query query)) =
    (match (state : (OracleSpec.ofFn R).QueryCache).toFn query with
      | some answer => pure (answer, state)
      | none => (fun answer => (answer, (state : (OracleSpec.ofFn R).QueryCache).cacheQuery query
          answer)) <$> liftM ((OracleSpec.ofFn R).query query))
  cases (state : (OracleSpec.ofFn R).QueryCache).toFn query with
  | some ideal => simp only [taggedSimulator_shared]
  | none =>
      simp only [taggedSimulator_shared]
      rfl

theorem taggedSimulator_translate {α : Type} (adversary : OracleComp (OracleSpec.ofFn R) α) :
    (taggedSimulator R).translate adversary () =
      Prod.fst <$> (simulateQ ZkcSecurity.VCVio.Memo.memoImpl adversary).run ∅ := by
  rw [Provider.Simulator.translate, taggedSimulator_handle, StateT.run'_eq]
  rfl

end Tagged

section Bridge
variable {Row Query Digest : Type} [DecidableEq Row] [DecidableEq Query] [DecidableEq Digest]
  [SampleableType Digest] [Fintype Digest]

/-- The joint answers of the committed verifier. -/
abbrev Answers (depth : ℕ) (Row Query Digest : Type) :=
  JointRange (fun _ : Event Row => Fin (2 ^ depth)) Unit Digest Query

/-- The two families of the tagged primitive: transcript inputs and hash inputs. -/
def family {Row Query Digest : Type} : JointKey (Event Row) Unit Digest Query → Bool :=
  Sum.isLeft

/-- The committed verifier's joint experiment. -/
noncomputable abbrev bridgeExperiment (model : LeafHashing Row Query Digest)
    (accepts : Row → Bool) (depth : ℕ) :=
  experiment (absorb depth) (scheme model depth) (fun _ : Digest => validator accepts depth) initial
    (fun root => [((), root)])

/-- The committed verifier's false acceptance. -/
abbrev bridgeEvent (model : LeafHashing Row Query Digest) (accepts : Row → Bool) (depth : ℕ)
    (fraction : ENNReal) (default : Row) :=
  FalseAcceptance (Raw := fun _ : Event Row => Fin (2 ^ depth)) (words depth default)
    (scheme model depth) (fun root => [((), root)]) (FalseTable accepts depth fraction default)
    (P := List Row) (A := Bool) (· = true)

/-- The concrete failure: the committed verifier's false acceptance against the tagged
primitive. -/
noncomputable def concreteFailure (model : LeafHashing Row Query Digest) (accepts : Row → Bool)
    (depth : ℕ) (fraction : ENNReal) (default : Row)
    (adversary : OracleComp (OracleSpec.ofFn (Answers depth Row Query Digest))
      (Digest × Proof (List Row) Row Digest)) (_ : Unit) : ENNReal :=
  Pr{let result ← (simulateQ randomOracle (bridgeExperiment model accepts depth adversary)).run' ∅}[
    bridgeEvent model accepts depth fraction default result]

/-- The tagged provider's simulation of the committed verifier: exact, at the total budget, with
the verifier's `depth + 2` calls as expansion. -/
noncomputable def simulation (model : LeafHashing Row Query Digest) (accepts : Row → Bool)
    (depth : ℕ) (fraction : ENNReal) (default : Row) :
    Provider.Simulation (OracleSpec.ofFn (Answers depth Row Query Digest)) family
      (Answers depth Row Query Digest) (concreteFailure model accepts depth fraction default)
      (fun provers _ => Joint.oracleMixture (bridgeExperiment model accepts depth)
        (bridgeEvent model accepts depth fraction default) provers) where
  Tape _ := Unit
  tapeSampleable _ := inferInstance
  simulator _ := taggedSimulator (Answers depth Row Query Digest)
  charged _ := True
  chargedDecidable _ := instDecidableTrue
  carries _ _ _ _ _ := trivial
  queryCost :=
    { cost budget := budget true + budget false
      monotone first second le := Nat.add_le_add (le true) (le false)
      expansion _ := depth + 2
      loss _ _ := 0 }
  covers budget := by simp [Provider.chargedBudget]
  bound adversary budget executions _ := by
    rw [add_zero]
    refine (falseAcceptance_le_memo (words depth default) (scheme model depth)
      (fun root => [((), root)]) (absorb depth)
      (Extractable.comap_firstMatch model.scheme (LeafHashing.scheme_firstMatch model) _)
      (fun _ => validator accepts depth) initial (FalseTable accepts depth fraction default)
      (· = true) adversary).trans (le_of_eq ?_)
    simp only [Joint.oracleMixture, bind_assoc, pure_bind]
    rw [← taggedSimulator_translate]
    exact (_root_.EvalDistEq.prEvent_eq
      (OracleComp.EvalDistEq.bind_const ($ᵗ Unit) _) _).symm

/-- The tags of the primitive's inputs: a transcript key and a hash call, jointly injective. -/
def namespaces {Row Query Digest : Type} :
    Joint.Namespaces Query (TranscriptKey (Event Row) Unit Digest)
      (JointKey (Event Row) Unit Digest Query) where
  hash := Sum.inr
  chain := Sum.inl
  separated first second same := by
    cases first <;> cases second <;> simp_all

/-- The tagged provider's frame: every obligation holds. -/
noncomputable def frame (model : LeafHashing Row Query Digest) (accepts : Row → Bool) (depth : ℕ)
    (fraction : ENNReal) (default : Row) :
    Joint.Frame (OracleSpec.ofFn (Answers depth Row Query Digest)) family
      (Answers depth Row Query Digest) (TranscriptKey (Event Row) Unit Digest)
      (concreteFailure model accepts depth fraction default)
      (fun provers _ => Joint.oracleMixture (bridgeExperiment model accepts depth)
        (bridgeEvent model accepts depth fraction default) provers) where
  simulation := simulation model accepts depth fraction default
  namespaces := namespaces
  passThrough _ _ _ := rfl
  separated _ _ _ _ assigned := Option.some.inj assigned
  chainOnly _ _ _ key assigned := ⟨key, Option.some.inj assigned⟩
  hashRange _ := Equiv.refl _
  hashAnswer _ call ideal := taggedSimulator_shared _ (Sum.inr call) ideal
  ChainState _ := (key : TranscriptKey (Event Row) Unit Digest) → Option (Fin (2 ^ depth))
  chainState _ state key := (state : (OracleSpec.ofFn (Answers depth Row Query Digest)).QueryCache).toFn
    (.inl key)
  recordHash _ state call ideal := by
    funext key
    exact QueryCache.cacheQuery_of_ne _ _ (by simp)
  attemptChain _ _ _ _ _ _ := rfl
  recordedChain _ _ _ key same := congrFun same key
  recordTranscript _ state other key ideal same := by
    funext entry
    by_cases equal : entry = key
    · subst equal
      exact (QueryCache.cacheQuery_self _ _ _).trans (QueryCache.cacheQuery_self _ _ _).symm
    · have different : (Sum.inl entry : JointKey (Event Row) Unit Digest Query) ≠ .inl key := by
        simpa using equal
      exact (QueryCache.cacheQuery_of_ne _ _ different).trans
        ((congrFun same entry).trans (QueryCache.cacheQuery_of_ne _ _ different).symm)
  respondChain _ _ _ _ _ := rfl
  respondState _ _ _ _ same := same
  jointLoss _ := 0
  joint _ _ := le_rfl

/-- The tagged provider composed with the committed verifier through the joint-stage contract: an
adversary within a per-family budget makes the committed verifier accept while the table extracted
at the checkpoint of its query is far with probability at most the commitment stage's loss at the
total budget. -/
theorem tagged_soundness (model : LeafHashing Row Query Digest) (accepts : Row → Bool) (depth : ℕ)
    (fraction : ENNReal) (default : Row)
    (adversary : OracleComp (OracleSpec.ofFn (Answers depth Row Query Digest))
      (Digest × Proof (List Row) Row Digest))
    (budget : Provider.Budget Bool) (within : Provider.FamilyQueryBound family adversary budget) :
    concreteFailure model accepts depth fraction default adversary () ≤
      (TestsSecurity.StageComposition.bridgeRelation model accepts depth fraction default).loss
        (budget true + budget false) := by
  have composed := TestsSecurity.StageComposition.frame_composes model accepts depth fraction
    default (frame model accepts depth fraction default) () _ (fun _ => le_rfl) adversary budget
    within
  exact composed.trans (le_of_eq (zero_add _))

end Bridge

section Transfer

/-! ### Delayed transfer

A simulator must not carry a hash answer into provider state, where a later call can expose it.
The controls here are simulators over a primitive with three inputs: a transcript call, a hash call
and a private call that belongs to no attempt. Each answers the transcript call and the hash call
from their own cells and the private call from a slot of its state. Two of them copy the recorded
hash answer into the slot at one transition: a private reply (`Transfer.respond`) or recording a
transcript answer (`Transfer.record`). With the recorded transcript answer and the slot as the
provider-state projection, every read obligation of a frame holds for them (`transfer_reads`):
recording the hash answer leaves the projection unchanged, and attempts, transcript records and
private replies read the state only through it. Yet two states with the same projection, before
and after the hash call, give different private replies after the transfer (`transfer_exposes`).
The transition obligations reject both: no frame has either simulation, whatever its projection
(`transfer_no_frame`). The third never writes the slot (`Transfer.kept`), and its simulation has
a frame at the same projection (`keptFrame`), so the rejection is the transfer's. The failure
functions are zero, since the controls concern the state obligations only. -/

/-- The inputs of the transfer controls: the transcript call `some (.inl ())`, the hash call
`some (.inr ())` and the private call `none`. -/
abbrev TransferInput := Option (Unit ⊕ Unit)

/-- The transfer controls' cells, one transcript cell and one hash cell, with Boolean answers. -/
abbrev TransferCells : Unit ⊕ Unit → Type := fun _ => Bool

/-- The transfer controls' primitive, with Boolean answers to every input. -/
abbrev transferPrimitive : OracleSpec TransferInput := OracleSpec.ofFn fun _ => Bool

/-- A transfer simulator's state: the recorded transcript answer, the recorded hash answer and the
slot the private replies read. -/
structure TransferState where
  transcript : Option Bool
  hash : Option Bool
  slot : Bool

/-- The transition at which a transfer simulator copies the recorded hash answer into its slot,
or none. -/
inductive Transfer where
  | respond
  | record
  | kept

/-- The recorded hash answer as a slot value. -/
def TransferState.copied (state : TransferState) : Bool := state.hash.getD false

/-- The transfer simulator: the transcript and hash calls belong to their own cells, the private
call is answered from the slot, and the recorded hash answer is copied into the slot at the
transition `transfer` names, if any. -/
def transferSimulator (transfer : Transfer) :
    Provider.Simulator transferPrimitive TransferCells Unit where
  State := TransferState
  start _ := ⟨none, none, false⟩
  attempt _ query := query
  recorded state key := match key with
    | .inl _ => state.transcript
    | .inr _ => state.hash
  record state key answer := match key with
    | .inl _ =>
        { state with
          transcript := some answer
          slot := match transfer with
            | .record => state.copied
            | _ => state.slot }
    | .inr _ => { state with hash := some answer }
  shared _ _ ideal := ideal
  respond state _ := (state.slot, match transfer with
    | .respond => { state with slot := state.copied }
    | _ => state)
  together := Eq
  recorded_start _ _ := by
    rename_i key
    cases key <;> rfl
  recorded_record _ key _ := by cases key <;> rfl
  recorded_record_of_ne _ key other _ different := by
    rcases key with ⟨⟩ | ⟨⟩ <;> rcases other with ⟨⟩ | ⟨⟩
    all_goals first | rfl | exact absurd rfl different
  recorded_respond _ _ key := by cases key <;> cases transfer <;> rfl
  attempt_record _ _ _ _ _ assigned := assigned
  attempt_respond _ _ _ _ assigned := assigned
  attempt_together _ _ _ same := by rw [same]

/-- The transfer controls' encodings: the hash call, and the transcript and private calls as the
provider's chain calls. -/
def transferNamespaces : Joint.Namespaces Unit (Option Unit) TransferInput where
  hash _ := some (.inr ())
  chain call := call.map fun _ => .inl ()
  separated first second same := by
    rcases first with ⟨⟩ | _ | ⟨⟩ <;> rcases second with ⟨⟩ | _ | ⟨⟩ <;> simp_all

/-- The projection the controls keep: the recorded transcript answer and the slot. -/
def transferProjection (state : TransferState) : Option Bool × Bool :=
  (state.transcript, state.slot)

/-- Every read obligation of a frame holds for a transfer simulator at `transferProjection`: the
namespaces are the ones it uses, the hash call's reply is its cell's answer, recording a hash answer
leaves the projection unchanged, and attempts, transcript records and private replies read the
state only through the projection. -/
theorem transfer_reads (transfer : Transfer) :
    (∀ state call, (transferSimulator transfer).attempt state (transferNamespaces.hash call) =
      some (.inr call)) ∧
    (∀ state query call, (transferSimulator transfer).attempt state query = some (.inr call) →
      query = transferNamespaces.hash call) ∧
    (∀ state query key, (transferSimulator transfer).attempt state query = some (.inl key) →
      ∃ chain, query = transferNamespaces.chain chain) ∧
    (∀ call ideal, (transferSimulator transfer).shared (transferNamespaces.hash call) (.inr call)
      ideal = ideal) ∧
    (∀ state call ideal, transferProjection
      ((transferSimulator transfer).record state (.inr call) ideal) = transferProjection state) ∧
    (∀ state other query, transferProjection state = transferProjection other →
      (transferSimulator transfer).attempt state query =
        (transferSimulator transfer).attempt other query) ∧
    (∀ state other key, transferProjection state = transferProjection other →
      (transferSimulator transfer).recorded state (.inl key) =
        (transferSimulator transfer).recorded other (.inl key)) ∧
    (∀ state other query, transferProjection state = transferProjection other →
      ((transferSimulator transfer).respond state query).1 =
        ((transferSimulator transfer).respond other query).1) := by
  refine ⟨fun _ _ => rfl, ?_, ?_, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl, ?_, ?_⟩
  · intro _ query call assigned
    cases call
    exact assigned
  · intro _ query key assigned
    cases key
    exact ⟨some (), assigned⟩
  · intro _ _ _ same
    exact congrArg Prod.fst same
  · intro _ _ _ same
    exact congrArg Prod.snd same

/-- The delayed transfer: recording the hash answer leaves the projection unchanged, yet after the
transfer the private reply is the hash answer, where it was the slot's starting value before. -/
theorem transfer_exposes (transfer : Transfer) (moves : transfer ≠ .kept) (answer : Bool) :
    let simulator := transferSimulator transfer
    let hashed := simulator.record (simulator.start ()) (.inr ()) answer
    let transferred := fun state : TransferState => match transfer with
      | .respond => (simulator.respond state none).2
      | _ => simulator.record state (.inl ()) false
    transferProjection hashed = transferProjection (simulator.start ()) ∧
      (simulator.respond (transferred hashed) none).1 = answer ∧
      (simulator.respond (transferred (simulator.start ())) none).1 = false := by
  cases transfer
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩
  · exact absurd rfl moves

/-- Zero concrete failure: the controls concern the state obligations only. -/
def transferFailure : OracleComp transferPrimitive Unit → Unit → ENNReal := fun _ _ => 0

/-- Zero ideal failure. -/
def transferIdealFailure :
    ProbComp (OracleComp (OracleSpec.ofFn TransferCells) Unit) → Unit → ENNReal := fun _ _ => 0

/-- A transfer simulator as a provider simulation with zero failures and zero loss. -/
noncomputable def transferSimulation (transfer : Transfer) :
    Provider.Simulation transferPrimitive (fun _ => ()) TransferCells transferFailure
      transferIdealFailure where
  Tape _ := Unit
  tapeSampleable _ := inferInstance
  simulator _ := transferSimulator transfer
  charged _ := True
  chargedDecidable _ := instDecidableTrue
  carries _ _ _ _ _ := trivial
  queryCost :=
    { cost budget := budget ()
      monotone _ _ le := le ()
      expansion _ := 0
      loss _ _ := 0 }
  covers budget := by simp [Provider.chargedBudget]
  bound _ _ _ _ := zero_le

/-- No frame has a transfer simulation, whatever its provider-state projection: recording the hash
answer must leave the projection unchanged, the transfer must then move it as a function of it,
and the next private reply must read only it, but that reply is the hash answer. -/
theorem transfer_no_frame (transfer : Transfer) (moves : transfer ≠ .kept)
    (frame : Joint.Frame transferPrimitive (fun _ => ()) TransferCells (Option Unit) transferFailure
      transferIdealFailure)
    (simulates : frame.simulation = transferSimulation transfer) : False := by
  obtain ⟨simulation, _, _, _, _, _, _, _, chainState, recordHash, _, _, recordTranscript,
    respondChain, respondState, _, _⟩ := frame
  change simulation = _ at simulates
  subst simulates
  have hashed := recordHash (fun _ => 0) (⟨none, none, false⟩ : TransferState) () true
  cases transfer with
  | respond =>
      have exposed := respondChain (fun _ => 0) _ _ none
        (respondState (fun _ => 0) _ _ none hashed)
      exact Bool.noConfusion exposed
  | record =>
      have exposed := respondChain (fun _ => 0) _ _ none
        (recordTranscript (fun _ => 0) _ _ () false hashed)
      exact Bool.noConfusion exposed
  | kept => exact moves rfl

/-- The simulator that never writes its slot has a frame at the projection the controls keep: the
transition obligations reject the transfer, not the primitive or the projection. -/
noncomputable def keptFrame :
    Joint.Frame transferPrimitive (fun _ => ()) TransferCells (Option Unit) transferFailure
      transferIdealFailure where
  simulation := transferSimulation .kept
  namespaces := transferNamespaces
  passThrough _ := (transfer_reads .kept).1
  separated _ := (transfer_reads .kept).2.1
  chainOnly _ := (transfer_reads .kept).2.2.1
  hashRange _ := Equiv.refl Bool
  hashAnswer _ := (transfer_reads .kept).2.2.2.1
  ChainState _ := Option Bool × Bool
  chainState _ := transferProjection
  recordHash _ := (transfer_reads .kept).2.2.2.2.1
  attemptChain _ state other query same _ := (transfer_reads .kept).2.2.2.2.2.1 state other query same
  recordedChain _ := (transfer_reads .kept).2.2.2.2.2.2.1
  recordTranscript _ _ _ _ ideal same := congrArg (fun projection => (some ideal, projection.2)) same
  respondChain _ := (transfer_reads .kept).2.2.2.2.2.2.2
  respondState _ _ _ _ same := same
  jointLoss _ := 0
  joint _ _ := le_rfl

end Transfer

end TestsSecurity.JointSimulation

run_cmd ZkcTools.DeclarationAudit.checkCurrent "JOINT-SIMULATION-AXIOM-PASS"
