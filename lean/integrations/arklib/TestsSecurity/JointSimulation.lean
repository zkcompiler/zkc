import TestsSecurity.StageComposition
import ZkcSecurity.Commitment.Repeats
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
`ZkcSecurity.Stage.Relation.ofRenaming`. -/

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
    exact (ZkcSecurity.VCVio.Deferral.prEvent_eq_of_evalSPMF_eq
      (ZkcSecurity.VCVio.Deferral.evalSPMF_uniform_drop (A := Unit) _) _).symm

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
  respondChain _ _ _ _ _ := rfl
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

end TestsSecurity.JointSimulation

run_cmd ZkcTools.DeclarationAudit.checkCurrent "JOINT-SIMULATION-AXIOM-PASS"
