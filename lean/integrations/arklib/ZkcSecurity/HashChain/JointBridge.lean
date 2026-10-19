module

public import ZkcSecurity.HashChain.JointCoupling

@[expose] public section

/-! # The lazily sampled joint simulation is the translated joint experiment

The lazily sampled joint simulation of `ZkcSecurity.HashChain.Joint.lazyExperiment` samples a
private answer when a call is first answered privately, a history cell when a counter block first
reads it, and a hash call's answer when the call is first made. The translated experiment
(`translatedExperiment`) samples the private tape ahead, runs the adversary against the joint
simulator (`jointSimulator`), whose transcript cells and hash cells are cells of one lazily sampled
joint oracle, and then runs the verifier's joint-oracle reading against the same oracle. The two
have the same law (`lazy_eq_translated`).

As in `ZkcSecurity.HashChain.simulatedExperiment_eq_translated`, the comparison fills a lazy state
ahead (`fillJoint`): the chain part as `ZkcSecurity.HashChain.fillAll` fills it, with the joint
cache holding the filled history answers at the chain histories of transcript keys and the hash
answers as they are (`combine`). Each step commutes with the fill
(`ZkcSecurity.VCVio.Deferral.evalSPMF_simulateQ_fill`):

- a chain input by `ZkcSecurity.HashChain.adversary_commute`, since on a chain input the joint
  simulator's step is the chain simulator's (`flatJoint_run_chain`);
- a hash call because its fresh answer is one uniform sample on both sides, drawn independently of
  the fill (`hash_commute`);
- in the verifier's phase, a transcript key by `ZkcSecurity.HashChain.answer_commute` and a hash
  call alike (`verifier_eq`).

**Logs.** The translated experiment's prover log is the joint oracle's record of the translated
prover's queries. A run of the joint simulator asks the joint oracle exactly at the first call of
each attempt, so that record has the skeleton of the classified byte log of the adversary's calls
(`translate_skeleton`, through the correspondence `Corresponds` of the simulator's state with the
classification). Hence the bridge's event has the same probability in the translated experiment
with either log (`translated_eq_ideal`), and the lazily sampled joint simulation's event
probability is the ideal failure of the translated prover mixture that the joint stage's frame
consumes.
-/

set_option autoImplicit false
set_option linter.deprecated false

namespace ZkcSecurity.HashChain.Joint
open OracleComp OracleSpec OracleComp.ProgramLogic.Relational ZkcSecurity.FiatShamir
  ZkcSecurity.Commitment ZkcSecurity.HashChain.Encoding ZkcSecurity.VCVio.Deferral

variable {J : PIR.Signature} {E P Shape Value Query S A Stmt : Type} [DecidableEq E]
  [DecidableEq Shape] [DecidableEq S] [DecidableEq Query] [Inhabited S] [SampleableType S]

section Fill
variable (width length slots : ℕ)

/-- A lazy joint state filled ahead: the chain simulator's state and the joint cache, from the
filled chain part and the hash answers. -/
noncomputable def fillJoint
    (state : Simulated (Absorbed E Shape S) S Bytes width × (Query → Option S)) :
    ProbComp (JointState E Shape S Query width length ×
      (OracleSpec.ofFn (Cells E Shape S Query width)).QueryCache) :=
  (fun filled => ((⟨filled.1, state.2⟩ : JointState E Shape S Query width length),
    combine width filled.2 state.2)) <$> fillAll (length := length) slots state.1

/-- A lazy joint state's joint cache filled ahead. -/
noncomputable def fillCache (state : Simulated (Absorbed E Shape S) S Bytes width × (Query → Option S)) :
    ProbComp (OracleSpec.ofFn (Cells E Shape S Query width)).QueryCache :=
  (fun cache => combine width cache state.2) <$> fillHistory slots state.1

end Fill

section AdversaryPhase
variable (encoding : Encoding E Shape S Query) (width length slots : ℕ)

/-- A chain input: filling then running the joint simulator has the law of running the lazy
simulator then filling. -/
theorem chain_commute {bytes : Bytes} {input : Input (Absorbed E Shape S) S Bytes}
    (classified : encoding.classify bytes = .inr input)
    (tables : Simulated (Absorbed E Shape S) S Bytes width) (rows : Query → Option S)
    (organized : Organized tables) (tapeRoom : tables.consumed.length < length)
    (slotRoom : tables.touched.length < slots) :
    𝒮[fillJoint width length slots (tables, rows) >>= fun filled =>
        (flatJoint encoding width length bytes).run filled] =
      𝒮[(splitSimulator encoding width bytes).run (tables, rows) >>= fun step =>
        (fun filled => (step.1, filled)) <$> fillJoint width length slots step.2] := by
  have lifted : (fillJoint width length slots (tables, rows) >>= fun filled =>
      (flatJoint encoding width length bytes).run filled) =
      (fun step => (step.1, ((⟨step.2.1, rows⟩ : JointState E Shape S Query width length),
        combine width step.2.2 rows))) <$>
          (fillAll (length := length) slots tables >>= fun filled =>
            (flatSimulator width length input).run filled) := by
    simp only [fillJoint, bind_map_left, map_bind]
    refine bind_congr fun filled => ?_
    exact flatJoint_run_chain encoding width length classified filled.1 rows filled.2
  rw [lifted, evalSPMF_map_eq_of_evalSPMF_eq
    (adversary_commute input tables organized tapeRoom slotRoom) _]
  rw [splitSimulator_inr encoding width classified, onFirst_run]
  simp only [map_bind, bind_map_left, Functor.map_map, fillJoint]

/-- A hash call: filling then running the joint simulator has the law of running the lazy
simulator then filling, since a fresh answer is one uniform sample drawn independently of the
fill. -/
theorem hash_commute (call : Query) (tables : Simulated (Absorbed E Shape S) S Bytes width)
    (rows : Query → Option S) :
    𝒮[fillJoint width length slots (tables, rows) >>= fun filled =>
        (flatJoint encoding width length (encoding.callBytes call)).run filled] =
      𝒮[(splitSimulator encoding width (encoding.callBytes call)).run (tables, rows) >>= fun step =>
        (fun filled => (step.1, filled)) <$> fillJoint width length slots step.2] := by
  have step : ∀ filled : ChainState (Absorbed E Shape S) S Bytes width length ×
      (OracleSpec.ofFn (Answer (Absorbed E Shape S) S width)).QueryCache,
      (flatJoint encoding width length (encoding.callBytes call)).run
          ((⟨filled.1, rows⟩ : JointState E Shape S Query width length), combine width filled.2 rows) =
        match rows call with
        | some answer => pure (answer, ((⟨filled.1, rows⟩ : JointState E Shape S Query width length),
            combine width filled.2 rows))
        | none => ($ᵗ S) >>= fun answer =>
            pure (answer, ((⟨filled.1, Function.update rows call (some answer)⟩ :
              JointState E Shape S Query width length),
              combine width filled.2 (Function.update rows call (some answer)))) :=
    fun filled => flatJoint_run_hash encoding width length call filled.1 rows filled.2
  rw [splitSimulator_inl encoding width (encoding.classify_callBytes call), onSecond_run]
  simp only [fillJoint, bind_map_left, rowImpl, StateT.run_mk, step]
  cases recorded : rows call with
  | some answer =>
      rw [lazy_some recorded]
      simp
  | none =>
      rw [lazy_none recorded]
      simp only [bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp_def]
      exact evalSPMF_bind_bind_swap _ _ _

omit [Inhabited S] in
theorem splitSimulator_support (bytes : Bytes) (tables : Simulated (Absorbed E Shape S) S Bytes width)
    (rows : Query → Option S) (organized : Organized tables) :
    ∀ step ∈ support ((splitSimulator encoding width bytes).run (tables, rows)),
      Organized step.2.1 ∧ step.2.1.consumed.length ≤ tables.consumed.length + 1 ∧
        step.2.1.touched.length ≤ tables.touched.length + 1 := by
  intro step member
  cases classified : encoding.classify bytes with
  | inl call =>
      rw [splitSimulator_inl encoding width classified, onSecond_run, support_map] at member
      obtain ⟨inner, -, rfl⟩ := member
      exact ⟨organized, Nat.le_succ _, Nat.le_succ _⟩
  | inr input =>
      rw [splitSimulator_inr encoding width classified] at member
      obtain ⟨inner, innerMember, rfl⟩ := onFirst_support member
      exact simulator_step_support input tables organized inner innerMember

/-- The lazy joint simulation's run of an adversary within its query bound, filled, has the law of
the joint simulator's run from the filled state. -/
theorem adversary_eq {α : Type} (adversary : OracleComp (ByteHash S) α) {calls : ℕ}
    (bounded : IsTotalQueryBound adversary calls)
    (state : Simulated (Absorbed E Shape S) S Bytes width × (Query → Option S))
    (organized : Organized state.1) (tapeRoom : state.1.consumed.length + calls ≤ length)
    (slotRoom : state.1.touched.length + calls ≤ slots) :
    𝒮[fillJoint width length slots state >>= fun filled =>
        (simulateQ (flatJoint encoding width length) adversary).run filled] =
      𝒮[(simulateQ (splitSimulator encoding width) adversary).run state >>= fun result =>
        (fun filled => (result.1, filled)) <$> fillJoint width length slots result.2] :=
  evalSPMF_simulateQ_fill (splitSimulator encoding width) (flatJoint encoding width length)
    (fillJoint width length slots)
    (fun remaining current => Organized current.1 ∧ current.1.consumed.length + remaining ≤ length ∧
      current.1.touched.length + remaining ≤ slots)
    (fun _ bytes current inv => by
      cases classified : encoding.classify bytes with
      | inl call =>
          rw [encoding.eq_of_classify_inl classified]
          exact hash_commute encoding width length slots call current.1 current.2
      | inr input =>
          exact chain_commute encoding width length slots classified current.1 current.2 inv.1
            (by omega) (by omega))
    (fun remaining bytes current inv step member => by
      obtain ⟨stepOrganized, consumed, touched⟩ :=
        splitSimulator_support encoding width bytes current.1 current.2 inv.1 step member
      exact ⟨stepOrganized, by omega, by omega⟩)
    adversary calls state bounded ⟨organized, tapeRoom, slotRoom⟩

end AdversaryPhase

section VerifierPhase
variable (width slots : ℕ)

/-- A transcript key: filling then asking the joint oracle has the law of reading the lazy history
cells of its chain history then filling. -/
theorem transcript_commute (positive : 0 < width) (key : TranscriptKey E Shape S)
    (tables : Simulated (Absorbed E Shape S) S Bytes width) (rows : Query → Option S)
    (organized : Organized tables) (room : tables.touched.length < slots) :
    𝒮[fillCache width slots (tables, rows) >>= fun cache =>
        (randomOracle (spec := OracleSpec.ofFn (Cells E Shape S Query width)) (.inl key)).run cache] =
      𝒮[(lazyJoint width (.inl key)).run (tables, rows) >>= fun step =>
        (fun cache => (step.1, cache)) <$> fillCache width slots step.2] := by
  have lifted : (fillCache width slots (tables, rows) >>= fun cache =>
      (randomOracle (spec := OracleSpec.ofFn (Cells E Shape S Query width)) (.inl key)).run cache) =
      (fun step => (step.1, combine width step.2 rows)) <$>
        (fillHistory slots tables >>= fun cache =>
          (randomOracle (spec := OracleSpec.ofFn (Answer (Absorbed E Shape S) S width))
            (chainKey key)).run cache) := by
    simp only [fillCache, bind_map_left, map_bind]
    refine bind_congr fun cache => ?_
    exact randomOracle_combine width cache rows key
  rw [lifted]
  refine (evalSPMF_map_eq_of_evalSPMF_eq
    (answer_commute positive (chainKey key) tables organized room) _).trans ?_
  congr 1
  show _ = ((fun result => (result.1, (result.2, rows))) <$> (historyAnswer width (chainKey key)).run tables) >>=
    fun (step : (Fin width → S) × (Simulated (Absorbed E Shape S) S Bytes width × (Query → Option S))) =>
      (fun cache => (step.1, cache)) <$> fillCache width slots step.2
  simp only [bind_map_left, fillCache]
  refine (map_bind _ _ _).trans (bind_congr fun step => ?_)
  refine Eq.trans (comp_map _ _ _).symm (Eq.trans ?_ (comp_map _ _ _))
  rfl

/-- A hash call: filling then asking the joint oracle has the law of reading the lazy table of
hash calls then filling. -/
theorem hashCell_commute (call : Query) (tables : Simulated (Absorbed E Shape S) S Bytes width)
    (rows : Query → Option S) :
    𝒮[fillCache width slots (tables, rows) >>= fun cache =>
        (randomOracle (spec := OracleSpec.ofFn (Cells E Shape S Query width)) (.inr call)).run cache] =
      𝒮[(lazyJoint width (.inr call)).run (tables, rows) >>= fun step =>
        (fun cache => (step.1, cache)) <$> fillCache width slots step.2] := by
  show 𝒮[fillCache width slots (tables, rows) >>= fun cache =>
      (randomOracle (spec := OracleSpec.ofFn (Cells E Shape S Query width)) (.inr call)).run cache] =
    𝒮[((fun result => (result.1, (tables, result.2))) <$> lazy rows call) >>=
      fun (step : S × (Simulated (Absorbed E Shape S) S Bytes width × (Query → Option S))) =>
        (fun cache => (step.1, cache)) <$> fillCache width slots step.2]
  simp only [fillCache, bind_map_left, randomOracle_combine_hash]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  exact evalSPMF_bind_bind_swap _ _ _

omit [DecidableEq Query] in
/-- Filling the cache, then dropping it, is the identity in law. -/
theorem fillCache_drop (state : Simulated (Absorbed E Shape S) S Bytes width × (Query → Option S)) {α : Type}
    (computation : ProbComp α) :
    𝒮[fillCache width slots state >>= fun _ => computation] = 𝒮[computation] := by
  simp only [fillCache, bind_map_left]
  exact fillHistory_drop state.1 computation

/-- A computation on the joint oracle, from the filled cache, has the law of the computation on
the lazy joint oracle. -/
theorem verifier_eq (positive : 0 < width) {β : Type}
    (reading : OracleComp (OracleSpec.ofFn (Cells E Shape S Query width)) β) {queries : ℕ}
    (bounded : IsTotalQueryBound reading queries) (tables : Simulated (Absorbed E Shape S) S Bytes width)
    (rows : Query → Option S) (organized : Organized tables)
    (room : tables.touched.length + queries ≤ slots) :
    𝒮[fillCache width slots (tables, rows) >>= fun cache => (simulateQ randomOracle reading).run' cache] =
      𝒮[(simulateQ (lazyJoint width) reading).run' (tables, rows)] := by
  have filled := evalSPMF_simulateQ_fill (lazyJoint width) randomOracle (fillCache width slots)
    (fun remaining current => Organized current.1 ∧ current.1.touched.length + remaining ≤ slots)
    (fun _ key current inv => by
      cases key with
      | inl key =>
          exact transcript_commute width slots positive key current.1 current.2 inv.1 (by omega)
      | inr call => exact hashCell_commute width slots call current.1 current.2)
    (fun remaining key current inv step member => by
      obtain ⟨organized', room'⟩ := inv
      cases key with
      | inl key =>
          obtain ⟨inner, innerMember, rfl⟩ := onFirst_support member
          obtain ⟨stepOrganized, stepTouched⟩ := collect_historyBlock_support (chainKey key) width
            (fun block => block) current.1 organized' inner innerMember
          refine ⟨stepOrganized, ?_⟩
          rcases stepTouched with same | ⟨-, appended⟩
          · simp only [same]; omega
          · simp only [appended, List.length_append, List.length_singleton]; omega
      | inr call =>
          change step ∈ support ((onSecond (rowImpl call)).run current) at member
          rw [onSecond_run, support_map] at member
          obtain ⟨inner, -, rfl⟩ := member
          show Organized current.1 ∧ current.1.touched.length + remaining ≤ slots
          exact ⟨organized', by omega⟩)
    reading queries (tables, rows) bounded ⟨organized, room⟩
  simp only [StateT.run'_eq, map_eq_bind_pure_comp, Function.comp_def]
  rw [← bind_assoc, evalSPMF_bind, filled, ← evalSPMF_bind, bind_assoc]
  refine evalSPMF_bind_congr fun step _ => ?_
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  exact fillCache_drop width slots step.2 _

end VerifierPhase

end ZkcSecurity.HashChain.Joint
