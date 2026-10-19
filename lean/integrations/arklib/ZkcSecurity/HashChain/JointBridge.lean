module

public import ZkcSecurity.HashChain.JointCoupling
public import ZkcSecurity.VCVio.Memo

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

section Experiments
variable (encoding : Encoding E Shape S Query) (width : ℕ)
  (absorb : Typed.Interface J E P (fun _ => Fin width → S)) (scheme : Extractable Shape Value Query S)
  (verifier : Stmt → PIR.Proc (committed J Shape Value) A) (initial : Stmt → List (Absorbed E Shape S))
  (statementRoots : Stmt → List (Shape × S))

/-- The translated experiment: draw the private tape, run the logged adversary against the joint
simulator, then the verifier's joint-oracle reading, all on one lazily sampled joint oracle; the
prover's log is the classified byte log. -/
noncomputable def translatedExperiment (calls : ℕ)
    (adversary : OracleComp (ByteHash S) (Stmt × Proof P Value S)) :
    ProbComp (JointRun Stmt P Value S A (QueryLog (OracleSpec.ofFn (Cells E Shape S Query width)))) := do
  let tape ← $ᵗ (Fin calls → S)
  (simulateQ randomOracle (do
    let claim ← (jointSimulator encoding width calls).translate adversary.withQueryLog tape
    let verifierRun ← jointReading width absorb scheme verifier initial statementRoots claim.1.1
      claim.1.2
    pure (assemble encoding width claim verifierRun))).run' ∅

omit [DecidableEq E] [DecidableEq Shape] [DecidableEq S] [DecidableEq Query] [Inhabited S]
  [SampleableType S] in
theorem combine_empty :
    combine width (∅ : (OracleSpec.ofFn (Answer (Absorbed E Shape S) S width)).QueryCache)
      (fun _ : Query => (none : Option S)) = ∅ := by
  apply QueryCache.ext
  intro key
  cases key <;> rfl

/-- The lazily sampled joint simulation has the law of the translated experiment. -/
theorem lazy_eq_translated (positive : 0 < width)
    (adversary : OracleComp (ByteHash S) (Stmt × Proof P Value S)) {calls : ℕ}
    (bounded : IsTotalQueryBound adversary calls) {queries : ℕ}
    (queryBounded : ∀ statement proof, IsTotalQueryBound
      (jointReading width absorb scheme verifier initial statementRoots statement proof) queries) :
    𝒮[lazyExperiment encoding width absorb scheme verifier initial statementRoots adversary] =
      𝒮[translatedExperiment encoding width absorb scheme verifier initial statementRoots calls
        adversary] := by
  have logged : IsTotalQueryBound adversary.withQueryLog calls :=
    (isTotalQueryBound_withQueryLog_iff _ _).mpr bounded
  let slots := calls + queries
  let finish : ((Stmt × Proof P Value S) × QueryLog (ByteHash S)) ×
      (JointState E Shape S Query width calls ×
        (OracleSpec.ofFn (Cells E Shape S Query width)).QueryCache) →
      ProbComp (JointRun Stmt P Value S A (QueryLog (OracleSpec.ofFn (Cells E Shape S Query width)))) :=
    fun result => assemble encoding width result.1 <$>
      (simulateQ randomOracle (jointReading width absorb scheme verifier initial statementRoots
        result.1.1.1 result.1.1.2)).run' result.2.2
  have right : ∀ tape : Fin calls → S,
      (simulateQ randomOracle (do
        let claim ← (jointSimulator encoding width calls).translate adversary.withQueryLog tape
        let verifierRun ← jointReading width absorb scheme verifier initial statementRoots claim.1.1
          claim.1.2
        pure (assemble encoding width claim verifierRun))).run' ∅ =
      (simulateQ (flatJoint encoding width calls) adversary.withQueryLog).run
          ((jointSimulator encoding width calls).start tape, ∅) >>= finish := by
    intro tape
    simp only [Provider.Simulator.translate, StateT.run'_eq, simulateQ_bind, simulateQ_pure,
      StateT.run_bind, StateT.run_pure, bind_map_left]
    rw [simulateQ_flatten]
    simp only [flatJoint, finish, map_bind, bind_map_left, Functor.map_map, StateT.run'_eq,
      bind_pure_comp]
  have filled : 𝒮[translatedExperiment encoding width absorb scheme verifier initial statementRoots
        calls adversary] =
      𝒮[(fillJoint width calls slots (Simulated.empty width, fun _ => none) >>= fun state =>
        (simulateQ (flatJoint encoding width calls) adversary.withQueryLog).run state) >>= finish] := by
    simp only [translatedExperiment, right, fillJoint, fillAll, completed_empty, completedWith_empty,
      combine_empty, map_bind, map_pure, bind_assoc, pure_bind]
    exact (evalSPMF_uniform_drop _).symm
  rw [filled, evalSPMF_bind, adversary_eq encoding width calls slots adversary.withQueryLog logged
    (Simulated.empty width, fun _ => none) (fun _ _ absent => absurd rfl absent)
    (by simp [Simulated.empty]) (by simp [Simulated.empty, slots]), ← evalSPMF_bind, bind_assoc]
  simp only [lazyExperiment]
  refine evalSPMF_bind_congr fun started member => ?_
  obtain ⟨left, -, organized, room⟩ := support_simulateQ_invariant (splitSimulator encoding width)
    (fun remaining current => Organized current.1 ∧ current.1.touched.length + remaining ≤ calls)
    (fun remaining bytes current inv step stepMember => by
      obtain ⟨stepOrganized, -, touched⟩ :=
        splitSimulator_support encoding width bytes current.1 current.2 inv.1 step stepMember
      exact ⟨stepOrganized, by omega⟩)
    adversary.withQueryLog calls (Simulated.empty width, fun _ => none) logged
    ⟨fun _ _ absent => absurd rfl absent, by simp [Simulated.empty]⟩ started member
  have verified := verifier_eq width slots positive (jointReading width absorb scheme verifier initial
    statementRoots started.1.1.1 started.1.1.2) (queryBounded _ _) started.2.1 started.2.2
    organized (show started.2.1.touched.length + queries ≤ slots by omega)
  have dropped : 𝒮[(fun filled => (started.1, filled)) <$> fillJoint width calls slots started.2 >>=
        finish] =
      𝒮[assemble encoding width started.1 <$> (fillCache width slots (started.2.1, started.2.2) >>=
        fun cache => (simulateQ randomOracle (jointReading width absorb scheme verifier initial
          statementRoots started.1.1.1 started.1.1.2)).run' cache)] := by
    simp only [bind_map_left, finish, fillJoint, fillAll, fillCache, fillHistory, bind_assoc, pure_bind,
      map_bind]
    refine evalSPMF_bind_congr' _ fun rowsTable => ?_
    exact evalSPMF_uniform_drop _
  rw [dropped, evalSPMF_map_eq_of_evalSPMF_eq verified, bind_pure_comp]

end Experiments

section Logs
variable (encoding : Encoding E Shape S Query) (width length : ℕ)

/-- A joint simulator state corresponds to a classification: the chain part's private answers and
recorded histories are the classification's, and a joint key has a recorded answer exactly when the
classification has read it. -/
def Corresponds (state : JointState E Shape S Query width length)
    (classification : Classification E Shape S Query) : Prop :=
  state.chain.answers = classification.answers ∧ state.chain.reached = classification.reached ∧
    ∀ key, ((jointSimulator encoding width length).recorded state key).isSome =
      classification.emitted key

omit [Inhabited S] [SampleableType S] in
theorem corresponds_start [Inhabited S] (tape : Fin length → S) :
    Corresponds encoding width length ((jointSimulator encoding width length).start tape)
      Classification.empty :=
  ⟨rfl, rfl, fun key => by cases key <;> rfl⟩

omit [SampleableType S] in
/-- One call of the joint simulator logs, on the joint oracle, what the classification reads from
the call and its reply, and keeps the correspondence. -/
theorem handle_log (bytes : Bytes) (state : JointState E Shape S Query width length)
    (classification : Classification E Shape S Query)
    (corresponds : Corresponds encoding width length state classification) :
    ∀ result ∈ support ((((jointSimulator encoding width length).handle bytes).run state).withQueryLog),
      skeleton result.2 = skeleton (classification.step encoding width bytes result.1.1).1 ∧
        Corresponds encoding width length result.1.2
          (classification.step encoding width bytes result.1.1).2 := by
  obtain ⟨answers, reached, emitted⟩ := corresponds
  intro result member
  have sameAttempt : jointAttempt encoding width classification.reached bytes =
      (jointSimulator encoding width length).attempt state bytes := by
    rw [jointSimulator_attempt, reached]
  cases assigned : (jointSimulator encoding width length).attempt state bytes with
  | none =>
      rw [(jointSimulator encoding width length).handle_private assigned, withQueryLog_pure,
        support_pure, Set.mem_singleton_iff] at member
      subst member
      have outside : jointAttempt encoding width classification.reached bytes = none :=
        sameAttempt.trans assigned
      cases fresh : state.chain.answers (encoding.chainInput bytes) with
      | some answer =>
          have stored : classification.answers (encoding.chainInput bytes) = some answer := by
            rw [← answers]; exact fresh
          have respond : state.chain.respond (encoding.chainInput bytes) = (answer, state.chain) := by
            simp only [ChainState.respond, fresh]
          simp only [Classification.step, outside, stored]
          refine ⟨trivial, ?_⟩
          rw [respond]
          exact ⟨answers, reached, emitted⟩
      | none =>
          have stored : classification.answers (encoding.chainInput bytes) = none := by
            rw [← answers]; exact fresh
          simp only [Classification.step, outside, stored]
          refine ⟨trivial, ?_, ?_, fun key => ?_⟩
          · change (state.chain.respond (encoding.chainInput bytes)).2.answers = _
            simp only [ChainState.respond, fresh, answers]
          · change (state.chain.respond (encoding.chainInput bytes)).2.reached = _
            simp only [ChainState.respond, fresh, reached]
          · rw [← emitted key]
            exact congrArg Option.isSome
              ((jointSimulator encoding width length).recorded_respond state bytes key)
  | some key =>
      have inside : jointAttempt encoding width classification.reached bytes = some key :=
        sameAttempt.trans assigned
      cases recorded : (jointSimulator encoding width length).recorded state key with
      | some ideal =>
          rw [(jointSimulator encoding width length).handle_recorded assigned recorded, withQueryLog_pure,
            support_pure, Set.mem_singleton_iff] at member
          subst member
          have read : classification.emitted key = true := by
            rw [← emitted key, recorded]; rfl
          simp only [Classification.step, inside, read, ↓reduceIte]
          exact ⟨trivial, answers, reached, emitted⟩
      | none =>
          rw [(jointSimulator encoding width length).handle_fresh assigned recorded,
            ZkcSecurity.VCVio.Memo.withQueryLog_map, withQueryLog_query, support_map] at member
          obtain ⟨⟨ideal, log⟩, inner, rfl⟩ := member
          simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at inner
          obtain ⟨answer, -, same⟩ := inner
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
          have unread : classification.emitted key = false := by
            rw [← emitted key, recorded]; rfl
          have stepped : classification.step encoding width bytes
              ((jointSimulator encoding width length).shared bytes key ideal) =
              ([keyEntry key ((jointSimulator encoding width length).shared bytes key ideal)],
                { classification with emitted := Function.update classification.emitted key true }) := by
            simp only [Classification.step, inside, unread, Bool.false_eq_true, ↓reduceIte]
          change skeleton [⟨key, ideal⟩] = skeleton (classification.step encoding width bytes
              ((jointSimulator encoding width length).shared bytes key ideal)).1 ∧
            Corresponds encoding width length ((jointSimulator encoding width length).record state key
              ideal) (classification.step encoding width bytes
                ((jointSimulator encoding width length).shared bytes key ideal)).2
          rw [stepped]
          refine ⟨?_, ?_, ?_, fun other => ?_⟩
          · cases key <;> rfl
          · rw [← answers]
            cases key <;> rfl
          · rw [← reached]
            cases key <;> rfl
          · by_cases same : other = key
            · subst same
              rw [(jointSimulator encoding width length).recorded_record]
              exact (Function.update_self other true classification.emitted).symm
            · rw [(jointSimulator encoding width length).recorded_record_of_ne _ _ _ _ same]
              exact (emitted other).trans (Function.update_of_ne same true classification.emitted).symm

omit [SampleableType S] in
/-- A run of the joint simulator on the logged adversary asks the joint oracle what the
classification reads from the adversary's logged calls: the joint oracle's record and the
classified byte log have one skeleton. -/
theorem run_log {α : Type} (adversary : OracleComp (ByteHash S) α) :
    ∀ (state : JointState E Shape S Query width length)
      (classification : Classification E Shape S Query),
      Corresponds encoding width length state classification →
      ∀ result ∈ support (((simulateQ (jointSimulator encoding width length).handle
          adversary.withQueryLog).run state).withQueryLog),
        skeleton result.2 = skeleton (classification.read encoding width result.1.1.2) := by
  induction adversary using OracleComp.inductionOn with
  | pure value =>
      intro state classification _ result member
      simp only [withQueryLog_pure, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at member
      subst member
      rfl
  | query_bind bytes next ih =>
      intro state classification corresponds result member
      rw [withQueryLog_bind, withQueryLog_query] at member
      simp only [bind_assoc, pure_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_map,
        StateT.run_bind, StateT.run_map] at member
      rw [withQueryLog_bind, mem_support_bind_iff] at member
      obtain ⟨step, stepMember, restMember⟩ := member
      rw [support_map, ZkcSecurity.VCVio.Memo.withQueryLog_map, support_map] at restMember
      obtain ⟨_, ⟨inner, innerMember, rfl⟩, rfl⟩ := restMember
      obtain ⟨stepSkeleton, stepCorresponds⟩ :=
        handle_log encoding width length bytes state classification corresponds step stepMember
      have restSkeleton := ih step.1.1 step.1.2 _ stepCorresponds inner innerMember
      simp only [Prod.map, id, List.singleton_append, Classification.read, skeleton_append,
        stepSkeleton, restSkeleton]

end Logs

section Ideal
variable (encoding : Encoding E Shape S Query) (width : ℕ)
  (absorb : Typed.Interface J E P (fun _ => Fin width → S)) (scheme : Extractable Shape Value Query S)
  (verifier : Stmt → PIR.Proc (committed J Shape Value) A) (initial : Stmt → List (Absorbed E Shape S))
  (statementRoots : Stmt → List (Shape × S))

omit [DecidableEq E] [DecidableEq Shape] [DecidableEq S] [DecidableEq Query] [Inhabited S]
  [SampleableType S] in
/-- Dropping the log of a logged computation gives the computation. -/
theorem fst_withQueryLog {ι α : Type} {spec : OracleSpec ι} (computation : OracleComp spec α) :
    Prod.fst <$> computation.withQueryLog = computation :=
  loggingOracle.fst_map_run_simulateQ computation

omit [SampleableType S] in
/-- On every run of a translated logged adversary, the joint oracle's record of the translated
prover's queries has the skeleton of the classified byte log. -/
theorem translate_skeleton (calls : ℕ) {α : Type} (adversary : OracleComp (ByteHash S) α)
    (tape : Fin calls → S) :
    ∀ result ∈ support (((jointSimulator encoding width calls).translate adversary.withQueryLog
        tape).withQueryLog),
      skeleton result.2 = skeleton (classifyLog encoding width result.1.2) := by
  intro result member
  unfold Provider.Simulator.translate at member
  rw [StateT.run'_eq, ZkcSecurity.VCVio.Memo.withQueryLog_map, support_map] at member
  obtain ⟨inner, innerMember, rfl⟩ := member
  exact run_log encoding width calls adversary _ _ (corresponds_start encoding width calls tape) inner
    innerMember

omit [SampleableType S] in
/-- The translated program of an adversary drops the log of the translated logged adversary. -/
theorem translate_fst (calls : ℕ) {α : Type} (adversary : OracleComp (ByteHash S) α)
    (tape : Fin calls → S) :
    (jointSimulator encoding width calls).translate adversary tape =
      Prod.fst <$> (jointSimulator encoding width calls).translate adversary.withQueryLog tape := by
  conv_lhs => rw [← fst_withQueryLog adversary]
  unfold Provider.Simulator.translate
  rw [simulateQ_map, StateT.run'_eq, StateT.run'_eq, StateT.run_map, Functor.map_map,
    Functor.map_map]

/-- The bridge's event has the same probability in the translated experiment, whose prover log is
the classified byte log, as for the translated prover mixture in the joint experiment, whose prover
log is the joint oracle's record of the prover's queries. -/
theorem translated_eq_ideal (words : Words J Shape Value) (calls : ℕ)
    (adversary : OracleComp (ByteHash S) (Stmt × Proof P Value S))
    (falseStatement : Stmt → List (Table Value) → Prop) (accepts : A → Prop) :
    Pr{let result ← translatedExperiment encoding width absorb scheme verifier initial
        statementRoots calls adversary}[
      FalseAcceptance words scheme statementRoots falseStatement accepts result] =
      Stage.Joint.oracleMixture
        (ZkcSecurity.Commitment.experiment absorb scheme verifier initial statementRoots)
        (FalseAcceptance words scheme statementRoots falseStatement accepts)
        (do let tape ← $ᵗ (Fin calls → S)
            pure ((jointSimulator encoding width calls).translate adversary tape)) := by
  have pointwise : ∀ tape : Fin calls → S,
      Pr{let result ← (simulateQ randomOracle (do
          let claim ← (jointSimulator encoding width calls).translate adversary.withQueryLog tape
          let verifierRun ← jointReading width absorb scheme verifier initial statementRoots claim.1.1
            claim.1.2
          pure (assemble encoding width claim verifierRun))).run' ∅}[
        FalseAcceptance words scheme statementRoots falseStatement accepts result] =
      Pr{let result ← (simulateQ randomOracle (ZkcSecurity.Commitment.experiment absorb scheme verifier
          initial statementRoots ((jointSimulator encoding width calls).translate adversary tape))).run'
            ∅}[FalseAcceptance words scheme statementRoots falseStatement accepts result] := by
    intro tape
    let logged := ((jointSimulator encoding width calls).translate adversary.withQueryLog tape).withQueryLog
    let reading : (((Stmt × Proof P Value S) × QueryLog (ByteHash S)) ×
        QueryLog (OracleSpec.ofFn (Cells E Shape S Query width))) →
        OracleComp (OracleSpec.ofFn (Cells E Shape S Query width))
          ((((Stmt × Proof P Value S) × QueryLog (ByteHash S)) ×
            QueryLog (OracleSpec.ofFn (Cells E Shape S Query width))) ×
            (PIR.Outcome A × QueryLog (OracleSpec.ofFn (Cells E Shape S Query width)))) :=
      fun claim => (fun verifierRun => (claim, verifierRun)) <$>
        jointReading width absorb scheme verifier initial statementRoots claim.1.1.1 claim.1.1.2
    have left : (do
        let claim ← (jointSimulator encoding width calls).translate adversary.withQueryLog tape
        let verifierRun ← jointReading width absorb scheme verifier initial statementRoots claim.1.1
          claim.1.2
        pure (assemble encoding width claim verifierRun)) =
        (fun pair => assemble encoding width pair.1.1 pair.2) <$> (logged >>= reading) := by
      conv_lhs => rw [← fst_withQueryLog ((jointSimulator encoding width calls).translate
        adversary.withQueryLog tape)]
      simp only [logged, reading, bind_map_left, map_bind, Functor.map_map, bind_pure_comp]
    have right : ZkcSecurity.Commitment.experiment absorb scheme verifier initial statementRoots
        ((jointSimulator encoding width calls).translate adversary tape) =
        (fun pair => (JointRun.mk pair.1.1.1.1 pair.1.1.1.2 pair.2.1 pair.1.2 pair.2.2 :
            JointRun Stmt P Value S A (QueryLog (OracleSpec.ofFn (Cells E Shape S Query width))))) <$>
          (logged >>= reading) := by
      rw [translate_fst encoding width calls adversary tape]
      unfold ZkcSecurity.Commitment.experiment
      rw [ZkcSecurity.VCVio.Memo.withQueryLog_map]
      simp only [logged, reading, bind_map_left, map_bind, Functor.map_map, bind_pure_comp, jointReading,
        Prod.map]
      rfl
    rw [left, right, simulateQ_map, simulateQ_map, StateT.run'_eq, StateT.run'_eq, StateT.run_map,
      StateT.run_map, Functor.map_map, Functor.map_map, prEvent_map, prEvent_map]
    refine le_antisymm (prEvent_mono_of_support _ _ _ fun run member holds => ?_)
      (prEvent_mono_of_support _ _ _ fun run member holds => ?_)
    all_goals
      have reachable : run.1 ∈ support (logged >>= reading) :=
        support_simulateQ_run'_subset randomOracle (logged >>= reading) ∅
          (by rw [StateT.run'_eq, support_map]; exact ⟨run, member, rfl⟩)
      rw [mem_support_bind_iff] at reachable
      obtain ⟨claim, claimMember, readingMember⟩ := reachable
      simp only [reading, support_map] at readingMember
      obtain ⟨verifierRun, -, same⟩ := readingMember
      have skeletons := translate_skeleton encoding width calls adversary tape claim claimMember
      rw [← same] at holds ⊢
    · exact (falseAcceptance_congr_skeleton words scheme statementRoots falseStatement accepts
        (assemble encoding width claim.1 verifierRun)
        (JointRun.mk claim.1.1.1 claim.1.1.2 verifierRun.1 claim.2 verifierRun.2) rfl rfl rfl
        skeletons.symm).mp holds
    · exact (falseAcceptance_congr_skeleton words scheme statementRoots falseStatement accepts
        (JointRun.mk claim.1.1.1 claim.1.1.2 verifierRun.1 claim.2 verifierRun.2)
        (assemble encoding width claim.1 verifierRun) rfl rfl rfl skeletons).mp holds
  have composed := prEvent_bind_congr (m := ProbComp) ($ᵗ (Fin calls → S)) _ _ _ _ pointwise
  unfold Stage.Joint.oracleMixture translatedExperiment
  simpa only [bind_assoc, pure_bind] using composed

end Ideal

end ZkcSecurity.HashChain.Joint
