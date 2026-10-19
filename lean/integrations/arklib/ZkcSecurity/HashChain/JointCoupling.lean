module

public import ZkcSecurity.HashChain.JointReading
public import ZkcSecurity.HashChain.Bound

@[expose] public section

/-! # The concrete experiment is the lazily sampled joint simulation up to the bad event

The concrete experiment (`concreteExperiment`) runs the adversary and the deployed verifier on one
lazily sampled byte hash. This module couples it with a lazily sampling simulation in which the
transcript is read from history cells and the hash calls from their own lazily sampled cells, up
to the hash chain's bad event, a collision or a prediction among the generating calls.

**Splitting the byte hash** (`split_coupling`). Because the classification of bytes is injective,
the lazy random oracle on bytes is the lazy random oracle on classified inputs: hash calls are
answered by a table of their own (`rowImpl`) and chain inputs by the traced oracle of
`ZkcSecurity.HashChain.Simulator`, which records the chain's trace (`splitTraced`). The two answer
every computation alike.

**The lazily sampled joint simulation.** The adversary runs against `splitSimulator`: hash calls
read the same table of their own, chain inputs the lazy simulator `ZkcSecurity.HashChain.simulator`
over history cells and auxiliary cells. The verifier then runs as the joint oracle's reading
`ZkcSecurity.Commitment.run`, logged, against `lazyJoint`: a transcript key reads the history cells
of its chain history, a hash call the table of hash calls (`lazyExperiment`).

**The coupling** (`concrete_le_lazy`). Hash calls are answered from one table on both sides and
never touch the chain's trace or the simulator's tables (`onFirst`, `onSecond`), so every coupling
step of the hash chain carries over with the table of hash calls alongside:

- the adversary's calls by `ZkcSecurity.HashChain.adversary_step` (`adversary_coupling`);
- the verifier's binding, absorbing and request calls by the chain lemmas of
  `ZkcSecurity.HashChain.Reduction`, and its hash calls by the shared table (`read_coupling`).

The event's probability in the concrete experiment exceeds that in the lazily sampled joint
simulation by at most the probability that the chain's trace raises the bad flag. The flag reads
chain inputs only, so it rises with probability at most `(q + V)² / |S|` for `q` adversary calls and
`V` verifier calls of every kind (`split_bad_le`, `concreteExperiment_queryBound`).
-/

set_option autoImplicit false

namespace ZkcSecurity.HashChain.Joint
open OracleComp OracleSpec OracleComp.ProgramLogic.Relational ZkcSecurity.FiatShamir
  ZkcSecurity.Commitment ZkcSecurity.HashChain.Encoding ZkcSecurity.VCVio.UntilBad

section Focus
variable {σ τ α : Type}

/-- A step on the first component of a product state, the second kept. -/
def onFirst (step : StateT σ ProbComp α) : StateT (σ × τ) ProbComp α :=
  StateT.mk fun state => (fun result => (result.1, (result.2, state.2))) <$> step.run state.1

/-- A step on the second component of a product state, the first kept. -/
def onSecond (step : StateT τ ProbComp α) : StateT (σ × τ) ProbComp α :=
  StateT.mk fun state => (fun result => (result.1, (state.1, result.2))) <$> step.run state.2

theorem onFirst_run (step : StateT σ ProbComp α) (state : σ × τ) :
    (onFirst step).run state = (fun result => (result.1, (result.2, state.2))) <$> step.run state.1 :=
  rfl

theorem onSecond_run (step : StateT τ ProbComp α) (state : σ × τ) :
    (onSecond step).run state = (fun result => (result.1, (state.1, result.2))) <$> step.run state.2 :=
  rfl

theorem collect_onFirst {S : Type} :
    ∀ (count : ℕ) (calls : Fin count → StateT σ ProbComp S) (state : σ) (other : τ),
      (collect count fun index => onFirst (τ := τ) (calls index)).run (state, other) =
        (fun result => (result.1, (result.2, other))) <$> (collect count calls).run state
  | 0, _, _, _ => by simp [collect]
  | count + 1, calls, state, other => by
      have tail := collect_onFirst count (fun index => calls index.succ)
      simp only [collect, StateT.run_bind, onFirst_run, StateT.run_pure, bind_map_left, map_bind]
      refine bind_congr fun head => ?_
      rw [tail]
      simp

theorem simulateQ_onSecond {ι : Type} {spec : OracleSpec ι} (impl : QueryImpl spec (StateT τ ProbComp))
    (computation : OracleComp spec α) :
    ∀ (first : σ) (second : τ),
      (simulateQ (fun query => onSecond (σ := σ) (impl query)) computation).run (first, second) =
        (fun result => (result.1, (first, result.2))) <$> (simulateQ impl computation).run second := by
  induction computation using OracleComp.inductionOn with
  | pure value => intro _ _; simp
  | query_bind query next ih =>
      intro first second
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, onSecond_run, bind_map_left,
        map_bind]
      exact bind_congr fun step => ih step.1 first step.2

theorem onFirst_support {step : StateT σ ProbComp α} {state : σ × τ} {result : α × (σ × τ)}
    (member : result ∈ support ((onFirst step).run state)) :
    ∃ inner ∈ support (step.run state.1), result = (inner.1, (inner.2, state.2)) := by
  rw [onFirst_run, support_map] at member
  obtain ⟨inner, innerMember, rfl⟩ := member
  exact ⟨inner, innerMember, rfl⟩

end Focus

variable {J : PIR.Signature} {E P Shape Value Query S A Stmt : Type} [DecidableEq E]
  [DecidableEq Shape] [DecidableEq S] [DecidableEq Query] [SampleableType S]

section Implementations

/-- The lazily sampled table of hash calls. -/
def rowImpl : QueryImpl (Query →ₒ S) (StateT (Query → Option S) ProbComp) :=
  fun call => StateT.mk fun rows => lazy rows call

variable (encoding : Encoding E Shape S Query) (width : ℕ)

/-- The lazy random oracle on bytes, split by classification: hash calls read their own table and
chain inputs the traced oracle, which records the chain's trace. -/
noncomputable def splitTraced :
    QueryImpl (ByteHash S)
      (StateT (Trace (Absorbed E Shape S) S Bytes × (Query → Option S)) ProbComp) :=
  fun bytes => match encoding.classify bytes with
    | .inl call => onSecond (rowImpl call)
    | .inr input => onFirst (traced input)

/-- The lazily sampling simulation of the byte hash: hash calls read their own table and chain
inputs the lazy simulator over history cells and auxiliary cells. -/
noncomputable def splitSimulator :
    QueryImpl (ByteHash S)
      (StateT (Simulated (Absorbed E Shape S) S Bytes width × (Query → Option S)) ProbComp) :=
  fun bytes => match encoding.classify bytes with
    | .inl call => onSecond (rowImpl call)
    | .inr input => onFirst (simulator width input)

/-- The joint oracle read lazily: a transcript key reads the history cells of its chain history, a
hash call the table of hash calls. -/
noncomputable def lazyJoint :
    QueryImpl (OracleSpec.ofFn (Cells E Shape S Query width))
      (StateT (Simulated (Absorbed E Shape S) S Bytes width × (Query → Option S)) ProbComp) :=
  fun key => match key with
    | .inl key => onFirst (historyAnswer width (chainKey key))
    | .inr call => onSecond (rowImpl call)

theorem splitTraced_inl {bytes : Bytes} {call : Query} (classified : encoding.classify bytes = .inl call) :
    splitTraced encoding bytes = onSecond (rowImpl call) := by
  simp only [splitTraced, classified]

theorem splitTraced_inr {bytes : Bytes} {input : Input (Absorbed E Shape S) S Bytes}
    (classified : encoding.classify bytes = .inr input) :
    splitTraced encoding bytes = onFirst (traced input) := by
  simp only [splitTraced, classified]

theorem splitSimulator_inl {bytes : Bytes} {call : Query}
    (classified : encoding.classify bytes = .inl call) :
    splitSimulator encoding width bytes = onSecond (rowImpl call) := by
  simp only [splitSimulator, classified]

theorem splitSimulator_inr {bytes : Bytes} {input : Input (Absorbed E Shape S) S Bytes}
    (classified : encoding.classify bytes = .inr input) :
    splitSimulator encoding width bytes = onFirst (simulator width input) := by
  simp only [splitSimulator, classified]

end Implementations

section Split
variable (encoding : Encoding E Shape S Query)

/-- A byte cache and a split state that answer the bytes of each classification alike. -/
def SplitCaches (cache : (ByteHash S).QueryCache)
    (state : Trace (Absorbed E Shape S) S Bytes × (Query → Option S)) : Prop :=
  ∀ bytes, cache bytes = match encoding.classify bytes with
    | .inl call => state.2 call
    | .inr input => state.1.cache input

/-- One byte call of the lazy random oracle against the split oracle, from agreeing caches. -/
theorem split_step (bytes : Bytes) (cache : (ByteHash S).QueryCache)
    (state : Trace (Absorbed E Shape S) S Bytes × (Query → Option S))
    (agree : ∀ bytes, cache bytes = match encoding.classify bytes with
      | .inl call => state.2 call
      | .inr input => state.1.cache input) :
    RelTriple ((randomOracle (spec := ByteHash S) bytes).run cache)
      ((splitTraced encoding bytes).run state)
      (fun one two => one.1 = two.1 ∧ SplitCaches encoding one.2 two.2) := by
  rw [randomOracle.run_eq]
  have cached := agree bytes
  cases classified : encoding.classify bytes with
  | inl call =>
      rw [splitTraced_inl encoding classified, onSecond_run]
      rw [classified] at cached
      change cache bytes = state.2 call at cached
      simp only [rowImpl, StateT.run_mk]
      cases fresh : state.2 call with
      | some answer =>
          rw [cached, fresh]
          rw [lazy_some fresh]
          simp only [map_pure]
          exact relTriple_pure_pure ⟨rfl, agree⟩
      | none =>
          rw [cached, fresh]
          rw [lazy_none fresh]
          simp only [map_bind, map_pure]
          refine relTriple_fresh fun answer => ⟨rfl, fun other => ?_⟩
          by_cases same : other = bytes
          · subst same
            rw [QueryCache.cacheQuery_self, classified]
            simp
          · rw [QueryCache.cacheQuery_of_ne _ _ same, agree other]
            cases otherClassified : encoding.classify other with
            | inl otherCall =>
                have distinct : otherCall ≠ call := fun equal => same
                  (encoding.classify_injective (otherClassified.trans (equal ▸ classified.symm)))
                simp [Function.update_of_ne distinct]
            | inr input => rfl
  | inr input =>
      rw [splitTraced_inr encoding classified, onFirst_run, traced_run]
      rw [classified] at cached
      change cache bytes = state.1.cache input at cached
      cases fresh : state.1.cache input with
      | some answer =>
          rw [cached, fresh]
          simp only [map_pure]
          exact relTriple_pure_pure ⟨rfl, agree⟩
      | none =>
          rw [cached, fresh]
          simp only [map_bind, map_pure]
          refine relTriple_fresh fun answer => ⟨rfl, fun other => ?_⟩
          by_cases same : other = bytes
          · subst same
            rw [QueryCache.cacheQuery_self, classified]
            simp
          · rw [QueryCache.cacheQuery_of_ne _ _ same, agree other]
            cases otherClassified : encoding.classify other with
            | inl otherCall => rfl
            | inr otherInput =>
                have distinct : otherInput ≠ input := fun equal => same
                  (encoding.classify_injective (otherClassified.trans (equal ▸ classified.symm)))
                simp [Trace.record_cache, Function.update_of_ne distinct]

/-- The lazy random oracle on bytes answers every computation as the split oracle does. -/
theorem split_coupling {α : Type} (computation : OracleComp (ByteHash S) α) :
    RelTriple ((simulateQ randomOracle computation).run' ∅)
      ((simulateQ (splitTraced encoding) computation).run (Trace.empty, fun _ => none))
      (fun one two => one = two.1) := by
  have coupled := OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run
    (randomOracle (spec := ByteHash S)) (splitTraced encoding) (SplitCaches encoding) computation
    (fun bytes cache state agree => split_step encoding bytes cache state agree) ∅
    (Trace.empty, fun _ => none) (fun bytes => by
      cases encoding.classify bytes <;> rfl)
  rw [StateT.run'_eq, ← id_map ((simulateQ (splitTraced encoding) computation).run
    (Trace.empty, fun _ => none))]
  exact relTriple_map (relTriple_post_mono coupled fun _ _ related => related.1)

end Split

section AdversaryPhase
variable (encoding : Encoding E Shape S Query) (width : ℕ)

/-- One byte call against the lazy joint simulation: equal answers and agreeing successors, unless
the call raises the bad flag. -/
theorem split_adversary_step (bytes : Bytes)
    (first : Trace (Absorbed E Shape S) S Bytes × (Query → Option S))
    (second : Simulated (Absorbed E Shape S) S Bytes width × (Query → Option S))
    (related : Agrees width first.1 second.1 ∧ first.2 = second.2) :
    RelTriple ((splitTraced encoding bytes).run first) ((splitSimulator encoding width bytes).run second)
      (fun one two => one.2.1.bad = true ∨
        (one.1 = two.1 ∧ Agrees width one.2.1 two.2.1 ∧ one.2.2 = two.2.2)) := by
  obtain ⟨agrees, rows⟩ := related
  cases classified : encoding.classify bytes with
  | inl call =>
      rw [splitTraced_inl encoding classified, splitSimulator_inl encoding width classified,
        onSecond_run, onSecond_run, rows]
      refine relTriple_map (relTriple_post_mono (relTriple_refl _) ?_)
      rintro one two rfl
      exact Or.inr ⟨rfl, agrees, rfl⟩
  | inr input =>
      rw [splitTraced_inr encoding classified, splitSimulator_inr encoding width classified,
        onFirst_run, onFirst_run, rows]
      refine relTriple_map (relTriple_post_mono (adversary_step input first.1 second.1 agrees) ?_)
      rintro one two (bad | ⟨same, agreement⟩)
      · exact Or.inl bad
      · exact Or.inr ⟨same, agreement, rfl⟩

theorem splitTraced_bad_mono (bytes : Bytes)
    (state : Trace (Absorbed E Shape S) S Bytes × (Query → Option S)) (isBad : state.1.bad = true) :
    ∀ result ∈ support ((splitTraced encoding bytes).run state), result.2.1.bad = true := by
  intro result member
  cases classified : encoding.classify bytes with
  | inl call =>
      rw [splitTraced_inl encoding classified, onSecond_run, support_map] at member
      obtain ⟨inner, -, rfl⟩ := member
      exact isBad
  | inr input =>
      rw [splitTraced_inr encoding classified] at member
      obtain ⟨inner, innerMember, rfl⟩ := onFirst_support member
      exact traced_bad_mono input state.1 isBad inner innerMember

/-- The adversary's run against the split oracle and against the lazy joint simulation, from
agreeing states: equal results and agreeing states, unless the trace raises the bad flag. -/
theorem adversary_coupling {α : Type} (computation : OracleComp (ByteHash S) α)
    (first : Trace (Absorbed E Shape S) S Bytes × (Query → Option S))
    (second : Simulated (Absorbed E Shape S) S Bytes width × (Query → Option S))
    (related : first.1.bad = true ∨ (Agrees width first.1 second.1 ∧ first.2 = second.2)) :
    RelTriple ((simulateQ (splitTraced encoding) computation).run first)
      ((simulateQ (splitSimulator encoding width) computation).run second)
      (fun one two => one.2.1.bad = true ∨
        (one.1 = two.1 ∧ Agrees width one.2.1 two.2.1 ∧ one.2.2 = two.2.2)) :=
  relTriple_simulateQ_run (splitTraced encoding) (splitSimulator encoding width)
    (fun state => state.1.bad = true)
    (fun one two => Agrees width one.1 two.1 ∧ one.2 = two.2)
    (fun bytes state isBad => splitTraced_bad_mono encoding bytes state isBad)
    (fun bytes one two related _ => split_adversary_step encoding width bytes one two related)
    computation first second related

/-- A run against the split oracle from a bad trace ends bad. -/
theorem split_persists {α : Type} (computation : OracleComp (ByteHash S) α)
    (state : Trace (Absorbed E Shape S) S Bytes × (Query → Option S)) (isBad : state.1.bad = true) :
    ∀ result ∈ support ((simulateQ (splitTraced encoding) computation).run state),
      result.2.1.bad = true :=
  support_bad (splitTraced encoding) (fun state => state.1.bad = true)
    (fun bytes state isBad => splitTraced_bad_mono encoding bytes state isBad) computation state isBad

end AdversaryPhase

section Flag
variable [Fintype S] (encoding : Encoding E Shape S Query)

/-- A byte call raises the flag with probability at most the record's length over the number of
digests, and only at a chain input. -/
theorem splitTraced_step_bad_le (bytes : Bytes)
    (state : Trace (Absorbed E Shape S) S Bytes × (Query → Option S)) (good : state.1.bad = false) :
    Pr{let result ← (splitTraced encoding bytes).run state}[result.2.1.bad = true] ≤
      (state.1.seen.length : ENNReal) / Fintype.card S := by
  cases classified : encoding.classify bytes with
  | inl call =>
      rw [splitTraced_inl encoding classified, onSecond_run, prEvent_map]
      simp only [good, Bool.false_eq_true]
      simp
  | inr input =>
      rw [splitTraced_inr encoding classified, onFirst_run, prEvent_map]
      exact traced_step_bad_le input state.1 good

omit [Fintype S] in
theorem splitTraced_seen_length (bytes : Bytes)
    (state : Trace (Absorbed E Shape S) S Bytes × (Query → Option S)) :
    ∀ result ∈ support ((splitTraced encoding bytes).run state),
      result.2.1.seen.length ≤ state.1.seen.length + 2 := by
  intro result member
  cases classified : encoding.classify bytes with
  | inl call =>
      rw [splitTraced_inl encoding classified, onSecond_run, support_map] at member
      obtain ⟨inner, -, rfl⟩ := member
      exact Nat.le_add_right _ _
  | inr input =>
      rw [splitTraced_inr encoding classified] at member
      obtain ⟨inner, innerMember, rfl⟩ := onFirst_support member
      exact traced_seen_length input state.1 inner innerMember

/-- At most `calls` byte calls raise the flag with probability at most
`calls * (seen + calls) / |S|`. -/
theorem split_bad_le {α : Type} (computation : OracleComp (ByteHash S) α) :
    ∀ (calls : ℕ) (state : Trace (Absorbed E Shape S) S Bytes × (Query → Option S)),
      IsTotalQueryBound computation calls → state.1.bad = false →
      Pr{let result ← (simulateQ (splitTraced encoding) computation).run state}[
        result.2.1.bad = true] ≤
        ((calls * (state.1.seen.length + calls) : ℕ) : ENNReal) / Fintype.card S := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro calls state _ good
      simp [good]
  | query_bind bytes next ih =>
      intro calls state bounded good
      obtain ⟨positive, rest⟩ := isTotalQueryBound_query_bind_iff.mp bounded
      obtain ⟨remaining, rfl⟩ : ∃ remaining, calls = remaining + 1 :=
        ⟨calls - 1, (Nat.succ_pred_eq_of_pos positive).symm⟩
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      refine (prEvent_bind_le_prEvent_add_of_support _ _ (fun result => result.2.1.bad = true) _
        (ε := ((remaining * (state.1.seen.length + 2 + remaining) : ℕ) : ENNReal) /
          Fintype.card S) fun step member quiet => ?_).trans ?_
      · have stepGood : step.2.1.bad = false := by simpa using quiet
        refine (ih step.1 remaining step.2 (by simpa using rest step.1) stepGood).trans ?_
        gcongr
        have := splitTraced_seen_length encoding bytes state step member
        omega
      · refine (add_le_add_left (splitTraced_step_bad_le encoding bytes state good) _).trans ?_
        rw [ENNReal.div_add_div_same, ← Nat.cast_add]
        gcongr
        nlinarith

end Flag

section Lifts

omit [DecidableEq E] [DecidableEq Shape] [DecidableEq S] [DecidableEq Query] [SampleableType S] in
theorem absorbAll_onFirst {σ τ : Type} (step : Input (Absorbed E Shape S) S Bytes → StateT σ ProbComp S) :
    ∀ (events : List (Absorbed E Shape S)) (state : S) (first : σ) (second : τ),
      (absorbAll (fun input => onFirst (τ := τ) (step input)) state events).run (first, second) =
        (fun result => (result.1, (result.2, second))) <$> (absorbAll step state events).run first
  | [], _, _, _ => by simp [absorbAll]
  | event :: rest, state, first, second => by
      simp only [absorbAll, StateT.run_bind, onFirst_run, bind_map_left, map_bind]
      exact bind_congr fun next => absorbAll_onFirst step rest next.1 next.2 second

omit [DecidableEq E] [DecidableEq Shape] [DecidableEq S] [DecidableEq Query] [SampleableType S] in
/-- A hash call's query logged on the joint oracle, stated at the hash value type at which
`hashCall` asks it. -/
theorem withQueryLog_hashQuery {width : ℕ} (query : Query) :
    (liftM ((joint (fun _ : E => Fin width → S) Shape S Query).query (.inr query)) :
        OracleComp (joint (fun _ : E => Fin width → S) Shape S Query) S).withQueryLog =
      (liftM ((joint (fun _ : E => Fin width → S) Shape S Query).query (.inr query)) :
          OracleComp (joint (fun _ : E => Fin width → S) Shape S Query) S) >>= fun answer =>
        pure (answer, [⟨.inr query, answer⟩]) :=
  withQueryLog_query _

omit [DecidableEq E] [DecidableEq Shape] [DecidableEq S] [DecidableEq Query] [SampleableType S] in
/-- A hash computation logged on the joint oracle is the computation logged, its entries read as
hash cells. -/
theorem withQueryLog_liftHash {width : ℕ} {α : Type} :
    ∀ computation : OracleComp (Query →ₒ S) α,
      (liftHash (fun _ : E => Fin width → S) Shape computation).withQueryLog =
        (fun result => (result.1, result.2.map (hashEntry (E := E) (Shape := Shape) (width := width)))) <$>
          liftHash (fun _ : E => Fin width → S) Shape computation.withQueryLog := by
  intro computation
  induction computation using OracleComp.inductionOn with
  | pure value => simp [liftHash]
  | query_bind query next ih =>
      simp only [liftHash, simulateQ_bind, simulateQ_spec_query, hashCall] at ih ⊢
      rw [withQueryLog_bind, withQueryLog_hashQuery, withQueryLog_bind, withQueryLog_query]
      simp only [bind_assoc, pure_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_map,
        map_bind]
      refine bind_congr fun answer => ?_
      rw [ih answer]
      simp only [Functor.map_map]
      refine congrArg (fun function => function <$> _) (funext fun result => ?_)
      simp [hashEntry]

/-- The lazy joint oracle answers a hash computation lifted to the joint oracle from the table of
hash calls. -/
theorem simulateQ_lazyJoint_liftHash (width : ℕ) {α : Type} (computation : OracleComp (Query →ₒ S) α) :
    simulateQ (lazyJoint (E := E) (Shape := Shape) width)
        (liftHash (fun _ : E => Fin width → S) Shape computation) =
      simulateQ (fun call => onSecond (rowImpl call)) computation := by
  rw [liftHash, ZkcSecurity.Oracle.simulateQ_simulateQ]
  refine congrArg (fun impl => simulateQ impl computation) (funext fun query => ?_)
  exact simulateQ_spec_query (impl := lazyJoint (E := E) (Shape := Shape) width) (Sum.inr query)

end Lifts

section VerifierPhase
variable (encoding : Encoding E Shape S Query) (width : ℕ)
  (absorb : Typed.Interface J E P (fun _ => Fin width → S)) (scheme : Extractable Shape Value Query S)

/-- The deployed reading against the split oracle is the reading with chain inputs answered by
the traced oracle and hash calls by their own table. -/
theorem chainRead_split (small : width ≤ 2 ^ 64) (process : PIR.Proc (committed J Shape Value) A)
    (state : S) (history : List (Absorbed E Shape S)) (roots : List (Shape × S))
    (messages : List (Message P S)) (openings : List (Opening Value S)) :
    simulateQ (splitTraced encoding)
        (chainRead absorb scheme (byteChain encoding) (byteHash encoding) process state history roots
          messages openings) =
      chainRead absorb scheme (fun input => onFirst (traced input)) (fun call => onSecond (rowImpl call))
        process state history roots messages openings := by
  rw [simulateQ_chainRead]
  have hashes : (fun call => simulateQ (splitTraced encoding) (byteHash encoding call)) =
      fun call => onSecond (rowImpl call) := by
    funext call
    simp only [byteHash, byteCall, simulateQ_spec_query]
    exact splitTraced_inl encoding (encoding.classify_callBytes call)
  rw [hashes]
  refine chainRead_congr absorb scheme _ (fun input read => ?_) process state history roots messages
    openings
  simp only [byteChain, byteCall, simulateQ_spec_query]
  exact splitTraced_inr encoding (encoding.classify_chainBytes (read.toCall small))

theorem chainVerify_split (small : width ≤ 2 ^ 64) (verifier : PIR.Proc (committed J Shape Value) A)
    (initial : List (Absorbed E Shape S)) (roots : List (Shape × S)) (messages : List (Message P S))
    (openings : List (Opening Value S)) :
    simulateQ (splitTraced encoding)
        (chainVerify absorb scheme (byteChain encoding) (byteHash encoding) verifier initial roots
          messages openings) =
      chainVerify absorb scheme (fun input => onFirst (traced input))
        (fun call => onSecond (rowImpl call)) verifier initial roots messages openings := by
  rw [simulateQ_chainVerify]
  have hashes : (fun call => simulateQ (splitTraced encoding) (byteHash encoding call)) =
      fun call => onSecond (rowImpl call) := by
    funext call
    simp only [byteHash, byteCall, simulateQ_spec_query]
    exact splitTraced_inl encoding (encoding.classify_callBytes call)
  rw [hashes]
  refine chainVerify_congr absorb scheme _ (fun input read => ?_) verifier initial roots messages
    openings
  simp only [byteChain, byteCall, simulateQ_spec_query]
  exact splitTraced_inr encoding (encoding.classify_chainBytes (read.toCall small))

include encoding in
/-- The reading against the traced oracle from a bad trace ends bad. -/
theorem chainRead_persists (small : width ≤ 2 ^ 64) (process : PIR.Proc (committed J Shape Value) A)
    (state : S) (history : List (Absorbed E Shape S)) (roots : List (Shape × S))
    (messages : List (Message P S)) (openings : List (Opening Value S))
    (first : Trace (Absorbed E Shape S) S Bytes × (Query → Option S)) (isBad : first.1.bad = true) :
    ∀ result ∈ support ((chainRead absorb scheme (fun input => onFirst (traced input))
        (fun call => onSecond (rowImpl call)) process state history roots messages openings).run first),
      result.2.1.bad = true := by
  rw [← chainRead_split encoding width absorb scheme small]
  exact split_persists encoding _ first isBad

include encoding in
/-- The verifier's reading against the traced oracle and its joint-oracle reading against the
lazy joint oracle return the same outcome and log, unless the trace raises the bad flag. -/
theorem read_coupling (small : width ≤ 2 ^ 64) :
    ∀ (process : PIR.Proc (committed J Shape Value) A) (state : S) (history : List (Absorbed E Shape S))
      (roots : List (Shape × S)) (messages : List (Message P S)) (openings : List (Opening Value S))
      (trace : Trace (Absorbed E Shape S) S Bytes) (tables : Simulated (Absorbed E Shape S) S Bytes width)
      (rows : Query → Option S),
      trace.bad = true ∨ (Consistent width trace tables ∧ chainState trace.cache history = some state) →
      RelTriple ((chainRead absorb scheme (fun input => onFirst (traced input))
          (fun call => onSecond (rowImpl call)) process state history roots messages openings).run
            (trace, rows))
        ((simulateQ (lazyJoint width)
          ((run absorb scheme process history roots messages openings).withQueryLog)).run (tables, rows))
        (fun one two => one.2.1.bad = true ∨ one.1 = two.1) := by
  intro process
  induction process with
  | done value =>
      intro _ _ _ _ _ _ _ _ _
      simp only [chainRead, run, withQueryLog_pure, simulateQ_pure, StateT.run_pure]
      exact relTriple_pure_pure (Or.inr rfl)
  | halt stop =>
      intro _ _ _ _ _ _ _ _ _
      simp only [chainRead, run, withQueryLog_pure, simulateQ_pure, StateT.run_pure]
      exact relTriple_pure_pure (Or.inr rfl)
  | call operation next ih =>
      intro state history roots messages openings trace tables rows start
      by_cases isBad : trace.bad = true
      · exact relTriple_of_left fun one member _ => Or.inl
          (chainRead_persists encoding width absorb scheme small _ state history roots messages
            openings (trace, rows) isBad one member)
      obtain ⟨consistent, reached⟩ := start.resolve_left isBad
      cases operation with
      | base operation =>
          rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
            ⟨event, decode⟩ | _
          · rcases messages with _ | ⟨message | root, rest⟩
            · simp only [chainRead, run, absorbed, withQueryLog_pure, simulateQ_pure, StateT.run_pure]
              exact relTriple_pure_pure (Or.inr rfl)
            · simp only [chainRead, run, absorbed]
              cases recover (event message) with
              | none =>
                  simp only [withQueryLog_pure, simulateQ_pure, StateT.run_pure]
                  exact relTriple_pure_pure (Or.inr rfl)
              | some value =>
                  simp only [StateT.run_bind, onFirst_run, bind_map_left]
                  refine relTriple_bind_left fun step member => ?_
                  rcases absorb_support consistent reached _ step member with
                    stepBad | ⟨consistent', reached'⟩
                  · exact ih value _ _ _ _ _ _ _ _ (Or.inl stepBad)
                  · exact ih value _ _ _ _ _ _ _ _ (Or.inr ⟨consistent', reached'⟩)
            · simp only [chainRead, run, absorbed, withQueryLog_pure, simulateQ_pure, StateT.run_pure]
              exact relTriple_pure_pure (Or.inr rfl)
          · simp only [chainRead, run, absorbed, StateT.run_bind, onFirst_run, bind_map_left]
            refine relTriple_bind_left fun step member => ?_
            rcases absorb_support consistent reached _ step member with
              stepBad | ⟨consistent', reached'⟩
            · exact ih value _ _ _ _ _ _ _ _ (Or.inl stepBad)
            · exact ih value _ _ _ _ _ _ _ _ (Or.inr ⟨consistent', reached'⟩)
          · simp only [chainRead, run, absorbed, withQueryLog_bind, withQueryLog_query, bind_assoc,
              pure_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
            rw [collect_onFirst]
            change RelTriple (((fun result => (result.1, (result.2, rows))) <$>
                (collect width fun block => traced (.request state (.event event) block.val)).run
                  trace) >>= _)
              ((onFirst (historyAnswer width (chainKey (history, event)))).run (tables, rows) >>= _) _
            rw [onFirst_run, bind_map_left]
            -- The continuation logs the cells at the transcript key's answer type, which is
            -- `Fin width → S` only after unfolding `JointRange`.
            rw (config := { transparency := .default }) [bind_map_left]
            refine relTriple_bind (collect_coupling (.event event) width (fun block => block) trace
              tables consistent reached) fun blocks cells ⟨same, consistent', reached'⟩ => ?_
            simp only [onFirst_run, bind_map_left]
            refine relTriple_bind_left fun step member => ?_
            rw [same]
            rcases absorb_support consistent' reached' (.event event) step member with
              stepBad | ⟨consistent'', reached''⟩
            · cases decode cells.1 with
              | none =>
                  simp only [StateT.run_pure, map_pure, simulateQ_pure, withQueryLog_pure]
                  exact relTriple_pure_pure (Or.inl stepBad)
              | some reply =>
                  simp only [StateT.run_map, simulateQ_map]
                  refine relTriple_map (relTriple_post_mono
                    (ih reply _ _ _ _ _ _ _ _ (Or.inl stepBad)) ?_)
                  rintro one two (bad | equal)
                  · exact Or.inl bad
                  · exact Or.inr (by rw [equal]; rfl)
            · cases decode cells.1 with
              | none =>
                  simp only [StateT.run_pure, map_pure, simulateQ_pure, withQueryLog_pure]
                  exact relTriple_pure_pure (Or.inr rfl)
              | some reply =>
                  simp only [StateT.run_map, simulateQ_map]
                  refine relTriple_map (relTriple_post_mono
                    (ih reply _ _ _ _ _ _ _ _ (Or.inr ⟨consistent'', reached''⟩)) ?_)
                  rintro one two (bad | equal)
                  · exact Or.inl bad
                  · exact Or.inr (by rw [equal]; rfl)
          · simp only [chainRead, run, absorbed, withQueryLog_pure, simulateQ_pure, StateT.run_pure]
            exact relTriple_pure_pure (Or.inr rfl)
      | commit shape =>
          rcases messages with _ | ⟨message | root, rest⟩
          · simp only [chainRead, run, withQueryLog_pure, simulateQ_pure, StateT.run_pure]
            exact relTriple_pure_pure (Or.inr rfl)
          · simp only [chainRead, run, withQueryLog_pure, simulateQ_pure, StateT.run_pure]
            exact relTriple_pure_pure (Or.inr rfl)
          · simp only [chainRead, run, StateT.run_bind, onFirst_run, bind_map_left]
            refine relTriple_bind_left fun step member => ?_
            rcases absorb_support consistent reached _ step member with
              stepBad | ⟨consistent', reached'⟩
            · exact ih () _ _ _ _ _ _ _ _ (Or.inl stepBad)
            · exact ih () _ _ _ _ _ _ _ _ (Or.inr ⟨consistent', reached'⟩)
      | read handle position =>
          unfold chainRead run
          split
          · rename_i _ _ shape root opening rest found
            simp only [found, withQueryLog_bind, withQueryLog_liftHash, simulateQ_bind, simulateQ_map,
              simulateQ_lazyJoint_liftHash, StateT.run_bind, StateT.run_map, bind_map_left,
              simulateQ_onSecond]
            refine relTriple_bind (relTriple_refl _) fun first second same => ?_
            cases same
            cases accepted : first.1.1 with
            | false =>
                simp only [StateT.run_pure, withQueryLog_pure, simulateQ_pure, map_pure]
                exact relTriple_pure_pure (Or.inr (by simp [Prod.map]))
            | true =>
                simp only [StateT.run_map]
                refine relTriple_map (relTriple_post_mono
                  (ih opening.value state history roots messages rest trace tables first.2
                    (Or.inr ⟨consistent, reached⟩)) ?_)
                rintro one two (bad | equal)
                · exact Or.inl bad
                · exact Or.inr (by rw [equal]; simp [Prod.map])
          · simp only [withQueryLog_pure, simulateQ_pure, StateT.run_pure]
            exact relTriple_pure_pure (Or.inr rfl)

end VerifierPhase

section Experiments
variable (encoding : Encoding E Shape S Query) (width : ℕ)
  (absorb : Typed.Interface J E P (fun _ => Fin width → S)) (scheme : Extractable Shape Value Query S)
  (verifier : Stmt → PIR.Proc (committed J Shape Value) A) (initial : Stmt → List (Absorbed E Shape S))
  (statementRoots : Stmt → List (Shape × S))

/-- The verifier's joint-oracle reading, logged. -/
def jointReading (statement : Stmt) (proof : Proof P Value S) :
    OracleComp (OracleSpec.ofFn (Cells E Shape S Query width))
      (PIR.Outcome A × QueryLog (OracleSpec.ofFn (Cells E Shape S Query width))) :=
  (run absorb scheme (verifier statement) (initial statement) (statementRoots statement) proof.messages
    proof.openings).withQueryLog

/-- The lazily sampled joint simulation of the concrete experiment: the logged adversary against
the lazy joint simulation, then the verifier's joint-oracle reading against the lazy joint
oracle. -/
noncomputable def lazyExperiment (adversary : OracleComp (ByteHash S) (Stmt × Proof P Value S)) :
    ProbComp (JointRun Stmt P Value S A (QueryLog (OracleSpec.ofFn (Cells E Shape S Query width)))) := do
  let started ← (simulateQ (splitSimulator encoding width) adversary.withQueryLog).run
    (Simulated.empty width, fun _ => none)
  let verifierRun ← (simulateQ (lazyJoint width) (jointReading width absorb scheme verifier initial
    statementRoots started.1.1.1 started.1.1.2)).run' started.2
  pure (assemble encoding width started.1 verifierRun)

omit [DecidableEq E] [DecidableEq Shape] [DecidableEq S] [DecidableEq Query] [SampleableType S] in
/-- The concrete experiment makes at most the adversary's calls plus the deployed verifier's. -/
theorem concreteExperiment_queryBound [DecidableEq E] [DecidableEq Shape] [DecidableEq S]
    [DecidableEq Query] (adversary : OracleComp (ByteHash S) (Stmt × Proof P Value S)) {calls : ℕ}
    (bounded : IsTotalQueryBound adversary calls) (verifierCalls : ℕ)
    (verifierBound : ∀ statement proof, IsTotalQueryBound
      (deployed encoding width absorb scheme verifier initial statementRoots statement proof)
      verifierCalls) :
    IsTotalQueryBound (concreteExperiment encoding width absorb scheme verifier initial statementRoots
      adversary) (calls + verifierCalls) := by
  refine isTotalQueryBound_bind ((isTotalQueryBound_withQueryLog_iff _ _).mpr bounded) fun claim => ?_
  rw [map_eq_bind_pure_comp]
  have composed := isTotalQueryBound_bind (n₂ := 0)
    (ob := pure ∘ assemble encoding width claim) (verifierBound claim.1.1 claim.1.2) fun _ => trivial
  simpa using composed

/-- The deployed verifier against the split oracle and the joint-oracle reading against the lazy
joint oracle, from agreeing states: equal outcomes and logs, unless the trace raises the bad
flag. -/
theorem deployed_coupling (small : width ≤ 2 ^ 64) (nonempty : ∀ statement, initial statement ≠ [])
    (statement : Stmt) (proof : Proof P Value S) (trace : Trace (Absorbed E Shape S) S Bytes)
    (tables : Simulated (Absorbed E Shape S) S Bytes width) (rows : Query → Option S)
    (consistent : Consistent width trace tables) :
    RelTriple ((simulateQ (splitTraced encoding)
        (deployed encoding width absorb scheme verifier initial statementRoots statement proof)).run
          (trace, rows))
      ((simulateQ (lazyJoint width) (jointReading width absorb scheme verifier initial statementRoots
        statement proof)).run (tables, rows))
      (fun one two => one.2.1.bad = true ∨ one.1 = two.1) := by
  unfold deployed jointReading
  rw [chainVerify_split encoding width absorb scheme small]
  obtain ⟨first, rest, shape⟩ := List.exists_cons_of_ne_nil (nonempty statement)
  rw [shape]
  simp only [chainVerify, StateT.run_bind, onFirst_run, bind_map_left]
  refine relTriple_bind_left fun step member => ?_
  rcases generating_support (input := .bind first) consistent trivial rfl step member with
    stepBad | ⟨consistent', reached'⟩
  · refine relTriple_bind_left fun started startedMember => ?_
    rw [absorbAll_onFirst, support_map] at startedMember
    obtain ⟨inner, innerMember, rfl⟩ := startedMember
    rw [← ZkcSecurity.HashChain.simulateQ_absorbAll traced rest step.1] at innerMember
    exact read_coupling encoding width absorb scheme small _ _ _ _ _ _ _ tables rows
      (Or.inl (traced_persists _ step.2 stepBad inner innerMember))
  · refine relTriple_bind_left fun started startedMember => ?_
    rw [absorbAll_onFirst, support_map] at startedMember
    obtain ⟨inner, innerMember, rfl⟩ := startedMember
    rcases absorbAll_support tables rest [first] step.1 step.2 consistent' reached' inner
        innerMember with startedBad | ⟨consistent'', reached''⟩
    · exact read_coupling encoding width absorb scheme small _ _ _ _ _ _ _ tables rows
        (Or.inl startedBad)
    · exact read_coupling encoding width absorb scheme small _ _ _ _ _ _ _ tables rows
        (Or.inr ⟨consistent'', by simpa using reached''⟩)

/-- The concrete experiment against the split oracle and the lazily sampled joint simulation:
equal runs unless the trace raises the bad flag. -/
theorem experiment_coupling (small : width ≤ 2 ^ 64) (nonempty : ∀ statement, initial statement ≠ [])
    (adversary : OracleComp (ByteHash S) (Stmt × Proof P Value S)) :
    RelTriple ((simulateQ (splitTraced encoding) (concreteExperiment encoding width absorb scheme
        verifier initial statementRoots adversary)).run (Trace.empty, fun _ => none))
      (lazyExperiment encoding width absorb scheme verifier initial statementRoots adversary)
      (fun one two => one.2.1.bad = true ∨ one.1 = two) := by
  unfold concreteExperiment lazyExperiment
  simp only [simulateQ_bind, simulateQ_map, StateT.run_bind, StateT.run_map, StateT.run'_eq,
    bind_map_left]
  refine relTriple_bind (adversary_coupling encoding width adversary.withQueryLog _ _
    (Or.inr ⟨agrees_empty, rfl⟩)) fun one two coupled => ?_
  rcases coupled with oneBad | ⟨same, agrees, rows⟩
  · refine relTriple_of_left fun result member _ => Or.inl ?_
    rw [support_map] at member
    obtain ⟨run, runMember, rfl⟩ := member
    exact split_persists encoding _ one.2 oneBad run runMember
  · rw [same]
    rcases one with ⟨claimOne, trace, rowsOne⟩
    rcases two with ⟨claimTwo, tables, rowsTwo⟩
    simp only at rows agrees
    subst rows
    simp only [bind_pure_comp]
    refine relTriple_map (relTriple_post_mono (deployed_coupling encoding width absorb scheme verifier
      initial statementRoots small nonempty claimTwo.1.1 claimTwo.1.2 trace tables rowsOne
      agrees.toConsistent) ?_)
    rintro first second (bad | equal)
    · exact Or.inl bad
    · exact Or.inr (by rw [equal])

/-- Any event of the concrete experiment exceeds its probability in the lazily sampled joint
simulation by at most `(q + V)² / |S|`, for an adversary with at most `q` calls of the byte hash
and a deployed verifier with at most `V` calls of every kind. -/
theorem concrete_le_lazy [Fintype S] (small : width ≤ 2 ^ 64)
    (nonempty : ∀ statement, initial statement ≠ [])
    (adversary : OracleComp (ByteHash S) (Stmt × Proof P Value S)) {calls : ℕ}
    (bounded : IsTotalQueryBound adversary calls) (verifierCalls : ℕ)
    (verifierBound : ∀ statement proof, IsTotalQueryBound
      (deployed encoding width absorb scheme verifier initial statementRoots statement proof)
      verifierCalls)
    (event : JointRun Stmt P Value S A (QueryLog (OracleSpec.ofFn (Cells E Shape S Query width))) →
      Prop) :
    Pr{let result ← (simulateQ randomOracle (concreteExperiment encoding width absorb scheme
          verifier initial statementRoots adversary)).run' ∅}[event result] ≤
      Pr{let result ← lazyExperiment encoding width absorb scheme verifier initial
          statementRoots adversary}[event result] +
        (((calls + verifierCalls) * (calls + verifierCalls) : ℕ) : ENNReal) / Fintype.card S := by
  have split_le := prEvent_le_of_relTriple (split_coupling encoding (concreteExperiment encoding width
    absorb scheme verifier initial statementRoots adversary)) (event := event)
    (target := fun result => event result.1) fun one two same holds => by rw [← same]; exact holds
  have lazy_le := prEvent_le_add_bad
    (bad := fun state : Trace (Absorbed E Shape S) S Bytes × (Query → Option S) => state.1.bad = true)
    (R := Eq) (experiment_coupling encoding width absorb scheme verifier initial statementRoots small
      nonempty adversary) (event := event) (target := event) fun one two same holds => same ▸ holds
  have bad_le := split_bad_le encoding (concreteExperiment encoding width absorb scheme verifier
    initial statementRoots adversary) (calls + verifierCalls) (Trace.empty, fun _ => none)
    (concreteExperiment_queryBound encoding width absorb scheme verifier initial statementRoots
      adversary bounded verifierCalls verifierBound) rfl
  refine split_le.trans (lazy_le.trans ?_)
  gcongr
  exact bad_le.trans (le_of_eq (by simp [Trace.empty]))

end Experiments

end ZkcSecurity.HashChain.Joint
