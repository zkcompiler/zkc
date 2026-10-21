module

public import ZkcSecurity.HashChain.Reduction
public import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure
public import ZkcSecurity.FiatShamir.Budget

@[expose] public section

/-! The probability of the bad event and the verifier's primitive calls.

**The bound.** A call raises the flag only when it is fresh, generates a state,
and its uniform answer lands in the record of the trace before it. The record
grows by at most two digests per call: the state the call reads and the state it
generates. Over a computation with at most `calls` primitive calls on every path,
started from a trace whose record has `seen` digests, the flag rises with
probability at most

```text
calls * (seen + calls) / |S|
```

(`traced_bad_le`). From the empty trace this is `calls² / |S|`
(`experiment_bad_le`), and with `|S| = 2^λ` digests it is the
`(q + V)² / 2^λ` of the joint trace of an adversary with `q` calls and a verifier
with `V` calls (`experiment_queryBound`).

**The verifier's calls.** `CallBound` counts the chain verifier's primitive calls
on every path: one per received or sent event and `width + 1` per query (the
counter blocks and the absorption of the occurrence). Binding and absorbing the
initial history adds its length (`chainRun_queryBound`).

**Primitive calls as a metric.** `CallBound` is the path bound of the shared
combinator `Zkc.Transcript.Walk.Bound` without positions that charges each
operation its primitive calls (`callBound_iff`). Primitive calls are a metric of
their own: they follow from a vector budget of queries and messages through the
conversion `(q, m) ↦ (width + 1) q + m` (`callBound_of_counts`).
-/

set_option autoImplicit false

namespace ZkcSecurity.HashChain
open OracleComp OracleSpec ZkcSecurity.FiatShamir

variable {E S X : Type} [DecidableEq E] [DecidableEq S] [DecidableEq X] [SampleableType S]
  [Fintype S]

section Flag

/-- One call raises the flag with probability at most the record's length over
the number of digests. -/
theorem traced_step_bad_le (input : Input E S X) (trace : Trace E S X) (good : trace.bad = false) :
    Pr{let result ← (traced input).run trace}[result.2.bad = true] ≤
      (trace.seen.length : ENNReal) / Fintype.card S := by
  rw [traced_run]
  cases cached : trace.cache input with
  | some answer =>
      simp [good]
  | none =>
      classical
      rw [show (($ᵗ S : ProbComp S) >>= fun answer => pure (answer, trace.record input answer)) =
          (fun answer => (answer, trace.record input answer)) <$> ($ᵗ S : ProbComp S) by
        rw [map_eq_bind_pure_comp]; rfl, prEvent_map]
      calc Pr{let answer ← $ᵗ S}[(trace.record input answer).bad = true]
          ≤ Pr{let answer ← $ᵗ S}[answer ∈ trace.seen] :=
            prEvent_mono _ _ _ fun answer raised => by
              by_cases loud : Generating trace.cache input ∧ answer ∈ trace.seen
              · exact loud.2
              · rw [Trace.record_bad_of_not _ _ loud, good] at raised
                cases raised
        _ = ((Finset.univ.filter fun answer => answer ∈ trace.seen).card : ENNReal) /
              Fintype.card S := SampleableType.prEvent_uniformSample _
        _ ≤ (trace.seen.length : ENNReal) / Fintype.card S := by
            gcongr
            calc (Finset.univ.filter fun answer => answer ∈ trace.seen).card
                = trace.seen.toFinset.card := by congr 1; ext; simp
              _ ≤ trace.seen.length := List.toFinset_card_le _

omit [Fintype S] in
/-- Recording a call adds at most two digests. -/
theorem traced_seen_length (input : Input E S X) (trace : Trace E S X) :
    ∀ result ∈ support ((traced input).run trace),
      result.2.seen.length ≤ trace.seen.length + 2 := by
  intro result member
  rw [traced_run] at member
  cases cached : trace.cache input with
  | some answer =>
      rw [cached] at member
      simp only [support_pure, Set.mem_singleton_iff] at member
      subst member
      simp
  | none =>
      rw [cached] at member
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
      obtain ⟨answer, -, rfl⟩ := member
      have reads : (input.state?.toList).length ≤ 1 := by
        cases input.state? <;> simp
      simp only [Trace.record, List.length_append]
      split
      · simp only [List.length_singleton]
        omega
      · simp only [List.length_nil]
        omega

/-- The record before the `i`-th of `calls` calls has at most `seen + 2 i`
digests, so the flag rises with probability at most
`Σ_{i < calls} (seen + 2 i) / |S| ≤ calls * (seen + calls) / |S|`. -/
theorem traced_bad_le {α : Type} (computation : OracleComp (Primitive E S X) α) :
    ∀ (calls : ℕ) (trace : Trace E S X), IsTotalQueryBound computation calls →
      trace.bad = false →
      Pr{let result ← (simulateQ traced computation).run trace}[result.2.bad = true] ≤
        ((calls * (trace.seen.length + calls) : ℕ) : ENNReal) / Fintype.card S := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro calls trace _ good
      simp [good]
  | query_bind input next ih =>
      intro calls trace bounded good
      obtain ⟨positive, rest⟩ := isTotalQueryBound_query_bind_iff.mp bounded
      obtain ⟨remaining, rfl⟩ : ∃ remaining, calls = remaining + 1 :=
        ⟨calls - 1, (Nat.succ_pred_eq_of_pos positive).symm⟩
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      refine (prEvent_bind_le_prEvent_add_of_support _ _ (fun result => result.2.bad = true) _
        (ε := ((remaining * (trace.seen.length + 2 + remaining) : ℕ) : ENNReal) /
          Fintype.card S) fun step member quiet => ?_).trans ?_
      · have stepGood : step.2.bad = false := by simpa using quiet
        refine (ih step.1 remaining step.2 (by simpa using rest step.1) stepGood).trans ?_
        gcongr
        have := traced_seen_length input trace step member
        omega
      · refine (add_le_add_left (traced_step_bad_le input trace good) _).trans ?_
        rw [ENNReal.div_add_div_same, ← Nat.cast_add]
        gcongr
        nlinarith

end Flag

section Calls
variable {I : PIR.Signature} {P A Stmt : Type} {width : ℕ}

omit [DecidableEq E] [DecidableEq S] [DecidableEq X] [SampleableType S] [Fintype S] in
/-- `count` blocks are `count` calls. -/
theorem collect_queryBound :
    ∀ (count : ℕ) (calls : Fin count → Input E S X),
      IsTotalQueryBound (collect count fun index => call (calls index)) count
  | 0, _ => trivial
  | count + 1, calls => by
      simp only [collect, call]
      refine isTotalQueryBound_query_bind_iff.mpr ⟨Nat.succ_pos _, fun head => ?_⟩
      have tail := isTotalQueryBound_bind (ob := fun tail : Fin count → S =>
        (pure (Fin.cons head tail) : OracleComp (Primitive E S X) (Fin (count + 1) → S)))
        (n₂ := 0) (collect_queryBound count fun index => calls index.succ) fun _ => trivial
      simpa [call] using tail

/-- The chain verifier's primitive calls on every path: one per received or sent
event and `width + 1` per query. -/
def CallBound (absorb : Typed.Interface I E P (Raw E S width)) : PIR.Proc I A → ℕ → Prop
  | .done _, _ => True
  | .halt _, _ => True
  | .call operation next, budget =>
      match absorb operation with
      | .receive _ _ => 0 < budget ∧ ∀ value, CallBound absorb (next value) (budget - 1)
      | .send _ value => 0 < budget ∧ CallBound absorb (next value) (budget - 1)
      | .query _ _ => width + 1 ≤ budget ∧
          ∀ value, CallBound absorb (next value) (budget - (width + 1))
      | .refuse => True

omit [DecidableEq E] [DecidableEq S] [DecidableEq X] [SampleableType S] [Fintype S] in
theorem chainTransform_queryBound (absorb : Typed.Interface I E P (Raw E S width)) :
    ∀ (process : PIR.Proc I A) (budget : ℕ) (state : S) (history : List E) (proof : List P),
      CallBound absorb process budget →
        IsTotalQueryBound (chainTransform (X := X) absorb call process state history proof) budget := by
  intro process
  induction process with
  | done value => intro _ _ _ _ _; trivial
  | halt stop => intro _ _ _ _ _; trivial
  | call operation next ih =>
      intro budget state history proof bounded
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      · simp only [CallBound, absorbed] at bounded
        cases proof with
        | nil => simp only [chainTransform, absorbed]; trivial
        | cons message rest =>
            simp only [chainTransform, absorbed]
            cases recover (event message) with
            | none => trivial
            | some value =>
                exact isTotalQueryBound_query_bind_iff.mpr
                  ⟨bounded.1, fun advanced => ih value _ _ _ _ (bounded.2 value)⟩
      · simp only [CallBound, absorbed] at bounded
        simp only [chainTransform, absorbed]
        exact isTotalQueryBound_query_bind_iff.mpr
          ⟨bounded.1, fun advanced => ih value _ _ _ _ bounded.2⟩
      · simp only [CallBound, absorbed] at bounded
        have enough := bounded.1
        simp only [chainTransform, absorbed]
        refine (isTotalQueryBound_bind (n₂ := 1 + (budget - (width + 1)))
          (collect_queryBound width _) fun raw =>
            isTotalQueryBound_query_bind_iff.mpr ⟨by omega, fun advanced => ?_⟩).mono
              (by omega)
        cases decode raw with
        | none => trivial
        | some value =>
            exact (ih value _ _ _ _ (bounded.2 value)).mono (by omega)
      · simp only [chainTransform, absorbed]
        trivial

omit [DecidableEq E] [DecidableEq S] [DecidableEq X] [SampleableType S] [Fintype S] in
theorem absorbAll_queryBound :
    ∀ (events : List E) (state : S),
      IsTotalQueryBound (absorbAll (X := X) call state events) events.length
  | [], _ => trivial
  | event :: rest, state =>
      isTotalQueryBound_query_bind_iff.mpr ⟨Nat.succ_pos _, fun next =>
        by simpa using absorbAll_queryBound rest next⟩

omit [DecidableEq E] [DecidableEq S] [DecidableEq X] [SampleableType S] [Fintype S] in
/-- Binding and absorbing the initial history adds its length. -/
theorem chainRun_queryBound (absorb : Typed.Interface I E P (Raw E S width))
    (validator : PIR.Proc I A) (initial : List E) (proof : List P) {budget : ℕ}
    (bounded : CallBound absorb validator budget) :
    IsTotalQueryBound (chainRun (X := X) absorb call validator initial proof)
      (initial.length + budget) := by
  cases initial with
  | nil => trivial
  | cons event rest =>
      simp only [chainRun]
      refine isTotalQueryBound_query_bind_iff.mpr ⟨by simp, fun state => ?_⟩
      have composed := isTotalQueryBound_bind (absorbAll_queryBound (X := X) rest state)
        fun started => chainTransform_queryBound (X := X) absorb validator budget started
          (event :: rest) proof bounded
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using composed

omit [DecidableEq E] [DecidableEq S] [DecidableEq X] [SampleableType S] [Fintype S] in
/-- The joint trace has at most the adversary's calls plus the verifier's. -/
theorem experiment_queryBound (absorb : Typed.Interface I E P (Raw E S width))
    (validator : Stmt → PIR.Proc I A) (initial : Stmt → List E)
    (adversary : OracleComp (Primitive E S X) (Stmt × List P)) {adversaryCalls : ℕ}
    (adversaryBound : IsTotalQueryBound adversary adversaryCalls) {verifierCalls : ℕ}
    (budget : Stmt → ℕ) (bounded : ∀ statement, CallBound absorb (validator statement) (budget statement))
    (within : ∀ statement, (initial statement).length + budget statement ≤ verifierCalls) :
    IsTotalQueryBound (experiment absorb validator initial adversary)
      (adversaryCalls + verifierCalls) := by
  refine isTotalQueryBound_bind adversaryBound fun claimed => ?_
  rw [map_eq_bind_pure_comp]
  have composed := isTotalQueryBound_bind (n₂ := 0)
    (ob := pure ∘ fun result => (claimed.1, result))
    ((chainRun_queryBound (X := X) absorb (validator claimed.1) (initial claimed.1) claimed.2
      (bounded claimed.1)).mono (within claimed.1)) fun _ => trivial
  simpa using composed

omit [DecidableEq E] [DecidableEq S] [DecidableEq X] [SampleableType S] [Fintype S] in
/-- The chain verifier's primitive calls per operation: one per received or sent
event, `width + 1` per query, none for a refusal. -/
def callCharge (absorb : Typed.Interface I E P (Raw E S width)) (operation : I.Op) : ℕ :=
  match absorb operation with
  | .receive _ _ => 1
  | .send _ _ => 1
  | .query _ _ => width + 1
  | .refuse => 0

omit [DecidableEq E] [DecidableEq S] [DecidableEq X] [SampleableType S] [Fintype S] in
/-- `CallBound` is the walk without positions charging each operation its
primitive calls. -/
theorem callBound_iff (absorb : Typed.Interface I E P (Raw E S width)) :
    ∀ (process : PIR.Proc I A) (budget : ℕ),
      CallBound absorb process budget ↔
        (absorb.replyWalk (callCharge absorb)).Bound process () budget
  | .done _, _ => Iff.rfl
  | .halt _, _ => Iff.rfl
  | .call operation next, budget => by
      have ih := fun reply => callBound_iff absorb (next reply)
      rw [Zkc.Transcript.Walk.bound_call]
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      all_goals simp only [CallBound, absorbed, Zkc.Transcript.Interface.replyWalk_admits,
        Zkc.Transcript.Interface.replyWalk_charge, Zkc.Transcript.Interface.replyWalk_next,
        callCharge, true_and, true_implies, IsEmpty.forall_iff, implies_true, and_true]
      · constructor
        · rintro ⟨positive, bounded⟩
          exact ⟨budget - 1, by omega, fun reply _ => (ih reply (budget - 1)).mp (bounded reply)⟩
        · rintro ⟨remaining, le, bounded⟩
          exact ⟨by omega, fun reply => (ih reply (budget - 1)).mpr
            (Zkc.Transcript.Walk.Bound.mono _ _ (bounded reply ()) (by omega))⟩
      · constructor
        · rintro ⟨positive, bounded⟩
          exact ⟨budget - 1, by omega, fun reply _ same =>
            same ▸ (ih value (budget - 1)).mp bounded⟩
        · rintro ⟨remaining, le, bounded⟩
          exact ⟨by omega, (ih value (budget - 1)).mpr
            (Zkc.Transcript.Walk.Bound.mono _ _ (bounded value () rfl) (by omega))⟩
      · constructor
        · rintro ⟨enough, bounded⟩
          exact ⟨budget - (width + 1), by omega, fun reply _ =>
            (ih reply (budget - (width + 1))).mp (bounded reply)⟩
        · rintro ⟨remaining, le, bounded⟩
          exact ⟨by omega, fun reply => (ih reply (budget - (width + 1))).mpr
            (Zkc.Transcript.Walk.Bound.mono _ _ (bounded reply ()) (by omega))⟩
      · exact ⟨fun _ => ⟨budget, by omega⟩, fun _ => trivial⟩

/-- Primitive calls from counts of queries and messages: `width + 1` calls per
query and one per message. -/
def callsOfCounts (width : ℕ) : ℕ × ℕ →+ ℕ :=
  (AddMonoidHom.mulLeft (width + 1)).comp (AddMonoidHom.fst ℕ ℕ) + AddMonoidHom.snd ℕ ℕ

omit [DecidableEq E] [DecidableEq S] [DecidableEq X] [SampleableType S] [Fintype S] in
/-- A vector budget of queries and messages bounds the chain verifier's primitive
calls through the conversion `(q, m) ↦ (width + 1) q + m`. -/
theorem callBound_of_counts (absorb : Typed.Interface I E P (Raw E S width))
    (process : PIR.Proc I A) (counts : ℕ × ℕ)
    (counted : (absorb.replyWalk absorb.messageQueryCharge).Bound process () counts) :
    CallBound absorb process (callsOfCounts width counts) := by
  refine (callBound_iff absorb process _).mpr
    (Zkc.Transcript.Walk.Bound.convert _ _ (callsOfCounts width) ?_ (fun _ _ _ => trivial) ?_
      (fun _ _ _ _ step => step) process counted)
  · intro first second le
    simp only [callsOfCounts, AddMonoidHom.add_apply, AddMonoidHom.coe_comp, Function.comp_apply,
      AddMonoidHom.coe_fst, AddMonoidHom.coe_snd, AddMonoidHom.coe_mulLeft]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ le.1) le.2
  · intro position operation
    simp only [Zkc.Transcript.Interface.replyWalk_charge, callCharge,
      Zkc.Transcript.Interface.messageQueryCharge]
    cases absorb operation <;> simp [callsOfCounts]

end Calls

section Experiments
variable {I : PIR.Signature} {P A Stmt : Type} {width : ℕ}

/-- From the empty trace, at most `calls` calls raise the flag with probability
at most `calls² / |S|`. -/
theorem experiment_bad_le (absorb : Typed.Interface I E P (Raw E S width))
    (validator : Stmt → PIR.Proc I A) (initial : Stmt → List E)
    (adversary : OracleComp (Primitive E S X) (Stmt × List P)) {calls : ℕ}
    (bounded : IsTotalQueryBound (experiment absorb validator initial adversary) calls) :
    Pr{let result ← ((simulateQ traced (experiment absorb validator initial adversary)).run
        Trace.empty)}[result.2.bad = true] ≤ ((calls * calls : ℕ) : ENNReal) / Fintype.card S := by
  simpa [Trace.empty] using traced_bad_le _ calls Trace.empty bounded rfl

/-- The concrete experiment exceeds the simulated experiment by at most
`(q + V)² / |S|` for an adversary with at most `q` primitive calls and a verifier
with at most `V`, initialization included. -/
theorem concrete_le_simulated (absorb : Typed.Interface I E P (Raw E S width))
    (validator : Stmt → PIR.Proc I A) (initial : Stmt → List E)
    (nonempty : ∀ statement, initial statement ≠ [])
    (adversary : OracleComp (Primitive E S X) (Stmt × List P)) {adversaryCalls : ℕ}
    (adversaryBound : IsTotalQueryBound adversary adversaryCalls) {verifierCalls : ℕ}
    (budget : Stmt → ℕ) (bounded : ∀ statement, CallBound absorb (validator statement) (budget statement))
    (within : ∀ statement, (initial statement).length + budget statement ≤ verifierCalls)
    (event : Stmt × (PIR.Outcome A × List P) → Prop) :
    Pr{let result ← (simulateQ randomOracle (experiment absorb validator initial adversary)).run' ∅}[
        event result] ≤
      Pr{let result ← simulatedExperiment width absorb validator initial adversary}[event result] +
        (((adversaryCalls + verifierCalls) * (adversaryCalls + verifierCalls) : ℕ) : ENNReal) /
          Fintype.card S :=
  (concrete_le absorb validator initial nonempty adversary event).trans
    (add_le_add_right (experiment_bad_le absorb validator initial adversary
      (experiment_queryBound absorb validator initial adversary adversaryBound budget bounded
        within)) _)

end Experiments

end ZkcSecurity.HashChain
