module

public import ZkcSecurity.Bindings.Transcript.QueryTreeSource.Composition.Typed

@[expose] public section

/-! Interleaved private randomness for the full dependent transcript. Private draws stay fresh;
only transcript cells are cached. Ordered primitive logs are returned as part of the outcome.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace ZkcSecurity.FiatShamir.QueryTreeSource.Composition
open OracleComp OracleSpec MeasureTheory
noncomputable section

/-- The existing finite-continuation mixture construction with a dependent reply family. -/
def privatePrograms {D α : Type} {R : D → Type} [∀ key, Finite (R key)]
    (program : OracleComp (unifSpec + ofFn R) α) : ProbComp (OracleComp (ofFn R) α) := by
  let : ∀ key, Fintype (R key) := fun key ↦ Fintype.ofFinite (R key)
  exact OracleComp.construct (C := fun _ ↦ ProbComp (OracleComp (ofFn R) α))
    (fun value ↦ pure (pure value))
    (fun call _ rest ↦ match call with
      | .inl bound => ProbComp.uniformFin bound >>= rest
      | .inr key => (fun continuations ↦ liftM ((ofFn R).query key) >>= continuations) <$>
          Fintype.mPi rest) program

@[simp] theorem privatePrograms_pure {D α : Type} {R : D → Type}
    [∀ key, Finite (R key)] (value : α) :
    privatePrograms (pure value : OracleComp (unifSpec + ofFn R) α) = pure (pure value) := rfl

@[simp] theorem privatePrograms_uniform_bind {D α : Type} {R : D → Type}
    [∀ key, Finite (R key)] (bound : Nat)
    (next : Fin (bound + 1) → OracleComp (unifSpec + ofFn R) α) :
    privatePrograms (liftM ((unifSpec + ofFn R).query (.inl bound)) >>= next) =
      ProbComp.uniformFin bound >>= fun reply ↦ privatePrograms (next reply) := rfl

@[simp] theorem privatePrograms_oracle_bind {D α : Type} {R : D → Type}
    [∀ key, Finite (R key)] (key : D)
    (next : R key → OracleComp (unifSpec + ofFn R) α) :
    privatePrograms (liftM ((unifSpec + ofFn R).query (.inr key)) >>= next) =
      (fun continuations ↦ liftM ((ofFn R).query key) >>= continuations) <$>
        (letI : Fintype (R key) := Fintype.ofFinite (R key)
         Fintype.mPi (fun reply ↦ privatePrograms (next reply))) := rfl

/-- The mixture preserves the actual stateful execution, not just individual reply marginals. -/
theorem privatePrograms_stateful {D α State : Type} {R : D → Type}
    [∀ key, Finite (R key)] [MeasurableSpace (α × State)]
    (impl : QueryImpl (ofFn R) (StateT State ProbComp))
    (program : OracleComp (unifSpec + ofFn R) α) (state : State) :
    𝒟[(simulateQ (unifSpec.passthrough + impl) program).run state] =
      𝒟[do let fixed ← privatePrograms program; (simulateQ impl fixed).run state] := by
  let : ∀ key, Fintype (R key) := fun key ↦ Fintype.ofFinite (R key)
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp only [privatePrograms_pure, simulateQ_pure, StateT.run_pure, pure_bind]
  | query_bind call next ih =>
    cases call with
    | inl bound =>
      simp only [privatePrograms_uniform_bind, bind_assoc]
      change 𝒟[ProbComp.uniformFin bound >>= fun reply ↦
        (simulateQ (unifSpec.passthrough + impl) (next reply)).run state] = _
      apply evalDist_bind_congr
      intro reply
      exact ih reply state
    | inr key =>
      simp only [privatePrograms_oracle_bind, bind_map_left, simulateQ_bind,
        simulateQ_spec_query, StateT.run_bind]
      rw [OracleComp.evalDist_bind_bind_swap]
      apply evalDist_bind_congr
      intro result
      exact (ih result.1 result.2).trans
        (QueryTree.finiteChoices_coordinate (fun reply ↦ privatePrograms (next reply)) result.1
          (fun fixed ↦ (simulateQ impl fixed).run result.2)).symm

/-- The outer mixture preserves structural bounds on every dependent oracle call.
Every possible reply branch remains budgeted; private draws consume no oracle budget. -/
theorem privatePrograms_queryBound {D α B : Type} {R : D → Type}
    [∀ key, Finite (R key)] (program : OracleComp (unifSpec + ofFn R) α)
    (canQuery : D → B → Prop) (cost : D → B → B) {budget : B}
    (bounded : IsQueryBound program budget
      (Sum.elim (fun _ _ ↦ True) canQuery) (Sum.elim (fun _ remaining ↦ remaining) cost))
    {fixed : OracleComp (ofFn R) α} (sampled : fixed ∈ support (privatePrograms program)) :
    IsQueryBound fixed budget canQuery cost := by
  let : ∀ key, Fintype (R key) := fun key ↦ Fintype.ofFinite (R key)
  induction program using OracleComp.inductionOn generalizing budget fixed with
  | pure value =>
    simp only [privatePrograms_pure, mem_support_pure_iff] at sampled
    subst fixed
    exact isQueryBound_pure _ _ _ _
  | query_bind call next ih =>
    rcases (isQueryBound_query_bind_iff _ _ _ _ _).mp bounded with ⟨allowed, rest⟩
    cases call with
    | inl bound =>
      rw [privatePrograms_uniform_bind, mem_support_bind_iff] at sampled
      obtain ⟨reply, _, member⟩ := sampled
      exact ih reply (rest reply) member
    | inr key =>
      rw [privatePrograms_oracle_bind, support_map] at sampled
      obtain ⟨continuations, member, rfl⟩ := sampled
      refine (isQueryBound_query_bind_iff _ _ _ _ _).mpr ⟨allowed, ?_⟩
      intro reply
      exact ih reply (rest reply) (mem_support_mPi _ _ member reply)

/-- Observe all dependent transcript calls while forwarding each private draw. -/
def logPrivate {D α : Type} {R : D → Type}
    (program : OracleComp (unifSpec + ofFn R) α) :
    OracleComp (unifSpec + ofFn R) (α × QueryLog (ofFn R)) :=
  (simulateQ (unifSpec.passthrough + QueryImpl.withLogging (spec := ofFn R)
    (fun key ↦ liftM ((unifSpec + ofFn R).query (.inr key)) :
      QueryImpl (ofFn R) (OracleComp (unifSpec + ofFn R)))) program).run

variable {carriers : Zkc.Source.Structured.Carriers} {bound height : Nat} [NeZero bound]
local instance (priority := 2000) (α : Type) : DecidableEq α := Classical.decEq α

attribute [local instance] rawSampler otherSampler primitiveSampler macroSampler

/-- Arbitrary interleaved private sampling, with the full dependent request space and cache.
The macro side uses an exact outer mixture, never a fixed or honest private tape. -/
theorem full_interleaved
    [∀ event, SampleableType (Zkc.Construction.Domain.Raw (carriers := carriers) event)]
    (segment : Segment) {α : Type}
    (program : OracleComp (unifSpec + ofFn (Typed.ByLast
      (@Zkc.Construction.Domain.Raw carriers))) α) :
    (simulateQ (unifSpec.passthrough + randomOracle) program).run' ∅ =ᵈ
      (do let fixed ← privatePrograms program
          (simulateQ randomOracle (fullTranslate (bound := bound) (height := height)
            segment fixed)).run' ∅) := by
  let : MeasurableSpace (α × (ofFn (Typed.ByLast
    (@Zkc.Construction.Domain.Raw carriers))).QueryCache) := ⊤
  have joint := EvalDistEq.of_evalDist_eq (privatePrograms_stateful randomOracle program ∅)
  have output := joint.map Prod.fst
  simp only [map_bind, ← StateT.run'_eq] at output
  exact output.trans (EvalDistEq.bind_right _ fun fixed ↦ full_exact segment fixed)

/-- A conservative full primitive budget survives private-mixture conversion and batching. -/
theorem full_interleaved_budget
    [∀ event, SampleableType (Zkc.Construction.Domain.Raw (carriers := carriers) event)]
    (segment : Segment) {α : Type}
    (program : OracleComp (unifSpec + ofFn (Typed.ByLast
      (@Zkc.Construction.Domain.Raw carriers))) α) (budget : Nat)
    (bounded : IsQueryBound program budget
      (Sum.elim (fun _ _ ↦ True) (fun _ remaining ↦ 0 < remaining))
      (Sum.elim (fun _ remaining ↦ remaining) (fun _ remaining ↦ remaining - 1)))
    {fixed : OracleComp (ofFn (Typed.ByLast (@Zkc.Construction.Domain.Raw carriers))) α}
    (sampled : fixed ∈ support (privatePrograms program)) :
    IsTotalQueryBound (fullTranslate (height := height) (bound := bound) segment fixed) budget :=
  full_budget segment fixed budget (privatePrograms_queryBound program _ _ bounded sampled)

/-- Full primitive key/reply logs, including every non-scalar request and repeat, survive
interleaved private draws and heterogeneous macro simulation jointly with the final outcome. -/
theorem full_interleaved_logged
    [∀ event, SampleableType (Zkc.Construction.Domain.Raw (carriers := carriers) event)]
    (segment : Segment) {α : Type}
    (program : OracleComp (unifSpec + ofFn (Typed.ByLast
      (@Zkc.Construction.Domain.Raw carriers))) α) :
    let observed := logPrivate program
    (simulateQ (unifSpec.passthrough + randomOracle) observed).run' ∅ =ᵈ
      (do let fixed ← privatePrograms observed
          (simulateQ randomOracle (fullTranslate (bound := bound) (height := height)
            segment fixed)).run' ∅) := full_interleaved segment _

end
end ZkcSecurity.FiatShamir.QueryTreeSource.Composition
