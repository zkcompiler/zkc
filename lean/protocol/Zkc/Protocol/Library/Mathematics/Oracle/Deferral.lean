module

public import VCVio.ProgramLogic.Relational.Basic
public import VCVio.OracleComp.SimSemantics.StateT.Basic
public import VCVio.OracleComp.QueryTracking.QueryBound
public import VCVio.EvalDist.Monad.UniformTable
public import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

@[expose] public section

/-! Deferred sampling for stateful simulations.

Two simulations of one computation differ only in when they sample: the second
holds in its state values that the first samples later, when it first reads
them. A kernel `fill` completes a state of the first simulation into a state of
the second by sampling the values the first has not read yet. If one step of the
second simulation after filling has the same law as one step of the first
followed by filling (`commute`), then so do the whole simulations of every
computation (`evalDistEq_simulateQ_fill`). Steps need to commute only from states
satisfying an invariant indexed by the remaining queries, which bounds the
values the fill must provide.
-/

set_option autoImplicit false

namespace ZkcSecurity.VCVio.Deferral
open OracleComp OracleSpec

variable {ι : Type} {spec : OracleSpec ι} {σ₁ σ₂ : Type}

/-- The simulations from a state of the first and from its filling have the same
law, up to filling the first's final state. -/
theorem evalDistEq_simulateQ_fill
    (impl₁ : QueryImpl spec (StateT σ₁ ProbComp)) (impl₂ : QueryImpl spec (StateT σ₂ ProbComp))
    (fill : σ₁ → ProbComp σ₂) (Inv : ℕ → σ₁ → Prop)
    (commute : ∀ (remaining : ℕ) query state, Inv (remaining + 1) state →
      (fill state >>= fun filled => (impl₂ query).run filled) =ᵈ ((impl₁ query).run state >>= fun step => (fun filled => (step.1, filled)) <$> fill step.2))
    (preserve : ∀ (remaining : ℕ) query state, Inv (remaining + 1) state →
      ∀ step ∈ support ((impl₁ query).run state), Inv remaining step.2)
    {α : Type} (computation : OracleComp spec α) :
    ∀ (remaining : ℕ) (state : σ₁), IsTotalQueryBound computation remaining → Inv remaining state →
      (fill state >>= fun filled => (simulateQ impl₂ computation).run filled) =ᵈ ((simulateQ impl₁ computation).run state >>= fun result =>
          (fun filled => (result.1, filled)) <$> fill result.2) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro remaining state _ _
      simp only [simulateQ_pure, StateT.run_pure, pure_bind, map_eq_bind_pure_comp,
        Function.comp_def]
      rfl
  | query_bind query next ih =>
      intro remaining state bounded inv
      obtain ⟨positive, rest⟩ := isTotalQueryBound_query_bind_iff.mp bounded
      obtain ⟨left, rfl⟩ : ∃ left, remaining = left + 1 :=
        ⟨remaining - 1, (Nat.succ_pred_eq_of_pos positive).symm⟩
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      calc (fill state >>= fun filled => (impl₂ query).run filled >>= fun step =>
              (simulateQ impl₂ (next step.1)).run step.2)
          =ᵈ ((fill state >>= fun filled => (impl₂ query).run filled) >>= fun step =>
              (simulateQ impl₂ (next step.1)).run step.2) := by rw [bind_assoc]
        _ =ᵈ (((impl₁ query).run state >>= fun step =>
              (fun filled => (step.1, filled)) <$> fill step.2) >>= fun step =>
              (simulateQ impl₂ (next step.1)).run step.2) :=
            (commute left query state inv).bind_left _
        _ =ᵈ ((impl₁ query).run state >>= fun step => fill step.2 >>= fun filled =>
              (simulateQ impl₂ (next step.1)).run filled) := by
            simp only [bind_assoc, bind_map_left]; rfl
        _ =ᵈ ((impl₁ query).run state >>= fun step =>
              (simulateQ impl₁ (next step.1)).run step.2 >>= fun result =>
                (fun filled => (result.1, filled)) <$> fill result.2) :=
            OracleComp.EvalDistEq.bind_congr_of_support _ fun step member =>
              ih step.1 left step.2 (by simpa using rest step.1)
                (preserve left query state inv step member)
        _ =ᵈ _ := by rw [bind_assoc]

/-- An invariant indexed by the remaining queries, kept by every step, holds
after every run within the query bound, for some remaining count. -/
theorem support_simulateQ_invariant (impl : QueryImpl spec (StateT σ₁ ProbComp))
    (Inv : ℕ → σ₁ → Prop)
    (preserve : ∀ (remaining : ℕ) query state, Inv (remaining + 1) state →
      ∀ step ∈ support ((impl query).run state), Inv remaining step.2)
    {α : Type} (computation : OracleComp spec α) :
    ∀ (remaining : ℕ) (state : σ₁), IsTotalQueryBound computation remaining → Inv remaining state →
      ∀ result ∈ support ((simulateQ impl computation).run state),
        ∃ left ≤ remaining, Inv left result.2 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro remaining state _ inv result member
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact ⟨remaining, le_rfl, inv⟩
  | query_bind query next ih =>
      intro remaining state bounded inv result member
      obtain ⟨positive, rest⟩ := isTotalQueryBound_query_bind_iff.mp bounded
      obtain ⟨left, rfl⟩ : ∃ left, remaining = left + 1 :=
        ⟨remaining - 1, (Nat.succ_pred_eq_of_pos positive).symm⟩
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
        at member
      obtain ⟨step, stepMember, restMember⟩ := member
      obtain ⟨final, below, finalInv⟩ := ih step.1 left step.2 (by simpa using rest step.1)
        (preserve left query state inv step stepMember) result restMember
      exact ⟨final, by omega, finalInv⟩

section Flatten
variable {ι' : Type} {spec' : OracleSpec ι'} {τ : Type}

/-- A stateful simulation into oracle computations, run against a stateful
implementation of their oracles, as one stateful simulation. -/
def flatten (inner : QueryImpl spec (StateT σ₁ (OracleComp spec')))
    (outer : QueryImpl spec' (StateT τ ProbComp)) : QueryImpl spec (StateT (σ₁ × τ) ProbComp) :=
  fun query => StateT.mk fun state =>
    (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ outer ((inner query).run state.1)).run state.2

theorem simulateQ_flatten (inner : QueryImpl spec (StateT σ₁ (OracleComp spec')))
    (outer : QueryImpl spec' (StateT τ ProbComp)) {α : Type} (computation : OracleComp spec α) :
    ∀ (state : σ₁) (outerState : τ),
      (simulateQ outer ((simulateQ inner computation).run state)).run outerState =
        (fun result => ((result.1, result.2.1), result.2.2)) <$>
          (simulateQ (flatten inner outer) computation).run (state, outerState) := by
  induction computation using OracleComp.inductionOn with
  | pure value => intro state outerState; simp
  | query_bind query next ih =>
      intro state outerState
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, flatten, StateT.run_mk,
        map_bind, bind_map_left, ih]

end Flatten

section Laws

/-- Resampling one cell of a uniform table with an independent uniform value
keeps the table uniform, whatever is computed from it. -/
theorem evalDistEq_uniform_update {D R α : Type} [Fintype D] [DecidableEq D] [SampleableType R]
    [SampleableType (D → R)] (cell : D) (continuation : (D → R) → ProbComp α) :
    (($ᵗ R) >>= fun value => ($ᵗ (D → R)) >>= fun table =>
        continuation (Function.update table cell value)) =ᵈ (($ᵗ (D → R)) >>= continuation) := by
  let : MeasurableSpace R := ⊤
  let : MeasurableSpace α := ⊤
  exact _root_.EvalDistEq.of_evalDist_eq (evalDist_bind_bind_update ($ᵗ R) ($ᵗ (D → R))
    SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample cell continuation)

end Laws

end ZkcSecurity.VCVio.Deferral
