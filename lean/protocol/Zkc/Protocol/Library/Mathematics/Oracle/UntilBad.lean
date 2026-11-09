module

public import VCVio.ProgramLogic.Relational.Basic
public import VCVio.ProgramLogic.Relational.SimulateQ.UntilBad
public import VCVio.OracleComp.SimSemantics.StateT.Basic

@[expose] public section

/-! Identical until bad, for two stateful simulations of one computation with
different states.

`impl₁` and `impl₂` simulate the same oracle computation, each with its own
state. A state relation `related` and a bad predicate on the first state, which
no step of `impl₁` leaves, describe a per-query coupling: from related states
that are not bad, the two answers are equal and the next states related, unless
the first next state is bad. Then the two whole simulations are coupled the same
way (`relTriple_simulateQ_run`), and an event of the first simulation's output
has at most the second's probability plus the probability that the first ends
bad (`prEvent_le_add_bad`).

VCVio's `measureETVDist_simulateQ_run'_le_prEvent_bad` states this for one shared state
type, with agreement as an equality of step distributions. Here the states
differ, as they do between a random oracle on primitive inputs and a simulator
holding a history oracle, so agreement is a coupling of each step.
-/

set_option autoImplicit false

namespace ZkcSecurity.VCVio.UntilBad
open OracleComp OracleSpec OracleComp.ProgramLogic.Relational

-- Uniform answer laws imply finite response types; keep this fact local rather
-- than adding a global instance or an extra premise to the coupling theorems.
local instance {ι : Type} {spec : OracleSpec ι} [UniformAnswerMeasure spec] :
    ∀ t, Finite (spec.Range t) := UniformAnswerMeasure.finite_range

section Couplings
variable {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
  [UniformAnswerMeasure spec₁] [UniformAnswerMeasure spec₂]

/-- A postcondition that holds for every left output in the support, against
every right output, relates the two computations. -/
theorem relTriple_of_left {α β : Type} {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {R : RelPost α β} (holds : ∀ a ∈ support oa, ∀ b, R a b) : RelTriple oa ob R := by
  exact relTriple_post_mono
    (relTriple_prod (P := fun a => ∀ b, R a b) (Q := fun _ => True) holds (fun _ _ => trivial))
    (fun {a b} h => h.1 b)

/-- A left step whose every outcome relates its continuation to the right
computation relates the composition. -/
theorem relTriple_bind_left {α γ δ : Type} {oa : OracleComp spec₁ α}
    {next : α → OracleComp spec₁ γ} {ob : OracleComp spec₂ δ} {R : RelPost γ δ}
    (holds : ∀ a ∈ support oa, RelTriple (next a) ob R) : RelTriple (oa >>= next) ob R := by
  have composed := relTriple_bind (ob := (pure () : OracleComp spec₂ Unit)) (fb := fun _ => ob)
    (R := fun a _ => a ∈ support oa) (relTriple_of_left fun a member _ => member)
    fun a _ member => holds a member
  simpa only [pure_bind] using composed

end Couplings

section Simulations
variable {ι : Type} {spec : OracleSpec ι} {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁}
  {spec₂ : OracleSpec ι₂} {σ₁ σ₂ : Type}

/-- The coupling of each step, from related states that are not bad, extends to
the whole simulations of any computation. -/
theorem relTriple_simulateQ_run [UniformAnswerMeasure spec₁] [UniformAnswerMeasure spec₂]
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec₁)))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec₂))) (bad : σ₁ → Prop)
    (related : σ₁ → σ₂ → Prop)
    (mono : ∀ query state, bad state → ∀ result ∈ support ((impl₁ query).run state), bad result.2)
    (step : ∀ query first second, related first second → ¬ bad first →
      RelTriple ((impl₁ query).run first) ((impl₂ query).run second)
        (fun one two => bad one.2 ∨ (one.1 = two.1 ∧ related one.2 two.2)))
    {α : Type} (computation : OracleComp spec α) :
    ∀ first second, bad first ∨ related first second →
      RelTriple ((simulateQ impl₁ computation).run first) ((simulateQ impl₂ computation).run second)
        (fun one two => bad one.2 ∨ (one.1 = two.1 ∧ related one.2 two.2)) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro first second start
      simp only [simulateQ_pure, StateT.run_pure]
      refine relTriple_pure_pure ?_
      rcases start with isBad | isRelated
      · exact Or.inl isBad
      · exact Or.inr ⟨rfl, isRelated⟩
  | query_bind query next ih =>
      intro first second start
      by_cases isBad : bad first
      · exact relTriple_of_left fun result member _ =>
          Or.inl (forall_mem_support_simulateQ_run_of_bad impl₁ bad mono _ isBad result member)
      · have isRelated : related first second := start.resolve_left isBad
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
        refine relTriple_bind (step query first second isRelated isBad) fun one two coupled => ?_
        rcases coupled with oneBad | ⟨same, stillRelated⟩
        · exact relTriple_of_left fun result member _ =>
            Or.inl (forall_mem_support_simulateQ_run_of_bad impl₁ bad mono _ oneBad result member)
        · rw [← same]
          exact ih one.1 one.2 two.2 (Or.inr stillRelated)

/-- An event of the first output has at most the probability of the matching
event of the second plus the probability that the first ends bad. -/
theorem prEvent_le_add_bad {α β γ : Type}
    {first : ProbComp (α × γ)} {second : ProbComp β} {bad : γ → Prop}
    {R : α → β → Prop}
    (coupled : RelTriple first second (fun one two => bad one.2 ∨ R one.1 two))
    {event : α → Prop} {target : β → Prop} (implies : ∀ a b, R a b → event a → target b) :
    Pr{let result ← first}[event result.1] ≤
      Pr{let result ← second}[target result] + Pr{let result ← first}[bad result.2] := by
  calc Pr{let result ← first}[event result.1]
      ≤ Pr{let result ← first}[(event result.1 ∧ ¬ bad result.2) ∨ bad result.2] :=
        prEvent_mono _ _ _ fun result holds => by
          by_cases isBad : bad result.2
          · exact Or.inr isBad
          · exact Or.inl ⟨holds, isBad⟩
    _ ≤ Pr{let result ← first}[event result.1 ∧ ¬ bad result.2] +
          Pr{let result ← first}[bad result.2] := prEvent_or_le _ _ _
    _ ≤ Pr{let x ← second}[target x] + Pr{let result ← first}[bad result.2] := by
        refine add_le_add_left (prEvent_le_of_relTriple coupled ?_) _
        rintro one two (isBad | relatedOutputs) ⟨holds, notBad⟩
        · exact absurd isBad notBad
        · exact implies _ _ relatedOutputs holds

end Simulations

end ZkcSecurity.VCVio.UntilBad
