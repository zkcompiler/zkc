module

public import VCVio.ProgramLogic.Relational.Basic
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

VCVio's `tvDist_simulateQ_le_probEvent_bad` states this for one shared state
type, with agreement as an equality of step distributions. Here the states
differ, as they do between a random oracle on primitive inputs and a simulator
holding a history oracle, so agreement is a coupling of each step.
-/

set_option autoImplicit false

namespace ZkcSecurity.VCVio.UntilBad
open OracleComp OracleSpec OracleComp.ProgramLogic.Relational

section Couplings
variable {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
  [spec₁.IsUniformSpec] [spec₂.IsUniformSpec]

/-- A postcondition that holds for every left output in the support, against
every right output, relates the two computations. -/
theorem relTriple_of_left {α β : Type} {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {R : RelPost α β} (holds : ∀ a ∈ support oa, ∀ b, R a b) : RelTriple oa ob R := by
  obtain ⟨coupling, -⟩ := relTriple_iff_relWP.1 (relTriple_true oa ob)
  refine relTriple_iff_relWP.2 ⟨coupling, fun pair member => holds pair.1 ?_ pair.2⟩
  have marginal : pair.1 ∈ (Prod.fst <$> coupling.1).support :=
    (spmf_support_map coupling.1 Prod.fst).symm ▸ ⟨pair, member, rfl⟩
  rw [coupling.2.map_fst] at marginal
  exact (mem_support_iff_evalSPMF_apply_ne_zero oa pair.1).2 ((SPMF.mem_support_iff _ _).1 marginal)

/-- A left step whose every outcome relates its continuation to the right
computation relates the composition. -/
theorem relTriple_bind_left {α γ δ : Type} {oa : OracleComp spec₁ α}
    {next : α → OracleComp spec₁ γ} {ob : OracleComp spec₂ δ} {R : RelPost γ δ}
    (holds : ∀ a ∈ support oa, RelTriple (next a) ob R) : RelTriple (oa >>= next) ob R := by
  have composed := relTriple_bind (ob := (pure () : OracleComp spec₂ Unit)) (fb := fun _ => ob)
    (R := fun a _ => a ∈ support oa) (relTriple_of_left fun a member _ => member)
    fun a _ member => holds a member
  simpa only [pure_bind] using composed

set_option linter.deprecated false in
/-- A coupling whose related outputs carry an event implication bounds the
event's probability. -/
theorem prEvent_le_of_relTriple {α β : Type} {oa : ProbComp α} {ob : ProbComp β}
    {R : RelPost α β} (coupled : RelTriple oa ob R) {event : α → Prop} {target : β → Prop}
    (implies : ∀ a b, R a b → event a → target b) :
    Pr{let result ← oa}[event result] ≤ Pr{let result ← ob}[target result] := by
  rw [probOutput_true_eq_probEvent oa event, probOutput_true_eq_probEvent ob target]
  exact probEvent_le_of_relTriple coupled implies

end Couplings

section Simulations
variable {ι : Type} {spec : OracleSpec ι} {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁}
  {spec₂ : OracleSpec ι₂} {σ₁ σ₂ : Type}

/-- A simulation started from a bad state ends bad when no step leaves the bad
states. -/
theorem support_bad (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec₁))) (bad : σ₁ → Prop)
    (mono : ∀ query state, bad state → ∀ result ∈ support ((impl₁ query).run state), bad result.2)
    {α : Type} (computation : OracleComp spec α) :
    ∀ state, bad state → ∀ result ∈ support ((simulateQ impl₁ computation).run state), bad result.2 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro state isBad result member
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact isBad
  | query_bind query next ih =>
      intro state isBad result member
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
        at member
      obtain ⟨step, stepMember, rest⟩ := member
      exact ih step.1 step.2 (mono query state isBad step stepMember) result rest

/-- The coupling of each step, from related states that are not bad, extends to
the whole simulations of any computation. -/
theorem relTriple_simulateQ_run [spec₁.IsUniformSpec] [spec₂.IsUniformSpec]
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
          Or.inl (support_bad impl₁ bad mono _ first isBad result member)
      · have isRelated : related first second := start.resolve_left isBad
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
        refine relTriple_bind (step query first second isRelated isBad) fun one two coupled => ?_
        rcases coupled with oneBad | ⟨same, stillRelated⟩
        · exact relTriple_of_left fun result member _ =>
            Or.inl (support_bad impl₁ bad mono _ one.2 oneBad result member)
        · rw [← same]
          exact ih one.1 one.2 two.2 (Or.inr stillRelated)

set_option linter.deprecated false in
/-- An event of the first output has at most the probability of the matching
event of the second plus the probability that the first ends bad. -/
theorem prEvent_le_add_bad {α β γ : Type}
    {first : ProbComp (α × γ)} {second : ProbComp β} {bad : γ → Prop}
    {R : α → β → Prop}
    (coupled : RelTriple first second (fun one two => bad one.2 ∨ R one.1 two))
    {event : α → Prop} {target : β → Prop} (implies : ∀ a b, R a b → event a → target b) :
    Pr{let result ← first}[event result.1] ≤
      Pr{let result ← second}[target result] + Pr{let result ← first}[bad result.2] := by
  rw [probOutput_true_eq_probEvent first (fun result => event result.1),
    probOutput_true_eq_probEvent second target,
    probOutput_true_eq_probEvent first (fun result => bad result.2)]
  calc Pr[fun result => event result.1 | first]
      ≤ Pr[fun result => (event result.1 ∧ ¬ bad result.2) ∨ bad result.2 | first] :=
        probEvent_mono fun result _ holds => by
          by_cases isBad : bad result.2
          · exact Or.inr isBad
          · exact Or.inl ⟨holds, isBad⟩
    _ ≤ Pr[fun result => event result.1 ∧ ¬ bad result.2 | first] +
          Pr[fun result => bad result.2 | first] := probEvent_or_le _ _ _
    _ ≤ Pr[target | second] + Pr[fun result => bad result.2 | first] := by
        refine add_le_add_left (probEvent_le_of_relTriple coupled ?_) _
        rintro one two (isBad | relatedOutputs) ⟨holds, notBad⟩
        · exact absurd isBad notBad
        · exact implies _ _ relatedOutputs holds

end Simulations

end ZkcSecurity.VCVio.UntilBad
