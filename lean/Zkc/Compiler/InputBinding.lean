import Zkc.Compiler.Refinement

/-! Executable input selection and coverage for an advertised refinement domain.

An implication over related inputs alone permits an empty initial relation.
An input binding supplies an actual partial map, proves it succeeds for the
advertised source domain, and connects its selected result to that relation.
Rejection outside the domain is not a logical protocol stop.
-/

namespace Zkc.Compiler.Refinement

open Zkc.Source

variable {sourceLanguage targetLanguage : Language}
  {source : ExecutionModel sourceLanguage} {target : ExecutionModel targetLanguage}
  {Γ : List sourceLanguage.Ty} {Δ : List targetLanguage.Ty}
  {result : sourceLanguage.Ty} {output : targetLanguage.Ty}

structure InputBinding (relation : Refinement source target Γ Δ result output)
    (admitted : Environment source.meaning.Value Γ → source.State → Prop) where
  bind : Environment source.meaning.Value Γ → source.State →
    Option (Environment target.meaning.Value Δ × target.State)
  covered : ∀ env state, admitted env state → ∃ selected, bind env state = some selected
  valid : ∀ env state selected, admitted env state → bind env state = some selected →
    relation.initial env state selected.1 selected.2

variable {relation : Refinement source target Γ Δ result output}
  {admitted : Environment source.meaning.Value Γ → source.State → Prop}

/-- Apply preservation to the target inputs actually chosen by this binding. -/
theorem InputBinding.selected (binding : InputBinding relation admitted)
    {program : Program sourceLanguage Γ result} {plan : Plan targetLanguage Δ output}
    (correct : relation.Holds program plan)
    (env : Environment source.meaning.Value Γ) (state : source.State)
    (targetInput : Environment target.meaning.Value Δ × target.State)
    (allowed : admitted env state) (chosen : binding.bind env state = some targetInput) :
    PIR.Execution.Relates relation.states relation.values relation.sourceView relation.targetView
      (source.runSource program env state) (target.runPlan plan targetInput.1 targetInput.2) :=
  correct env state targetInput.1 targetInput.2 (binding.valid env state targetInput allowed chosen)

/-- Coverage and refinement together give an execution comparison for every
advertised source input. This still supplies no native progress theorem. -/
theorem InputBinding.realizes (binding : InputBinding relation admitted)
    {program : Program sourceLanguage Γ result} {plan : Plan targetLanguage Δ output}
    (correct : relation.Holds program plan)
    (env : Environment source.meaning.Value Γ) (state : source.State)
    (allowed : admitted env state) :
    ∃ selected, binding.bind env state = some selected ∧
      PIR.Execution.Relates relation.states relation.values relation.sourceView relation.targetView
        (source.runSource program env state) (target.runPlan plan selected.1 selected.2) := by
  obtain ⟨selected, chosen⟩ := binding.covered env state allowed
  exact ⟨selected, chosen, binding.selected correct env state selected allowed chosen⟩

end Zkc.Compiler.Refinement
