module

public import ZkcSecurity.Bindings.Gkr.RootEncoding
public import ZkcExamples.Structured.GkrSourceAdmission

@[expose] public section

/-! Exhaustive admission of the actual retained validator. The registered input
predicate fixes the case split; every failure is proved about source execution.
No malformed list or mathematical natural is removed from the runtime domain. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace ZkcSecurity.Realizations.Gkr.Source
open Zkc.Source Zkc.Source.Structured
open ZkcExamples.Structured

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- Invalid raw inputs stop before any challenge. In particular, this theorem
covers unused malformed wiring and every checked-index overflow. -/
theorem invalid_stops (runtime : Invocation F) (invalid : ¬ runtime.Admitted) :
    ∃ reason : PIR.Stop,
      GkrSourceAdmission.participant (G := G) runtime.inputs runtime.outputs runtime.add runtime.mul
        runtime.layers runtime.selector runtime.width runtime.handle = .halt reason := by
  by_cases widthBound : runtime.width ≤ 4
  · by_cases layersBound : runtime.layers ≤ 4
    · by_cases initialShape : runtime.inputs.length = 2 ^ runtime.width
      · by_cases outputShape : runtime.outputs.length = 2 ^ runtime.width
        · by_cases dimensions : runtime.selector + runtime.width + runtime.width + runtime.width < 64
          · by_cases addShape : runtime.add.length =
              2 ^ (runtime.selector + runtime.width + runtime.width + runtime.width)
            · by_cases mulShape : runtime.mul.length =
                2 ^ (runtime.selector + runtime.width + runtime.width + runtime.width)
              · by_cases capacity : runtime.layers ≤ 2 ^ runtime.selector
                · apply False.elim (invalid ?_)
                  refine ⟨⟨initialShape, ?_, ?_, capacity⟩, outputShape, widthBound, layersBound, dimensions⟩
                  · simpa only [Invocation.encoding, ← Nat.pow_add, Nat.add_assoc] using addShape
                  · simpa only [Invocation.encoding, ← Nat.pow_add, Nat.add_assoc] using mulShape
                · exact ⟨.reject, GkrSourceAdmission.capacity_refuses _ _ _ _ _ _ _ _
                    widthBound layersBound initialShape outputShape dimensions addShape mulShape capacity⟩
              · exact ⟨_, GkrSourceAdmission.mul_refuses _ _ _ _ _ _ _ _
                  widthBound layersBound initialShape outputShape dimensions addShape mulShape⟩
            · exact ⟨_, GkrSourceAdmission.add_refuses _ _ _ _ _ _ _ _
                widthBound layersBound initialShape outputShape dimensions addShape⟩
          · exact ⟨_, GkrSourceAdmission.dimensions_refuse _ _ _ _ _ _ _ _
              widthBound layersBound initialShape outputShape dimensions⟩
        · exact ⟨_, GkrSourceAdmission.outputs_refuse _ _ _ _ _ _ _ _
            widthBound layersBound initialShape outputShape⟩
      · exact ⟨_, GkrSourceAdmission.initial_refuses _ _ _ _ _ _ _ _
          widthBound layersBound initialShape⟩
    · exact ⟨_, GkrSourceAdmission.layers_refuses _ _ _ _ _ _ _ _ widthBound (by omega)⟩
  · exact ⟨_, GkrSourceAdmission.width_refuses _ _ _ _ _ _ _ _ (by omega)⟩

end ZkcSecurity.Realizations.Gkr.Source
