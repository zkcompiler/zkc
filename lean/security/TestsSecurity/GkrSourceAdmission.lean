import ZkcSecurity.Realizations.Gkr.SourceAdmission
import ZkcExamples.Structured.GkrInputInvocation

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 50000
set_option backward.isDefEq.respectTransparency false

namespace TestsSecurity.GkrSourceAdmission
open Zkc.Source Zkc.Source.Structured
open ZkcExamples.Structured

/-- Complete actual source execution, without challenges at zero width and
zero layers. This is deliberately a concrete control, not producer closure. -/
theorem valid_zero_layers : GkrSourceAdmission.participant (F := ℚ) (G := ℚ)
    [3] [3] [1] [0] 0 0 0 0 = .done (.cons (some true) .nil) := by
  kernel_rfl

theorem false_output_zero_layers : GkrSourceAdmission.participant (F := ℚ) (G := ℚ)
    [3] [4] [1] [0] 0 0 0 0 = .done (.cons (some false) .nil) := by
  kernel_rfl

example : GkrSourceAdmission.participant (F := ℚ) (G := ℚ)
    [] [] [] [] 0 0 5 0 = .halt .reject := by
  simpa only [show 5 < indexLimit by decide, ite_true] using
    GkrSourceAdmission.width_refuses (F := ℚ) (G := ℚ) [] [] [] [] 0 0 5 0 (by decide)

example : GkrSourceAdmission.participant (F := ℚ) (G := ℚ)
    [] [] [] [] 0 0 indexLimit 0 = .halt .refused := by
  simpa only [lt_self_iff_false, ite_false] using
    GkrSourceAdmission.width_refuses (F := ℚ) (G := ℚ) [] [] [] [] 0 0 indexLimit 0 (by decide)

example : GkrSourceAdmission.participant (F := ℚ) (G := ℚ)
    [] [] [] [] 5 0 0 0 = .halt .reject := by
  simpa only [show 5 < indexLimit by decide, ite_true] using
    GkrSourceAdmission.layers_refuses (F := ℚ) (G := ℚ) [] [] [] [] 5 0 0 0 (by decide) (by decide)

example : GkrSourceAdmission.participant (F := ℚ) (G := ℚ)
    [3] [3] [] [1] 0 0 0 0 = .halt .reject :=
  GkrSourceAdmission.zero_add_refuses 3 3 [1] 0

example : GkrSourceAdmission.participant (F := ℚ) (G := ℚ)
    [3] [3] [1] [] 0 0 0 0 = .halt .reject :=
  GkrSourceAdmission.zero_mul_refuses 3 3 1 0

example : GkrSourceAdmission.participant (F := ℚ) (G := ℚ)
    [] [3] [1] [0] 0 0 0 0 = .halt .reject := by
  simpa only [List.length_nil, show 0 < indexLimit by decide, ite_true] using
    GkrSourceAdmission.initial_refuses (F := ℚ) (G := ℚ)
      [] [3] [1] [0] 0 0 0 0 (by decide) (by decide) (by decide)

example : GkrSourceAdmission.participant (F := ℚ) (G := ℚ)
    [3] [] [1] [0] 0 0 0 0 = .halt .reject := by
  simpa only [List.length_nil, show 0 < indexLimit by decide, ite_true] using
    GkrSourceAdmission.outputs_refuse (F := ℚ) (G := ℚ)
      [3] [] [1] [0] 0 0 0 0 (by decide) (by decide) (by decide) (by decide)

example : GkrSourceAdmission.participant (F := ℚ) (G := ℚ)
    [3] [3] [1] [0] 2 0 0 0 = .halt .reject :=
  GkrSourceAdmission.capacity_refuses _ _ _ _ _ _ _ _
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

example : GkrSourceAdmission.participant (F := ℚ) (G := ℚ)
    [3] [3] [] [] 0 64 0 0 = .halt .reject := by
  simpa only [Nat.add_zero, show 64 < indexLimit by decide, ite_true] using
    GkrSourceAdmission.dimensions_refuse (F := ℚ) (G := ℚ)
      [3] [3] [] [] 0 64 0 0 (by decide) (by decide) (by decide) (by decide) (by decide)

example : GkrSourceAdmission.participant (F := ℚ) (G := ℚ)
    [3] [3] [] [] 0 indexLimit 0 0 = .halt .refused := by
  simpa only [Nat.add_zero, lt_self_iff_false, ite_false] using
    GkrSourceAdmission.dimensions_refuse (F := ℚ) (G := ℚ)
      [3] [3] [] [] 0 indexLimit 0 0 (by decide) (by decide) (by decide) (by decide) (by decide)

example : invokeProtocol (GkrSourceViews.unit.plainProtocolTable ℚ ℚ)
    GkrSourceBodies.sourceProtocol80Signature {} 0
    (.cons none (.cons (some []) (.cons (some 3) .nil))) = .halt .incomplete := by
  simpa only [GkrInputNormalForms.verifierProcess, id_eq] using
    GkrInputInvocation.invoke (F := ℚ) (G := ℚ) {} none (some []) (some 3)

example : invokeProtocol (GkrSourceViews.unit.plainProtocolTable ℚ ℚ)
    GkrSourceBodies.sourceProtocol80Signature {} 0
    (.cons (some [3]) (.cons none (.cons (some 3) .nil))) = .halt .incomplete := by
  simpa only [GkrInputNormalForms.verifierProcess, id_eq] using
    GkrInputInvocation.invoke (F := ℚ) (G := ℚ) {} (some [3]) none (some 3)

example : invokeProtocol (GkrSourceViews.unit.plainProtocolTable ℚ ℚ)
    GkrSourceBodies.sourceProtocol80Signature {} 0
    (.cons (some [3]) (.cons (some []) (.cons none .nil))) = .halt .incomplete := by
  simpa only [GkrInputNormalForms.verifierProcess, id_eq] using
    GkrInputInvocation.invoke (F := ℚ) (G := ℚ) {} (some [3]) (some []) none

#print axioms GkrSourceGuards.index_add_all
#print axioms GkrSourceGuards.shape_all
#print axioms GkrSourceGuards.power_bounded
#print axioms GkrSourceAdmission.body
#print axioms GkrSourceAdmission.width_refuses
#print axioms GkrSourceAdmission.layers_refuses
#print axioms GkrSourceAdmission.initial_refuses
#print axioms GkrSourceAdmission.outputs_refuse
#print axioms GkrSourceAdmission.add_refuses
#print axioms GkrSourceAdmission.mul_refuses
#print axioms GkrSourceAdmission.dimensions_refuse
#print axioms GkrSourceAdmission.capacity_refuses
#print axioms ZkcSecurity.Realizations.Gkr.Source.invalid_stops
#print axioms ZkcSecurity.Realizations.Gkr.Source.invalid_verifier_stops
#print axioms ZkcSecurity.Realizations.Gkr.Source.invalid_derivation
#print axioms GkrSourceAdmission.zero_add_refuses
#print axioms GkrSourceAdmission.zero_mul_refuses
#print axioms GkrInputInvocation.invoke
#print axioms valid_zero_layers
#print axioms false_output_zero_layers

end TestsSecurity.GkrSourceAdmission
