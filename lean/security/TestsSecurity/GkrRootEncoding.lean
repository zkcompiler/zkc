module

public import ZkcSecurity.Realizations.Gkr.RootEncoding
public import Mathlib.Data.Rat.Defs

@[expose] public section

/-! Fixed-meaning controls for raw circuit encoding. In particular, the honest
shape policy admits a false output claim and checks unused zero-layer wiring. -/

namespace TestsSecurity.GkrRootEncoding
open ZkcSecurity.Realizations.Gkr

@[simp] def oneLayer : Source.Invocation ℚ := ⟨[3], [6], [1], [0], 1, 0, 0, 0⟩

theorem admitted : oneLayer.Admitted := by simp [Source.Invocation.Admitted, Source.Invocation.encoding, CircuitEncoding.Admitted, CircuitEncoding.Shape]

example : Source.Represents oneLayer.encoding.circuit oneLayer.layers oneLayer.outputTable oneLayer :=
  Source.admitted_represents oneLayer admitted

theorem correct : oneLayer.Correct := by
  refine ⟨by simp [Source.Invocation.encoding, CircuitEncoding.Shape], ?_⟩
  apply congrArg some
  funext bits
  cbv

@[simp] def falseOutput : Source.Invocation ℚ := { oneLayer with outputs := [7] }

theorem false_output_admitted : falseOutput.Admitted := by
  simp [Source.Invocation.Admitted, Source.Invocation.encoding, CircuitEncoding.Admitted, CircuitEncoding.Shape]

theorem false_output : ¬ falseOutput.Correct := by
  intro correct
  have atGate := congrArg (fun table => table (fun i => Fin.elim0 i)) (Option.some.inj correct.2)
  cbv at atGate

@[simp] def zeroLayers : Source.Invocation ℚ := { oneLayer with outputs := [3], layers := 0 }

example : zeroLayers.Admitted := by simp [Source.Invocation.Admitted, Source.Invocation.encoding, CircuitEncoding.Admitted, CircuitEncoding.Shape]

theorem zero_correct : zeroLayers.Correct := by
  refine ⟨by simp [Source.Invocation.encoding, CircuitEncoding.Shape], ?_⟩
  apply congrArg some
  funext bits
  cbv

@[simp] def malformedZeroLayerAdd : Source.Invocation ℚ := { zeroLayers with add := [] }
@[simp] def malformedZeroLayerMul : Source.Invocation ℚ := { zeroLayers with mul := [] }

example : ¬ malformedZeroLayerAdd.Admitted := by simp [Source.Invocation.Admitted, Source.Invocation.encoding, CircuitEncoding.Admitted, CircuitEncoding.Shape]
example : ¬ malformedZeroLayerMul.Admitted := by simp [Source.Invocation.Admitted, Source.Invocation.encoding, CircuitEncoding.Admitted, CircuitEncoding.Shape]

theorem malformed_zero_add_false : ¬ malformedZeroLayerAdd.Correct :=
  CircuitEncoding.invalid_shape _ _ (by simp [Source.Invocation.encoding, CircuitEncoding.Shape])

theorem malformed_zero_mul_false : ¬ malformedZeroLayerMul.Correct :=
  CircuitEncoding.invalid_shape _ _ (by simp [Source.Invocation.encoding, CircuitEncoding.Shape])

example : ¬ ({ oneLayer with layers := 2 } : Source.Invocation ℚ).Admitted := by simp [Source.Invocation.Admitted, Source.Invocation.encoding, CircuitEncoding.Admitted, CircuitEncoding.Shape]
example : ¬ ({ oneLayer with outputs := [] } : Source.Invocation ℚ).Admitted := by simp [Source.Invocation.Admitted, Source.Invocation.encoding, CircuitEncoding.Admitted, CircuitEncoding.Shape]

example : ¬ ({ oneLayer with outputs := [] } : Source.Invocation ℚ).Correct := by
  intro correct
  have length := CircuitEncoding.outputs_shape _ _ correct
  norm_num [oneLayer, Source.Invocation.encoding] at length

#print axioms Source.admitted_represents
#print axioms Source.represents_admitted
#print axioms Source.admitted_correct_iff
#print axioms correct

end TestsSecurity.GkrRootEncoding
