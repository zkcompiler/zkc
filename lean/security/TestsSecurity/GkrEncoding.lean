module

public import ZkcSecurity.Bindings.Gkr.Encoding

public section
namespace TestsSecurity.GkrEncoding
open ZkcSecurity.Realizations.Gkr

@[expose] def emptyCircuit : CircuitEncoding ℚ := ⟨[7], [0], [0], 0, 0, 0⟩

theorem valid_empty : emptyCircuit.Outputs [7] := by
  constructor
  · norm_num [CircuitEncoding.Shape, emptyCircuit]
  · rfl

/-- Unused wiring still belongs to the fixed public circuit schema. -/
theorem malformed_empty : ¬ ({ emptyCircuit with add := [] }).Outputs [7] := by
  apply CircuitEncoding.invalid_shape
  norm_num [CircuitEncoding.Shape, emptyCircuit]

theorem no_padding : ¬ emptyCircuit.Outputs [7, 0] := by
  intro truth
  have size := CircuitEncoding.outputs_shape _ _ truth
  norm_num [emptyCircuit] at size

theorem changed_output : ¬ emptyCircuit.Outputs [8] := by
  intro truth
  have entry := Zkc.Polynomial.Multilinear.ofList?_entry [8] _ truth.2 ⟨0, by decide⟩
  norm_num [emptyCircuit, CircuitEncoding.circuit, ZkcSecurity.Families.Gkr.Circuit.wires,
    Zkc.Protocols.Gkr.values, Zkc.Polynomial.Multilinear.ofList?,
    Zkc.Polynomial.Multilinear.ofVector] at entry

#print axioms CircuitEncoding.inputs_decode
#print axioms CircuitEncoding.add_decode
#print axioms CircuitEncoding.mul_decode
#print axioms changed_output

end TestsSecurity.GkrEncoding
