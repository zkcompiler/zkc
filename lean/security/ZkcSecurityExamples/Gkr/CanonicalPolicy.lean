module

public import ZkcSecurityExamples.Gkr.Generated.ABI
public import ZkcSecurityExamples.Gkr.Canonical
public import ZkcSecurity.Claims.Completeness

@[expose] public section

/-! Independent target and admission laws at the generated current-source ABI.
The optional producer service slot does not enter either circuit predicate. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 250000
noncomputable section
namespace ZkcSecurity.Realizations.Gkr.CanonicalPolicy
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Claims.HonestPair
open Generated.Subject Generated.ABI
abbrev Scalar := model.Field scalarDomain

abbrev RuntimeData := Values (TypedABI.Slot Domain.dataType model.Value)
  [Ty.vector scalarDomain, .vector scalarDomain, .vector scalarDomain, .vector scalarDomain,
    .index, .index, .index, .service "random.bls12-381.fr/0"]

def runtimeData (values : RuntimeData) : Source.Invocation Scalar where
  inputs := values.get .here
  outputs := values.get (.there .here)
  add := values.get (.there (.there .here))
  mul := values.get (.there (.there (.there .here)))
  layers := values.get (.there (.there (.there (.there .here))))
  selector := values.get (.there (.there (.there (.there (.there .here)))))
  width := values.get (.there (.there (.there (.there (.there (.there .here))))))
  handle := 0

def runtime (values : Data) : Source.Invocation Scalar := runtimeData values

theorem relation_exact (values : Data) :
    subject.Relation (abi.pack values) ↔ (runtime values).Correct := by
  obtain ⟨initial, outputs, add, mul, layers, selector, width, service, rfl⟩ := data_surjective values
  change subject.Relation (inputs initial outputs add mul layers selector width service) ↔ _
  exact (subject.relation_iff_of_read _ _
    (application_read initial outputs add mul layers selector width service)).trans (by rfl)

theorem admitted (values : Data) (honest : subject.HonestInput (abi.pack values)) :
    (runtime values).Admitted := by
  have clause := honest.2.1 ⟨0, by decide⟩ rfl
  obtain ⟨initial, outputs, add, mul, layers, selector, width, service, rfl⟩ := data_surjective values
  change (∃ arguments : Values model.Value (Relations.shapeInputs scalarDomain),
    some (.cons initial (.cons outputs (.cons add (.cons mul (.cons layers
      (.cons selector (.cons width .nil))))))) = some arguments ∧
      Relations.shapeMeaning model scalarDomain 4 4 arguments) at clause
  obtain ⟨arguments, same, valid⟩ := clause
  cases Option.some.inj same
  exact valid

/-- An independently admitted zero-layer circuit witnesses the actual fixed
subject's honest domain. This does not depend on any proof or oracle table. -/
theorem nonvacuous : Nonvacuous subject := by
  let values := data [0] [0] [0] [0] 0 0 0 none
  have shape : (runtime values).encoding.Shape := by
    change (CircuitEncoding.mk ([0] : List Scalar) [0] [0] 0 0 0).Shape
    simp [CircuitEncoding.Shape]
  have correct : (runtime values).Correct := by
    refine ⟨shape, ?_⟩
    change Zkc.Polynomial.Multilinear.ofList? 0 [0] =
      some (runtime values).encoding.circuit.inputs
    exact (runtime values).encoding.inputs_decode shape
  refine ⟨abi.pack values, (relation_exact values).mpr correct, ?_⟩
  change subject.HonestInput (inputs [0] [0] [0] [0] 0 0 0 none)
  rw [honestInput_iff]
  constructor
  · decide +kernel
  · change (CircuitEncoding.mk ([0] : List Scalar) [0] [0] 0 0 0).Admitted 4 4 [0]
    simp [CircuitEncoding.Admitted, CircuitEncoding.Shape]

end ZkcSecurity.Realizations.Gkr.CanonicalPolicy
