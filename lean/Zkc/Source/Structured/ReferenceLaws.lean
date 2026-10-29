module

public import Zkc.Source.Structured.DomainLinking
public import Zkc.Source.Structured.Association

@[expose] public section

/-! Mathematical reference laws for exact typed helper bodies.

A rule is independent of a declaration's name and position. Its body retains
all nominal types, constants, operations, guards and dependency signatures.
The actual checked declaration supplies the association; linking supplies the
captured-table frame. New mathematical premises remain explicit. This layer
neither selects a claim's relation nor asserts challenge independence.
-/
set_option autoImplicit false
namespace Zkc.Source.Structured

/-- One reusable body theorem. The reference retains stopping outcomes; a
conditional rule does not claim successful execution outside its premises.
References may use a mathematical representation, but must return the entire
ordered helper result. -/
structure ReferenceLaw (model : DomainModel) (inputs outputs : List Ty) where
  body : Region dialect inputs outputs
  Requires : Evaluation.MeaningsOn model.toCarriers closedInterface →
    Values model.Value inputs → Prop
  reference : Values model.Value inputs → PIR.Outcome (Values model.Value outputs)
  valid : ∀ table arguments, Requires table arguments →
    body.denote (Evaluation.meaningOn model SiteObservations.closed table) arguments.get =
      primitiveOutcome (reference arguments)

namespace ReferenceLaw
variable {model : DomainModel} {helper : Helper}

/-- Apply the same mathematical rule to any exact associated body. The
statement uses the actual complete linked table, including dependency bodies;
name equality alone cannot establish the association or the premises. -/
theorem invoke (law : ReferenceLaw model helper.inputs helper.outputs)
    (definitions : List CheckedDefinition) (linked : DeclarationsLinked [] definitions)
    (associated : BodyIn definitions helper law.body)
    (arguments : Values model.Value helper.inputs)
    (premises : law.Requires
      (definitions.foldl (Evaluation.extendMeaningsOn model SiteObservations.closed) []) arguments) :
    Structured.invoke
      (definitions.foldl (Evaluation.extendMeaningsOn model SiteObservations.closed) [])
      helper arguments = primitiveOutcome (law.reference arguments) := by
  obtain ⟨definition, member, signature, same⟩ := associated
  rw [Evaluation.definitions_invoke_body_view_asOn model SiteObservations.closed
    definitions linked definition member helper signature law.body same arguments]
  exact law.valid _ _ premises

/-- The same closed mathematics is installed into the actual silent helper
fold in any effect interface. Query, delivery and occurrence effects remain in
the surrounding protocol; helper outcomes are lifted without changing them. -/
theorem invokeOn {I : PIR.Signature} (law : ReferenceLaw model helper.inputs helper.outputs)
    (definitions : List CheckedDefinition) (linked : DeclarationsLinked [] definitions)
    (associated : BodyIn definitions helper law.body)
    (arguments : Values model.Value helper.inputs)
    (premises : law.Requires
      (definitions.foldl (Evaluation.extendMeaningsOn model SiteObservations.closed) []) arguments) :
    Structured.invoke (definitions.foldl
      (Evaluation.ComponentTablesOn.extend model (.silent I)) ⟨[], []⟩).closed helper arguments =
      primitiveOutcome (law.reference arguments) := by
  rw [Evaluation.closed_invoke_componentTablesOn,
    law.invoke definitions linked associated arguments premises]
  cases law.reference arguments <;> rfl

/-- Return-only facts and rejection facts are derived from the same exact
outcome equation. They do not replace it with partial correctness. -/
theorem returned (law : ReferenceLaw model helper.inputs helper.outputs)
    (definitions : List CheckedDefinition) (linked : DeclarationsLinked [] definitions)
    (associated : BodyIn definitions helper law.body)
    (arguments : Values model.Value helper.inputs)
    (premises : law.Requires
      (definitions.foldl (Evaluation.extendMeaningsOn model SiteObservations.closed) []) arguments)
    (values : Values model.Value helper.outputs) (reference : law.reference arguments = .returned values) :
    Structured.invoke
      (definitions.foldl (Evaluation.extendMeaningsOn model SiteObservations.closed) [])
      helper arguments = .done values := by
  rw [law.invoke definitions linked associated arguments premises, reference]
  rfl

end ReferenceLaw
end Zkc.Source.Structured
