import ZkcTools.StructuredSource.ReferenceInstallation
import ZkcTools.StructuredSource.ReferenceComposition

/-! Installation shares complete laws through exact associations. Missing
association and mathematical premises cannot be manufactured by the proposer. -/
set_option autoImplicit false
noncomputable section
namespace Tests.ReferenceLawInstallation
open Zkc.Source Zkc.Source.Structured

private def leaf : Helper := ⟨"arbitrary-leaf", .math, [.boolean, .index], [.index, .boolean]⟩
private def wrapper : Helper :=
  ⟨"arbitrary-wrapper", .math, [.boolean, .index, .vector "capture"], leaf.outputs⟩

private def leafLaw (model : DomainModel) :=
  ReferenceLibrary.projection model
    (.cons (.there .here) (.cons .here .nil) : Operands leaf.inputs leaf.outputs)

private def wrapperBody : Region dialect wrapper.inputs wrapper.outputs :=
  .letOp (.invoke leaf) (.cons .here (.cons (.there .here) .nil)) .nil
    (.ret (ReferenceLibrary.resultOperands leaf.outputs _))

private def wrapperLaw (model : DomainModel) :=
  forward_reference% wrapperBody using (leafLaw model)

private structure Bodies (model : DomainModel) (definitions : List CheckedDefinition) : Prop where
  first : BodyIn definitions leaf (leafLaw model).body
  second : BodyIn definitions wrapper (wrapperLaw model).body

private structure Laws (model : DomainModel)
    (table : Evaluation.MeaningsOn model.toCarriers closedInterface) : Prop where
  first : (leafLaw model).Realizes (helper := leaf) table
  second : (wrapperLaw model).Realizes (helper := wrapper) table

example (model : DomainModel) (definitions : List CheckedDefinition)
    (_linked : DeclarationsLinked [] definitions) (bodies : Bodies model definitions) :
    Laws model (closedMeaningsOn model definitions) := by
  install_reference_laws using _linked with bodies

example (model : DomainModel) (definitions : List CheckedDefinition)
    (_linked : DeclarationsLinked [] definitions)
    (_body : BodyIn definitions wrapper (wrapperLaw model).body)
    (manual : Laws model (closedMeaningsOn model definitions)) :
    Laws model (closedMeaningsOn model definitions) := by
  fail_if_success solve | install_reference_laws using _linked with _body
  exact manual

private def guarded : Helper := ⟨"conditional", .math, [.boolean], [.boolean]⟩
private def conditionalLaw (model : DomainModel) :
    ReferenceLaw model guarded.inputs guarded.outputs where
  body := .letOp .guard (.cons .here .nil) .nil (.ret (.cons .here .nil))
  Requires _ arguments := arguments.get .here = true
  reference _ := .returned (.cons true .nil)
  valid _ arguments accepted := by
    cases arguments with
    | cons decision rest =>
      cases rest
      change decision = true at accepted
      subst decision
      rfl

example (model : DomainModel) (definitions : List CheckedDefinition)
    (_linked : DeclarationsLinked [] definitions)
    (_body : BodyIn definitions guarded (conditionalLaw model).body)
    (manual : (conditionalLaw model).Realizes (helper := guarded)
      (closedMeaningsOn model definitions)) :
    (conditionalLaw model).Realizes (helper := guarded) (closedMeaningsOn model definitions) := by
  fail_if_success solve | install_reference_laws using _linked with _body
  exact manual

end Tests.ReferenceLawInstallation
