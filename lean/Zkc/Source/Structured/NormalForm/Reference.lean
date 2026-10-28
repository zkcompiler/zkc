module

public import Zkc.Source.Structured.ReferenceLaws
public import Zkc.Source.Structured.NormalForm.Denote

@[expose] public section

/-! Mathematical references install into the existing normal-form law table.
Input pins delimit applicability; they never supply the mathematical premises.
The same checked normal form can therefore serve independent honest, adversarial
and cost consumers. These lemmas neither choose a target nor fix a challenge.
-/
set_option autoImplicit false
namespace Zkc.Source.Structured.NormalForm

variable {model : DomainModel} {helper : Helper}

private theorem lawValues_selected
    (results : Values model.Value helper.outputs) (args : Values model.Value helper.inputs)
    {types : List Ty} (selected : Values model.Value types)
    (position : {ty : Ty} → Var types ty → Var helper.outputs ty)
    (same : ∀ {ty} (ref : Var types ty), results.get (position ref) = selected.get ref) :
    lawValues model helper results args types position [] = some selected := by
  induction selected with
  | nil => rfl
  | cons head tail ih =>
    have first := same .here
    simp only [lawValues, List.headD_nil, List.tail_nil, first, Values.get]
    rw [ih (fun ref => position (.there ref)) (fun ref => same (.there ref))]
    rfl

theorem lawValues_complete (results : Values model.Value helper.outputs)
    (args : Values model.Value helper.inputs) :
    lawValues model helper results args helper.outputs (fun position => position) [] = some results :=
  lawValues_selected results args results (fun position => position) (fun _ => rfl)

variable {I : PIR.Signature} {inputs : List Ty}

/-- Install a returning mathematical reference on exactly its pinned inputs.
Both applicability and reference agreement are checked obligations, independent
of the protocol's requested target and of any No/Yes predicate. -/
theorem reference_returns
    (definitions : List CheckedDefinition) (linked : DeclarationsLinked [] definitions)
    (law : ReferenceLaw model helper.inputs helper.outputs)
    (associated : BodyIn definitions helper law.body)
    (input : Values (Component model.Value) inputs) (pins : List LawPin)
    (result : Values model.Value helper.inputs → Values model.Value helper.outputs)
    (applicable : ∀ args, Pinned input pins args → law.Requires
      (definitions.foldl (Evaluation.extendMeaningsOn model SiteObservations.closed) []) args)
    (returns : ∀ args, Pinned input pins args → law.reference args = .returned (result args)) :
    LawHolds (definitions.foldl (Evaluation.ComponentTablesOn.extend model (.silent I)) ⟨[], []⟩)
      input ⟨helper, .returns [], pins⟩ result := by
  intro args pinned values selected
  have same : result args = values := by
    rw [lawValues_complete] at selected
    exact Option.some.inj selected
  rw [law.invokeOn definitions linked associated args (applicable args pinned), returns args pinned, same]
  rfl

/-- A stopping reference retains its particular reason on the pinned inputs.
Stopping does not establish an honest-success or completeness obligation. -/
theorem reference_stops
    (definitions : List CheckedDefinition) (linked : DeclarationsLinked [] definitions)
    (law : ReferenceLaw model helper.inputs helper.outputs)
    (associated : BodyIn definitions helper law.body)
    (input : Values (Component model.Value) inputs) (pins : List LawPin)
    (result : Values model.Value helper.inputs → Values model.Value helper.outputs)
    (reason : PIR.Stop)
    (applicable : ∀ args, Pinned input pins args → law.Requires
      (definitions.foldl (Evaluation.extendMeaningsOn model SiteObservations.closed) []) args)
    (stops : ∀ args, Pinned input pins args → law.reference args = .stopped reason) :
    LawHolds (definitions.foldl (Evaluation.ComponentTablesOn.extend model (.silent I)) ⟨[], []⟩)
      input ⟨helper, .stops reason, pins⟩ result := by
  intro args pinned
  rw [law.invokeOn definitions linked associated args (applicable args pinned), stops args pinned]
  rfl

end Zkc.Source.Structured.NormalForm
