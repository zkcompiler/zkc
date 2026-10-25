module

public import ZkcSecurity.Claims.AuthoredPair

@[expose] public section

/-! A checked source-selector read reduces the existing retained relation to
its actual formula invocation. This lemma neither supplies selectors nor
replaces the retained source predicate. -/
set_option autoImplicit false
namespace ZkcSecurity.Claims.HonestPair.Subject
open Zkc.Source Zkc.Source.Structured Zkc.Construction

variable {model : DomainModel} {original : Snapshot} {imported : Imported original}
  {selected : AuthoredPair.Selection original}

theorem relation_iff_of_read (subject : Subject model original imported selected)
    (inputs : subject.Inputs)
    (arguments : Values model.Value subject.target.application.relation.declaration.inputs)
    (read : subject.target.application.read {} (subject.boundary inputs)
      (subject.assignments inputs) = some arguments) :
    subject.Relation inputs ↔
      subject.target.formula.invokeRelationOn model arguments =
        .done (subject.target.booleanOutput.symm ▸ Values.cons true .nil) := by
  constructor
  · rintro ⟨actual, actualRead, truth⟩
    have same := Option.some.inj (read.symm.trans actualRead)
    cases same
    exact truth
  · intro truth
    exact ⟨arguments, read, truth⟩

end ZkcSecurity.Claims.HonestPair.Subject
