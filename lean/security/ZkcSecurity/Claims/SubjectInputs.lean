module

public import ZkcSecurity.Claims.AuthoredPair

@[expose] public section

/-! A checked source-selector read reduces the existing retained relation to
its fixed relation meaning. This lemma neither supplies selectors nor
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
      subject.meaning.HoldsOn subject.target.booleanOutput arguments :=
  (subject.target.clause subject.meaning).holds_iff_of_read {} (subject.boundary inputs)
    (subject.assignments inputs) arguments read

end ZkcSecurity.Claims.HonestPair.Subject
