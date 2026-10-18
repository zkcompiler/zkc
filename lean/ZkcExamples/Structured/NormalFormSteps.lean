module

public import Zkc.Source.Participant

@[expose] public section

/-! Steps cited by generated participant normal forms
(`lean/bridges/structured/normal_forms.py`): an owned Local call whose helper
law returns or stops behaves as that law at its owner. -/
namespace ZkcExamples.Structured.NormalFormSteps
open Zkc.Source

theorem owned_done {Role : Type} [DecidableEq Role] {Ty : Type} {Value : Ty → Type}
    {I : PIR.Signature} {inputs outputs : List Ty} (self : Role)
    {work : Values Value inputs → PIR.Proc I (Values Value outputs)}
    (args : Values Value inputs) {results : Values Value outputs}
    (law : work args = .done results) :
    Participant.owned self self work args.present = .done results.present := by
  rw [Participant.owned_present, law]
  rfl

theorem owned_halt {Role : Type} [DecidableEq Role] {Ty : Type} {Value : Ty → Type}
    {I : PIR.Signature} {inputs outputs : List Ty} (self : Role)
    {work : Values Value inputs → PIR.Proc I (Values Value outputs)}
    (args : Values Value inputs) {reason : PIR.Stop}
    (law : work args = .halt reason) :
    Participant.owned self self work args.present = .halt reason := by
  rw [Participant.owned_present, law]
  rfl

end ZkcExamples.Structured.NormalFormSteps
