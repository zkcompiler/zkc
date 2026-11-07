module

public import Zkc.Realization.ClearStorageCaptures
public import Tests.ClearStorage

@[expose] public section

namespace Tests.CaptureLayout
open Zkc.Source Zkc.Source.Structured Zkc.Realization
open Zkc.Realization.CaptureLayout

abbrev inputs : List Ty := [.oracle ClearStorage.kind, .oracle ClearStorage.kind, .index]
abbrev outputs : List Ty := [referenceType ClearStorage.layout.referenceIdentity,
  referenceType ClearStorage.layout.referenceIdentity, .index]

def layout : Layout inputs outputs :=
  .handle ClearStorage.kind ClearStorage.layout.referenceIdentity
    (.handle ClearStorage.kind ClearStorage.layout.referenceIdentity (.data rfl .nil))

def captures (model : DomainModel) (first second : OracleAnchor) (parameter : Nat) :
    Values model.Value inputs := .cons first (.cons second (.cons parameter .nil))

def encoded (model : DomainModel) (parameter : Nat) : Values model.Value outputs :=
  .cons (7, 0, ()) (.cons (7, 1, ()) (.cons parameter .nil))

def association (model : DomainModel) : References :=
  Zkc.Realization.ClearStorage.references ClearStorage.layout
    (ClearStorage.words model) (ClearStorage.records model)

/-- Distinct publications have equal cells, but their captures use different slots. -/
theorem captures_related (model : DomainModel) (parameter : Nat) :
    Related (association model) layout
      (captures model (ClearStorage.word model 2 7).anchor (ClearStorage.word model 2 9).anchor parameter)
      (encoded model parameter) :=
  ⟨⟨rfl, rfl, _, rfl, ClearStorage.first_stored model⟩,
    ⟨⟨rfl, rfl, _, rfl, ClearStorage.second_stored model⟩, rfl, trivial⟩⟩

/-- Same-typed parent substitution fails on the logical association, even though
both candidate captures are well-typed and both words contain the same data. -/
theorem swapped_parents_refused (model : DomainModel) (parameter : Nat) :
    ¬ Related (association model) layout
      (captures model (ClearStorage.word model 2 9).anchor (ClearStorage.word model 2 7).anchor parameter)
      (encoded model parameter) := by
  intro swapped
  have equal := (captures_related model parameter).source_unique
    (Zkc.Realization.ClearStorage.references_unambiguous _ _ _) swapped
  have first := congrArg (fun values ↦ values.get .here) equal
  have distinct : (ClearStorage.word model 2 7).anchor ≠ (ClearStorage.word model 2 9).anchor := by
    change (ClearStorage.location 2 7).anchor ≠ (ClearStorage.location 2 9).anchor
    decide
  exact distinct first

/-- Parameter equality is just as strict as parent identity. -/
theorem changed_parameter_refused (model : DomainModel) :
    ¬ Related (association model) layout
      (captures model (ClearStorage.word model 2 7).anchor (ClearStorage.word model 2 9).anchor 8)
      (encoded model 7) := by
  intro wrong
  have equal := (captures_related model 7).source_unique
    (Zkc.Realization.ClearStorage.references_unambiguous _ _ _) wrong
  have parameter := congrArg (fun values ↦ values.get (.there (.there .here))) equal
  change (7 : Nat) = 8 at parameter
  contradiction

/-- Parameter and parent projection both use the same derived slot map. -/
example (model : DomainModel) (parameter : Nat) :
    (encoded model parameter).get (layout.physicalVar (.there (.there .here))) = parameter :=
  ((captures_related model parameter).get (.there (.there .here))).symm

example (model : DomainModel) (parameter : Nat) :
    association model ClearStorage.kind ClearStorage.layout.referenceIdentity
      (ClearStorage.word model 2 9).anchor (7, 1) :=
  (captures_related model parameter).get (.there .here)

example : (recognize inputs outputs).isSome = true := by decide +kernel
example : (recognize inputs [.index, .index, .index]).isSome = false := by decide +kernel
example : (recognize [.oracleSequence ClearStorage.kind 2] [.indices]).isSome = false := by decide +kernel
example : (recognize [.service "draw"] [.index]).isSome = false := by decide +kernel
example : (recognize [.sequence (.oracle ClearStorage.kind)] [.sequence .index]).isSome = false := by decide +kernel

#print axioms captures_related
#print axioms swapped_parents_refused
#print axioms Zkc.Realization.CaptureLayout.Related.transport
end Tests.CaptureLayout
