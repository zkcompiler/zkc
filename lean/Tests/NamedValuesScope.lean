module

public import Zkc.Source.Structured.NormalForm.Denote
public meta import ZkcTools.StructuredSource.NamedValues

/-! The same record presentation covers both source rows and normalized binder
scopes. No per-client tuple adapter or alternate binder semantics is needed. -/
set_option autoImplicit false
namespace Tests.NamedValuesScope
open Zkc.Source Zkc.Source.Structured NormalForm

def pattern : InputPattern [.index, .boolean, .vector "field", .index] :=
  .cons .optional (.cons .absent (.cons .present (.cons (.index 9) .nil)))

named_values Inputs [position, samples] := pattern.scope
named_values Full [value, optional, results, tuple] :=
  ([.value .index, .component .boolean, .results [.index, .boolean], .tuple [.index]] : Scope)

example (model : DomainModel) (position : Option Nat) (row : List (model.Field "field")) :
    pattern.environment model
      (Inputs.pack (Value := Slot.Value model) { position, samples := row }) =
        .cons position (.cons none (.cons (some row) (.cons (some 9) .nil))) := rfl

example (model : DomainModel) (scope : Binders model pattern.scope) :
    Inputs.pack (Inputs.unpack scope) = scope := Inputs.pack_unpack scope

example (model : DomainModel) (values : Binders model Full.types) :
    Full.pack (Full.unpack values) = values := Full.pack_unpack values

example (model : DomainModel) (position : Nat) (row : List (model.Field "field")) :
    (Inputs.unpack (Inputs.pack (Value := Slot.Value model)
      { position := none, samples := row })).position ≠ some position := by
  change (none : Option Nat) ≠ some position
  simp

/-- error: named_values requires an ordered list schema -/
#guard_msgs in
named_values NotARow [value] := (3 : Nat)

#print axioms Inputs.pack_unpack
#print axioms Full.pack_unpack
end Tests.NamedValuesScope
