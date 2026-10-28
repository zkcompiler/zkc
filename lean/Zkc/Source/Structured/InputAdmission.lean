module

public import Zkc.Source.Structured.DomainEvaluation
public import Zkc.Source.Component

@[expose] public section

/-! Representation bounds of the executable input ABI. These do not restrict
Math's natural-number semantics. Presence, role projection and oracle anchors
are checked separately by the selected participant pair's preparation. -/
set_option autoImplicit false
namespace Zkc.Source.Structured
open Zkc.Source

mutual
  /-- An absent slot carries no value to represent. A service handle is logical
  input metadata, not an executable index, and has no machine range condition.
  Products and sequences retain the bounds of every nested member. This is a
  representation premise, not admission of a generated or native ABI. -/
  def inputRepresentable {carriers : Carriers} : (type : Ty) →
      Component carriers.Value type → Prop
    | .index, some value => value < indexLimit
    | .vector _, some values | .groups _, some values => values.length < indexLimit
    | .indices, some values => values.length < indexLimit ∧ ∀ value ∈ values, value < indexLimit
    | .oracleSequence _ maximum, some values => values.length ≤ maximum
    | .sequence element, some values => values.length < indexLimit ∧
        ∀ value ∈ values, inputRepresentable element (some value)
    | .product _ _ fields, some value => productRepresentable fields value
    | _, _ => True

  def productRepresentable {carriers : Carriers} : (fields : ProductFields) →
      carriers.ProductValue fields → Prop
    | .nil, _ => True
    | .cons type fields, (value, rest) =>
        inputRepresentable type (some value) ∧ productRepresentable fields rest
end

/-- The ordered source input tuple fixes the bounds, independently of evidence
and of a protocol-specific shape predicate. -/
def inputsRepresentable {carriers : Carriers} : {types : List Ty} →
    Values (Component carriers.Value) types → Prop
  | [], .nil => True
  | type :: _, .cons value rest => inputRepresentable type value ∧ inputsRepresentable rest

-- Materialize shared equation proofs at their definition's owner. Independent
-- clients must not realize different private matcher proofs under the same
-- public equation name. The scoped attribute exports no global simp rule.
section
attribute [local simp] inputRepresentable productRepresentable inputsRepresentable
end

@[simp] theorem inputsRepresentable_nil {carriers : Carriers} :
    inputsRepresentable (carriers := carriers) .nil := trivial

@[simp] theorem inputsRepresentable_cons {carriers : Carriers} {type : Ty} {types : List Ty}
    (value : Component carriers.Value type) (rest : Values (Component carriers.Value) types) :
    inputsRepresentable (.cons value rest) ↔
      inputRepresentable type value ∧ inputsRepresentable rest := Iff.rfl

end Zkc.Source.Structured
