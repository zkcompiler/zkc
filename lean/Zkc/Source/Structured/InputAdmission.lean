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

/-- An absent slot carries no value to represent. A service handle is logical
input metadata, not an executable index, and has no machine range condition. -/
def inputRepresentable {carriers : Carriers} : (type : Ty) →
    Component carriers.Value type → Prop
  | .index, some value => value < indexLimit
  | .vector _, some values => values.length < indexLimit
  | _, _ => True

/-- The ordered source input tuple fixes the bounds, independently of evidence
and of a protocol-specific shape predicate. -/
def inputsRepresentable {carriers : Carriers} : {types : List Ty} →
    Values (Component carriers.Value) types → Prop
  | [], .nil => True
  | type :: _, .cons value rest => inputRepresentable type value ∧ inputsRepresentable rest

-- Materialize the shared equations at their definition owner. Otherwise each
-- ABI client can generate different private matcher proofs under the same
-- equation name. The scoped attribute adds no global simplifier rules.
section
attribute [local simp] inputRepresentable inputsRepresentable
end

@[simp] theorem inputsRepresentable_nil {carriers : Carriers} :
    inputsRepresentable (carriers := carriers) .nil := trivial

@[simp] theorem inputsRepresentable_cons {carriers : Carriers} {type : Ty} {types : List Ty}
    (value : Component carriers.Value type) (rest : Values (Component carriers.Value) types) :
    inputsRepresentable (.cons value rest) ↔
      inputRepresentable type value ∧ inputsRepresentable rest := Iff.rfl

end Zkc.Source.Structured
