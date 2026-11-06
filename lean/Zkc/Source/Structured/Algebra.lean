module

public import Zkc.Source.Structured.Table
public import Zkc.Source.Structured.PolynomialValue
public import Mathlib.Algebra.Module.Defs

@[expose] public section

/-! Uniform mathematical values and an independent site-observation hook.
Group values are independent of scalars and interpreted by lawful modules. -/

set_option autoImplicit false
namespace Zkc.Source.Structured

def closedInterface : PIR.Signature := ⟨Empty, fun value => nomatch value⟩
abbrev Closed (A : Type) := PIR.Process closedInterface A

/-! Domain carriers. Domain identities are the native catalogue strings that
exported sorts name. Carriers interpret identities as types and nothing else, so
the value interpretation needs no instance arguments; the structures operations
use are added by domain models (`DomainModels`). -/

/-- A type for every field identity and every group identity. -/
structure Carriers where
  Field : String → Type
  Group : String → Type

/-- Every field identity interpreted by `F` and every group identity by `G`. -/
abbrev uniformCarriers (F G : Type) : Carriers where
  Field := fun _ => F
  Group := fun _ => G

/-- The ghost identity of one custody occurrence. A custody value has no data
payload: the token only names the occurrence for the custody ledger
(`Zkc.Semantics.Custody`). The payload-erased meaning uses token zero. -/
abbrev CustodyToken := Nat

/- Products and sequences retain the domain interpretation of each member.
Services are values only at admitted direct ports; aggregate admission refuses
nested service handles. -/
mutual
  @[reducible] def Carriers.Value (carriers : Carriers) : Ty → Type
    | .boolean => Bool
    | .index => Nat
    | .field domain => carriers.Field domain
    | .vector domain => List (carriers.Field domain)
    | .polynomial domain => PolynomialValue (carriers.Field domain)
    | .group domain => carriers.Group domain
    | .groups domain => List (carriers.Group domain)
    | .indices => List Nat
    | .oracle _ => OracleAnchor
    | .oracleSequence _ _ => List OracleAnchor
    | .service _ => Nat
    | .sequence element => List (carriers.Value element)
    | .product _ _ fields => carriers.ProductValue fields
    | .resourceUnit _ => CustodyToken
  @[reducible] def Carriers.ProductValue (carriers : Carriers) : ProductFields → Type
    | .nil => Unit
    | .cons type rest => carriers.Value type × carriers.ProductValue rest
end

/-- Uniform carriers are a specialization of the same aggregate interpretation. -/
abbrev assignment (F G : Type) := (uniformCarriers F G).Value

theorem assignment_eq_value (F G : Type) : assignment F G = (uniformCarriers F G).Value := rfl

def ProductFields.pack {carriers : Carriers} : (fields : ProductFields) →
    Values carriers.Value fields.toList → carriers.ProductValue fields
  | .nil, .nil => ()
  | .cons _ fields, .cons value rest => (value, fields.pack rest)

def ProductFields.unpack {carriers : Carriers} : (fields : ProductFields) →
    carriers.ProductValue fields → Values carriers.Value fields.toList
  | .nil, () => .nil
  | .cons _ fields, (value, rest) => .cons value (fields.unpack rest)

@[simp] theorem ProductFields.unpack_pack {carriers : Carriers} (fields : ProductFields)
    (values : Values carriers.Value fields.toList) :
    fields.unpack (fields.pack values) = values := by
  cases fields with
  | nil => cases values; rfl
  | cons type rest =>
    cases values with
    | cons value values =>
      exact congrArg (Values.cons value) (ProductFields.unpack_pack rest values)
termination_by fields

@[simp] theorem ProductFields.pack_unpack {carriers : Carriers} (fields : ProductFields)
    (value : carriers.ProductValue fields) :
    fields.pack (fields.unpack value) = value := by
  cases fields with
  | nil => cases value; rfl
  | cons type rest =>
    rcases value with ⟨value, values⟩
    exact congrArg (Prod.mk value) (ProductFields.pack_unpack rest values)
termination_by fields

def Collection.values {carriers : Carriers} : (collection : Collection) →
    carriers.Value collection.type → List (carriers.Value collection.element)
  | .vector _, values => values
  | .sequence _, values => values

/-- Site observations are the only configurable effects of mathematical bodies.
Group operations themselves use the lawful module instances directly.

The three custody transfers of a slot are configurable in the same way. Their
defaults are the payload-erased meaning: every token is zero and nothing is
checked. The custody ledger (`Zkc.Source.Structured.CustodySoundness`) supplies
the checked meaning, with fresh tokens and refusal of stale or duplicate use,
and proves that on admitted bodies the erased meaning is the checked one with
its custody requests interpreted away. -/
structure SiteObservations (interface : PIR.Signature) where
  mark : String → PIR.Process interface Unit
  /-- Create a fresh occurrence of a slot. -/
  createUnit : String → PIR.Process interface CustodyToken := fun _ => .done 0
  /-- Consume the current occurrence and transfer its successor. -/
  passUnit : String → CustodyToken → PIR.Process interface CustodyToken := fun _ _ => .done 0
  /-- Consume the occurrence without a successor. -/
  consumeUnit : String → CustodyToken → PIR.Process interface Unit := fun _ _ => .done ()

/-- Ignore site labels while retaining the chosen effect interface. -/
def SiteObservations.silent (interface : PIR.Signature) : SiteObservations interface where
  mark := fun _ => .done ()

abbrev SiteObservations.closed : SiteObservations closedInterface :=
  silent closedInterface

end Zkc.Source.Structured
