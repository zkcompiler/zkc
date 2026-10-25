module

public import Zkc.Claims.Registry

@[expose] public section

set_option autoImplicit false
namespace ZkcSecurity.Claims
open Zkc.Claims

inductive PropertyKey where
  | soundness | knowledge | completeness | specialSoundness
  deriving DecidableEq, Repr

namespace PropertyKey

def identifier : PropertyKey → Identifier
  | .soundness => ⟨"soundness", 0⟩
  | .knowledge => ⟨"knowledge", 0⟩
  | .completeness => ⟨"completeness", 0⟩
  | .specialSoundness => ⟨"special_soundness", 0⟩

def schema : PropertyKey → String
  | .soundness => "zkc.property.soundness/0"
  | .knowledge => "zkc.property.knowledge/0"
  | .completeness => "zkc.property.completeness/0"
  | .specialSoundness => "zkc.property.special-soundness/0"

def all : List PropertyKey := [.soundness, .knowledge, .completeness, .specialSoundness]

def ofIdentifier? (identifier : Identifier) : Option PropertyKey :=
  all.find? (·.identifier == identifier)

end PropertyKey

/-- All root names and the infrastructure namespaces are reserved, at every
version. Undefined canonical properties cannot fall through to author claims. -/
def namespaceBytes : List UInt8 → Option (List UInt8)
  | [] => none
  | byte :: rest => if byte = 46 then some [] else (namespaceBytes rest).map (byte :: ·)

def reservedIdentifier (identifier : Identifier) : Bool :=
  match namespaceBytes identifier.name.toByteArray.data.toList with
  | none => true
  | some space => ["models", "extractors", "reductions", "assumptions",
      "charges", "guarantees", "capabilities", "oracles", "gaps", "producers"].any
        (fun candidate => candidate.toByteArray.data.toList == space)

theorem PropertyKey.reserved (key : PropertyKey) : reservedIdentifier key.identifier = true := by
  cases key <;> decide

end ZkcSecurity.Claims
