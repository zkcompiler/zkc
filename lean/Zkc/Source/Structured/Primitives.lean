module

public import Zkc.Source.Structured.Numerical
public import Zkc.Source.LogicalFormat

@[expose] public section

/-! Closed primitive vocabulary and ordered ports, independent of evaluation.
Names and parameters are resolved by admission, never by helper dispatch. -/

namespace Zkc.Source.Structured

inductive Primitive where
  | numerical (operation : Numerical) (domain base : String)
  | binaryConstant (domain : String) (bits : Nat)
  | booleanNot
  | indexConstant (value : Nat)
  | indexEqual | indexLess | indexAdd | indexMul | indexSub | indexDiv | indexMod
  | vectorEmpty (domain : String) | vectorLength (domain : String)
  | vectorSum (domain : String) | vectorSplit (domain : String)
  | vectorAppend (domain : String) | vectorEqual (domain : String)
  | fieldEqual (domain : String)
  deriving DecidableEq, Repr

def Primitive.arguments : Primitive → List Ty
  | .numerical op d b => op.arguments d b
  | .binaryConstant .. => []
  | .booleanNot => [.boolean]
  | .indexConstant _ | .vectorEmpty _ => []
  | .indexEqual | .indexLess | .indexAdd | .indexMul | .indexSub | .indexDiv | .indexMod =>
      [.index, .index]
  | .vectorLength d | .vectorSum d | .vectorSplit d => [.vector d]
  | .vectorAppend d => [.vector d, .field d]
  | .vectorEqual d => [.vector d, .vector d]
  | .fieldEqual d => [.field d, .field d]

def Primitive.results : Primitive → List Ty
  | .numerical op d b => op.results d b
  | .binaryConstant d _ => [.field d]
  | .booleanNot => [.boolean]
  | .indexConstant _ | .indexAdd | .indexMul | .indexSub | .indexDiv | .indexMod |
    .vectorLength _ => [.index]
  | .indexEqual | .indexLess | .vectorEqual _ | .fieldEqual _ => [.boolean]
  | .vectorEmpty d | .vectorAppend d => [.vector d]
  | .vectorSum d => [.field d]
  | .vectorSplit d => [.vector d, .vector d]

/-- The custody transfers of one exact slot. Their one static root is a `Slot`
identity: an exact nominal custody identity, never a catalogue domain. -/
def custodyContract : String → Bool
  | "resource_unit.create" | "resource_unit.pass" | "resource_unit.consume" => true
  | _ => false

/-- The primitive families: the capability their one field root needs, the
`Slot` root of a custody transfer, or no root. No prefix matching or default
domain inference; a field root is a catalogue identity resolved by admission. -/
def bindingRoot : String → Option (Option String)
  | "index.constant" | "index.equal" | "index.less" | "index.add" |
    "index.mul" | "index.sub" | "index.div" | "index.mod" => some none
  | "vector.empty" | "vector.length" | "vector.sum" | "vector.split" |
    "vector.append" | "field.equal" => some (some "Field")
  | "field.embed" => some (some "ExtensionField")
  | "vector.equal" => some (some "CommRing")
  | "resource_unit.create" | "resource_unit.pass" | "resource_unit.consume" => some (some "Slot")
  | "bool.and" | "bool.or" | "bool.not" => some none
  | "field.constant" | "field.add" | "field.sub" | "field.mul" => some (some "Field")
  | contract => (Numerical.ofContract contract).map Numerical.root

/-- The sort of a binding's static root. -/
def bindingRootSort (contract : String) : String :=
  if custodyContract contract then "Slot" else "Field"

def Binding.nameValid (name : String) : Bool :=
  name.utf8ByteSize ≤ 256 && match name.toList with
  | [] => false
  | first :: rest =>
    let letter := fun c => ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z') || c == '_'
    letter first && rest.all (fun c => letter c || ('0' ≤ c && c ≤ '9') ||
      c == '.' || c == '-')

def Binding.valid (binding : Binding) : Bool :=
  nameValid binding.name && binding.implementation.isEmpty &&
    (match bindingRoot binding.contract with
    | some none => binding.arguments.isEmpty
    | some (some _) => binding.arguments.length == 1
    | none => false) &&
    (match binding.schema with
    | none => true
    | some schema => schema.arguments ==
        binding.arguments.map (BindingArgument.domain (bindingRootSort binding.contract)))

/-- Independently fixed ordered logical signatures. These are the existing
formal meanings, not signatures selected from a candidate's catalogue. The
base of an embedding is resolved from the actual nominal row before use. -/
def bindingSignature (contract root : String) (base : String := "") :
    Except String (List Ty × List Ty) := do
  if contract == "field.embed" then return ([.field base], [.field root])
  if contract == "field.constant" then return ([], [.field root])
  if ["field.add", "field.sub", "field.mul"].contains contract then
    return ([.field root, .field root], [.field root])
  if ["bool.and", "bool.or"].contains contract then return ([.boolean, .boolean], [.boolean])
  if contract == "bool.not" then return ([.boolean], [.boolean])
  if let some numerical := Numerical.ofContract contract then
    return (numerical.arguments root base, numerical.results root base)
  if contract == "resource_unit.create" then return ([], [.resourceUnit root])
  if contract == "resource_unit.pass" then return ([.resourceUnit root], [.resourceUnit root])
  if contract == "resource_unit.consume" then return ([.resourceUnit root], [])
  let primitive ← match contract with
    | "index.constant" => pure (Primitive.indexConstant 0)
    | "index.add" => pure Primitive.indexAdd
    | "index.sub" => pure Primitive.indexSub
    | "index.mul" => pure Primitive.indexMul
    | "index.div" => pure Primitive.indexDiv
    | "index.mod" => pure Primitive.indexMod
    | "index.equal" => pure Primitive.indexEqual
    | "index.less" => pure Primitive.indexLess
    | "vector.empty" => pure (Primitive.vectorEmpty root)
    | "vector.length" => pure (Primitive.vectorLength root)
    | "vector.sum" => pure (Primitive.vectorSum root)
    | "vector.split" => pure (Primitive.vectorSplit root)
    | "vector.append" => pure (Primitive.vectorAppend root)
    | "vector.equal" => pure (Primitive.vectorEqual root)
    | "field.equal" => pure (Primitive.fieldEqual root)
    | _ => throw "structured-binding"
  return (primitive.arguments, primitive.results)

/-- Retained wire signatures are claims to check, including for unused rows.
Internal declarations without wire metadata retain their original denotation. -/
def Binding.checkSignature (binding : Binding) (root base : String) : Except String Unit := do
  if !binding.valid then throw "structured-binding"
  if let some schema := binding.schema then
    let (inputs, outputs) ← bindingSignature binding.contract root base
    if schema.inputs != inputs || schema.outputs != outputs then
      throw "structured-binding-signature"

/-- The binding's root: a field row with the family's capability. -/
def Binding.resolveRoot (catalogue : Catalogue) (binding : Binding) : Except String String := do
  if !binding.valid then throw "structured-binding"
  match bindingRoot binding.contract, binding.arguments with
  | some none, [] =>
    binding.checkSignature "" ""
    return ""
  | some (some capability), [root] => do
    if custodyContract binding.contract then
      -- An exact nominal slot: no catalogue row is consulted or required.
      unless LogicalFormat.slotIdentityValid root do throw "structured-slot-identity"
      binding.checkSignature root ""
      return root
    catalogue.require root .field capability
    let base ← if binding.contract == "field.embed" || binding.contract == "vector.embed" then do
      let nominal ← catalogue.expect root .field
      let some base := nominal.member "BaseField" | throw "structured-domain-member"
      catalogue.requireEmbedding root base
      pure base
    else pure ""
    if binding.contract == "poly.even_odd_fold" then
      catalogue.require root .field "CharacteristicNotTwo"
    binding.checkSignature root base
    return root
  | _, _ => throw "structured-binding"

end Zkc.Source.Structured
