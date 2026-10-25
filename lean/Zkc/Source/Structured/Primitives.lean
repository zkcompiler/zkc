module

public import Zkc.Source.Structured.Vocabulary

@[expose] public section

/-! Closed primitive vocabulary and ordered ports, independent of evaluation.
Names and parameters are resolved by admission, never by helper dispatch. -/

namespace Zkc.Source.Structured

inductive Primitive where
  | indexConstant (value : Nat)
  | indexEqual | indexLess | indexAdd | indexMul | indexSub | indexDiv | indexMod
  | vectorEmpty (domain : String) | vectorLength (domain : String)
  | vectorSum (domain : String) | vectorSplit (domain : String)
  | vectorAppend (domain : String) | vectorEqual (domain : String)
  | fieldEqual (domain : String)
  deriving DecidableEq, Repr

def Primitive.arguments : Primitive → List Ty
  | .indexConstant _ | .vectorEmpty _ => []
  | .indexEqual | .indexLess | .indexAdd | .indexMul | .indexSub | .indexDiv | .indexMod =>
      [.index, .index]
  | .vectorLength d | .vectorSum d | .vectorSplit d => [.vector d]
  | .vectorAppend d => [.vector d, .field d]
  | .vectorEqual d => [.vector d, .vector d]
  | .fieldEqual d => [.field d, .field d]

def Primitive.results : Primitive → List Ty
  | .indexConstant _ | .indexAdd | .indexMul | .indexSub | .indexDiv | .indexMod |
    .vectorLength _ => [.index]
  | .indexEqual | .indexLess | .vectorEqual _ | .fieldEqual _ => [.boolean]
  | .vectorEmpty d | .vectorAppend d => [.vector d]
  | .vectorSum d => [.field d]
  | .vectorSplit d => [.vector d, .vector d]

/-- The primitive families: the capability their one field root needs, or no
root. No prefix matching or default domain inference; the root is a catalogue
identity resolved by admission. -/
def bindingRoot : String → Option (Option String)
  | "index.constant" | "index.equal" | "index.less" | "index.add" |
    "index.mul" | "index.sub" | "index.div" | "index.mod" => some none
  | "vector.empty" | "vector.length" | "vector.sum" | "vector.split" |
    "vector.append" | "field.equal" => some (some "Field")
  | "field.embed" => some (some "ExtensionField")
  | "vector.equal" => some (some "CommRing")
  | _ => none

def Binding.nameValid (name : String) : Bool :=
  name.utf8ByteSize ≤ 256 && match name.toList with
  | [] => false
  | first :: rest =>
    let letter := fun c => ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z') || c == '_'
    letter first && rest.all (fun c => letter c || ('0' ≤ c && c ≤ '9') ||
      c == '.' || c == '-')

def Binding.valid (binding : Binding) : Bool :=
  nameValid binding.name && binding.implementation.isEmpty &&
    match bindingRoot binding.contract with
    | some none => binding.arguments.isEmpty
    | some (some _) => binding.arguments.length == 1
    | none => false

/-- The binding's root: a field row with the family's capability. -/
def Binding.resolveRoot (catalogue : Catalogue) (binding : Binding) : Except String String :=
  match bindingRoot binding.contract, binding.arguments with
  | some none, [] => .ok ""
  | some (some capability), [root] => do
    catalogue.require root .field capability
    if binding.contract == "field.embed" then
      let nominal ← catalogue.expect root .field
      let some base := nominal.member "BaseField" | throw "structured-domain-member"
      catalogue.requireEmbedding root base
    return root
  | _, _ => .error "structured-binding"

end Zkc.Source.Structured
