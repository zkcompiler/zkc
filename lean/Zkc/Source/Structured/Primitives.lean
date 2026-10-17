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

/-- Exact closed allowlist. No prefix matching or default domain inference. -/
def bindingArguments : String → Option (List String)
  | "index.constant" | "index.equal" | "index.less" | "index.add" |
    "index.mul" | "index.sub" | "index.div" | "index.mod" => some []
  | "vector.empty" | "vector.length" | "vector.sum" | "vector.split" |
    "vector.append" | "vector.equal" | "field.equal" => some [scalarDomain]
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
    bindingArguments binding.contract == some binding.arguments

end Zkc.Source.Structured
