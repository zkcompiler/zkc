import Zkc.Frontend.Environment.Results
import Zkc.Frontend.Semantics.Rows

namespace Zkc.Tests.Frontend.PrimitiveBindings
open Zkc.Frontend Zkc.Frontend.Emit

def fr : ClosedType := StandardNames.fieldType .bls12381Fr
def scalar : LinkedType := .nominal (.inl (.field .bls12381Fr))
def gateMessage : LinkedType := .tuple (.cons scalar (.cons scalar (.cons scalar .nil)))
def evaluate : PrimitiveName := primitiveName ⟨"circuit.gate_evaluate", #[.type fr]⟩
def signature : PrimitiveSignature := ⟨[gateMessage, scalar], [scalar]⟩
def bound : Bindings := ⟨[(evaluate, signature)], by decide⟩

example : (bound.insert evaluate signature).isOk = true := by decide +kernel
example : (bound.insert evaluate ⟨[scalar], [scalar]⟩).isOk = false := by decide +kernel

def checkWith (key : PrimitiveName) : Bool := Id.run do
  let body : Zkc.Core.Definition bound.vocabulary := .fn ⟨1⟩ [gateMessage, scalar] [scalar] false none
    ⟨[], []⟩ (.mk [0,1] [.op ⟨1⟩ [2] (.row (.inr key)) [0,1]] [2])
  let package : SourcePackage := ⟨bound, ⟨[body]⟩, ⟨[],[],[],[],[]⟩⟩
  return package.check.isOk

example : checkWith evaluate = true := by decide +kernel
example : checkWith (primitiveName ⟨"circuit.gate_evaluate", #[.type .nat]⟩) = false := by decide +kernel

def declaration (label : Option String) (output : ClosedType) : Typing.Row :=
  let t := ClosedType.tuple #[.nat] #[label]
  ⟨⟨"project.f", #[.type t]⟩, .pure, #[t], #[output]⟩

def compatible (other : Typing.Row) : Bool := Id.run do
  let some (store, first) := ({} : ResultStore).internRow (declaration (some "original") .bool) | return false
  let some (next, second) := store.internRow other | return false
  return first == second && next.rows.size == 1

#guard compatible (declaration (some "renamed") .bool) = true
#guard compatible (declaration none .nat) = false
#guard compatible { declaration none .bool with kind := .sampling } = false

end Zkc.Tests.Frontend.PrimitiveBindings
