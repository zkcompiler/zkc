import Examples.VectorService.Language
import Zkc.Compiler.ArtifactFormat

/-! Closed consumer descriptors and named invocation values. -/
set_option autoImplicit false
namespace VectorService
open Lean Zkc.Source Zkc.Compiler

def types : Format.Codec Ty where
  encode
    | .count => toJson (["count"] : List String)
    | .vector => toJson (["vector"] : List String)
    | .predicate => toJson (["predicate"] : List String)
  decode json := do
    match ← Format.array json with
    | [.str "count"] => return .count
    | [.str "vector"] => return .vector
    | [.str "predicate"] => return .predicate
    | _ => throw .unknownType
def operations : Format.Codec Op where
  encode
    | .request => toJson (["request"] : List String)
    | .send => toJson (["send"] : List String)
    | .requestAndSend => toJson (["request_and_send"] : List String)
    | .sum => toJson (["sum"] : List String)
  decode json := do
    match ← Format.array json with
    | [.str "request"] => return .request
    | [.str "send"] => return .send
    | [.str "request_and_send"] => return .requestAndSend
    | [.str "sum"] => return .sum
    | _ => throw .unknownOperation
def dependencies : List DefinitionRef := [⟨"vector-service", "1"⟩]
private def natural (v : Json) : Except String Nat :=
  (Format.natural v).mapError Format.Error.code
private def array (v : Json) : Except String (List Json) :=
  (Format.array v).mapError Format.Error.code
private def scalar (v : Json) : Except String (Fin 7) := do
  let n ← natural v
  if h : n < 7 then return ⟨n, h⟩ else throw "noncanonical-scalar"
def decodeValue : (ty : Ty) → Json → Except String (Value ty)
  | .count, v => natural v
  | .vector, v => do (← array v).mapM scalar
  | .predicate, v => v.getBool?.mapError (fun _ => "invalid-value")
def valueJson : (ty : Ty) → Value ty → Json
  | .count, n => toJson n
  | .vector, xs => toJson (xs.map Fin.val)
  | .predicate, b => toJson b
def suppliedInput (v : Json) : Except String (SuppliedInput Value) := do
  match ← array v with
  | [name, ty, value] =>
    let name ← name.getStr?.mapError (fun _ => "expected-string")
    let ty ← types.decode ty |>.mapError Format.Error.code
    return ⟨name, ty, ← decodeValue ty value⟩
  | _ => throw "invalid-input"
def decodeState (v : Json) : Except String State := do
  match ← array v with
  | [calls, tape] => return ⟨← natural calls, ← (← array tape).mapM scalar⟩
  | _ => throw "invalid-state"
def stateJson (s : State) : Json := .arr #[toJson s.calls, toJson (s.tape.map Fin.val)]
def eventJson : Event → Json
  | .requested n => .arr #[.str "request", toJson n]
  | .sent n => .arr #[.str "send", toJson n]

end VectorService
