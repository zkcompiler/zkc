module

public import Zkc.Source.Constructed.Format
public import ZkcTools.JsonSupport

@[expose] public section

/-! Exact primitive replay for differential bridge controls.

Natural-number tokens stand for opaque native values. Replay checks every reached
primitive name and actual operand and retains successor results. It establishes
no arithmetic, provider, sampling, or byte-codec conformance by itself.
-/
set_option autoImplicit false
namespace Zkc.Tools.Constructed
open Lean Source Source.Constructed

abbrev Token (_ : String) := Nat
structure Request where
  operation : Primitive
  arguments : Values Token operation.arguments

def interface : PIR.Signature where
  Op := Request
  Reply request := Values Token request.operation.results

def meaning : Meaning interface where
  Value := Token
  condition := fun token => token != 0
  primitive := fun op args => .call ⟨op, args⟩ .done

def tokens {types : List String} : Values Token types → List Nat
  | .nil => []
  | .cons value rest => value :: tokens rest

def values : (types : List String) → List Json → Except String (Values Token types)
  | [], [] => .ok .nil
  | ty :: types, json :: rest => do
      let value ← Source.Format.natural json |>.mapError fun _ => "constructed-run-value"
      if ty == "i1" && value > 1 then throw "constructed-run-boolean"
      return .cons value (← values types rest)
  | _, _ => .error "constructed-run-arity"

def inputs : (types : List String) → Values Token types →
    Values (Values Token) (types.map scalar)
  | [], .nil => .nil
  | _ :: types, .cons value rest => .cons (.cons value .nil) (inputs types rest)

structure Replay where
  entries : Array Json
  position : Nat := 0

def handler : PIR.Handler interface Replay Json := fun request state =>
  let asked := Json.arr #[.str request.operation.name, toJson (tokens request.arguments)]
  match state.entries[state.position]? with
  | none => ⟨.stopped .incomplete, state, [.arr #[asked, .str "missing"]]⟩
  | some entry =>
    let next := {state with position := state.position + 1}
    let event := Json.arr #[asked, entry]
    match entry with
    | .arr #[expected, .arr #[.str "return", .arr reply]] =>
      if expected != asked then ⟨.stopped .refused, next, [event]⟩
      else match values request.operation.results reply.toList with
        | .error _ => ⟨.stopped .refused, next, [event]⟩
        | .ok reply => ⟨.returned reply, next, [event]⟩
    | .arr #[expected, .arr #[.str "stop", reason]] =>
      if expected != asked then ⟨.stopped .refused, next, [event]⟩
      else match Source.Format.stop.decode reason with
        | .error _ => ⟨.stopped .refused, next, [event]⟩
        | .ok reason => ⟨.stopped reason, next, [event]⟩
    | _ => ⟨.stopped .refused, next, [event]⟩

def evaluate {s : Snapshot} (imported : Imported s) (json : Json) : Except String Json := do
  let .arr #[.str "zkc.constructed-run/0", .arr input, .arr entries] := json
    | throw "constructed-run-format"
  if entries.size > 2048 then throw "constructed-run-limit"
  let input ← values s.inputs input.toList
  let result := (imported.denote meaning (inputs s.inputs input)).run handler ⟨entries, 0⟩
  let outcome := match result.outcome with
    | .stopped reason => Json.arr #[.str "stopped", Source.Format.stop.encode reason]
    | .returned result => .arr #[.str "returned", toJson (tokens result)]
  return .arr #[.str "zkc.constructed-result/0", outcome,
    toJson result.state.position, toJson result.events]

end Zkc.Tools.Constructed
