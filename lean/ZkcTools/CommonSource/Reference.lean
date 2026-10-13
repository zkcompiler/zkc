module

public import Zkc.Source.Common.Format
public import Zkc.Source.Common.Scalar
public import ZkcTools.JsonSupport
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

/-! Executable common-source reference with explicitly supplied open replies.

The selected finite model uses ZMod 97 for scalar and additive group carriers.
It does not implement a native curve or infer random sampling. The replay trace
retains every attempted request, reply, stop and consumed-reply position.
-/

set_option autoImplicit false

namespace ZkcTools.CommonSource

open Lean Zkc.Source Zkc.Source.Common Zkc.Source.Common.Native

instance : Fact (Nat.Prime 97) := ⟨by decide⟩
abbrev F := ZMod 97
abbrev meaning := scalarMeaning F F

def encodeType : Ty → Json
  | .boolean => .arr #[.str "bool"]
  | .field domain => .arr #[.str "field", .str domain]
  | .group domain => .arr #[.str "group", .str domain]
  | .service contract => .arr #[.str "service", .str contract]

def encodeValue : (ty : Ty) → ScalarValue F F ty → Json
  | .boolean, value => .bool value
  | .field _, value | .group _, value => toJson value.val
  | .service _, value => toJson value

def decodeValue : (ty : Ty) → Json → Except String (ScalarValue F F ty)
  | .boolean, .bool value => .ok value
  | .boolean, _ => .error "common-run-boolean"
  | .field _, json | .group _, json => do
      let value ← Zkc.Source.Format.natural json |>.mapError fun _ => "common-run-scalar"
      if value ≥ 97 then throw "common-run-scalar"
      return value
  | .service _, json => do
      let value ← Zkc.Source.Format.natural json |>.mapError fun _ => "common-run-handle"
      if value > 65535 then throw "common-run-handle"
      return value

def decodeInputs : (types : List Ty) → List Json →
    Except String (Values (fun ty => Option (ScalarValue F F ty)) types)
  | [], [] => .ok .nil
  | ty :: types, json :: values => do
      let value ← match json with
        | .null => pure none
        | _ => some <$> decodeValue ty json
      return .cons value (← decodeInputs types values)
  | _, _ => .error "common-run-inputs"

def inputsMatch {types : List Ty} (role : Nat) :
    Values (fun _ => Nat → Bool) types → Values (fun ty => Option (ScalarValue F F ty)) types → Bool
  | .nil, .nil => true
  | .cons scope scopes, .cons value values =>
      value.isSome == scope role && inputsMatch role scopes values

def request : Action Nat language services meaning.Value → Json
  | .send (ty := ty) site receiver value =>
      .arr #[.str "send", .str site, toJson receiver, encodeType ty, encodeValue ty value]
  | .receive ty site sender => .arr #[.str "receive", .str site, toJson sender, encodeType ty]
  | .query site field (.cons handle .nil) =>
      .arr #[.str "draw", .str site, .str field, toJson handle]

def reply (action : Action Nat language services meaning.Value) (json : Json) :
    Except String ((interface Nat language services meaning.Value).Reply action) :=
  match action with
  | .send .. => if json == .null then .ok () else .error "common-run-send-reply"
  | .receive ty .. => decodeValue ty json
  | .query _ field _ => decodeValue (.field field) json

structure Replay where
  entries : Array Json
  position : Nat := 0

def handler : PIR.Handler (interface Nat language services meaning.Value) Replay Json :=
  fun action state =>
    let asked := request action
    match state.entries[state.position]? with
    | none => ⟨.stopped .incomplete, state, [.arr #[asked, .arr #[.str "missing"]]]⟩
    | some entry =>
        let next := { state with position := state.position + 1 }
        let event := Json.arr #[asked, entry]
        match entry with
        | .arr #[expected, .arr #[.str "return", value]] =>
            if expected != asked then ⟨.stopped .refused, next, [event]⟩
            else match reply action value with
              | .error _ => ⟨.stopped .refused, next, [event]⟩
              | .ok value => ⟨.returned value, next, [event]⟩
        | .arr #[expected, .arr #[.str "stop", reason]] =>
            if expected != asked then ⟨.stopped .refused, next, [event]⟩
            else match Zkc.Source.Format.stop.decode reason with
              | .error _ => ⟨.stopped .refused, next, [event]⟩
              | .ok reason => ⟨.stopped reason, next, [event]⟩
        | _ => ⟨.stopped .refused, next, [event]⟩

def evaluate (imported : Imported) (json : Json) : Except String Json := do
  let .arr #[.str "zkc.common-run/0", role, .arr values, .arr replies] := json
    | throw "common-run-format"
  let role ← Zkc.Source.Format.natural role |>.mapError fun _ => "common-run-role"
  if role ≥ imported.snapshot.roles.length then throw "common-run-role"
  if replies.size > 2048 then throw "common-run-limit"
  let inputs ← decodeInputs imported.snapshot.inputs values.toList
  if !inputsMatch role imported.scopes inputs then throw "common-run-input-scopes"
  let result := (imported.denote meaning id role inputs).run handler ⟨replies, 0⟩
  let outcome := match result.outcome with
    | .stopped reason => Json.arr #[.str "stopped", Zkc.Source.Format.stop.encode reason]
    | .returned value => .arr #[.str "returned", match value with
        | none => .null
        | some value => encodeValue imported.snapshot.result value]
  return .arr #[.str "zkc.common-result/0", outcome, toJson result.state.position, toJson result.events]

def read (path : System.FilePath) : IO (Except String Json) := do
  try
    IO.FS.withFile path .read fun handle => do
      let mut bytes := ByteArray.empty
      while bytes.size ≤ 1024 * 1024 do
        let chunk ← handle.read (min 65536 (1024 * 1024 + 1 - bytes.size)).toUSize
        if chunk.isEmpty then break
        bytes := bytes ++ chunk
      if bytes.size > 1024 * 1024 then return .error "byte-limit"
      let some text := String.fromUTF8? bytes | return .error "invalid-utf8"
      return Format.parse text
  catch _ => return .error "common-source-io"

end ZkcTools.CommonSource
