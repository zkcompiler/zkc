module

public import Zkc.Source.Constructed
public import Zkc.Source.Format

@[expose] public section

set_option autoImplicit false
namespace Zkc.Source.Constructed.Format
open Lean

abbrev Decode := Except Source.Format.Error

/-- Resource policy is separate from structural decoding. The executable runs
this gate before either flat or structured decoding. -/
def preflight : Nat → Json → Decode Unit
  | 0, _ => .error .depthLimit
  | depth + 1, .arr values => do
      for value in values do preflight depth value
  | _ + 1, .str value =>
      if value.utf8ByteSize > 262144 then .error .string else .ok ()
  | _ + 1, _ => .ok ()

def text : Json → Decode String := Source.Format.string

def list {α : Type} (decode : Json → Decode α) (json : Json) : Decode (List α) := do
  let values ← Source.Format.array json
  if values.length > 2048 then throw .shape
  values.mapM decode

def natural (json : Json) : Decode Nat := do
  let value ← Source.Format.natural json
  if value > 8192 then throw .natural
  return value

def primitive (json : Json) : Decode Primitive := do
  match ← Source.Format.array json with
  | [name, attrs, binding, origin, args, results] =>
    return ⟨← text name, ← text attrs, ← text binding, ← text origin,
      ← list text args, ← list text results⟩
  | _ => throw .shape

def instruction (json : Json) : Decode Instruction := do
  match ← Source.Format.array json with
  | [.str "apply", op, args] => return .apply (← primitive op) (← list natural args)
  | [.str "project", types, index, tuple] =>
      return .project (← list text types) (← natural index) (← natural tuple)
  | [.str "guard", condition, attrs] => return .guard (← natural condition) (← text attrs)
  | [.str "stop", reason, attrs] =>
      return .stop (← Source.Format.stop.decode reason) (← text attrs)
  | _ => throw .shape

def handler (json : Json) : Decode Handler := do
  match ← Source.Format.array json with
  | [name, digest, body] => return ⟨← text name, ← text digest, ← text body⟩
  | _ => throw .shape

def snapshot (json : Json) : Decode Snapshot := do
  match ← Source.Format.array json with
  | [.str "zkc.constructed-source/0", source, candidate, entry, role, participant,
      policy, handlers, inputs, outputs, instructions, returned] =>
    return ⟨← text source, ← text candidate, ← text entry, ← text role, ← text participant,
      ← text policy, ← list handler handlers, ← list text inputs, ← list text outputs,
      ← list instruction instructions, ← list natural returned⟩
  | _ => throw .shape

end Zkc.Source.Constructed.Format
