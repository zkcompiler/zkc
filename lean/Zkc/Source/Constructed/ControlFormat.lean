module

public import Zkc.Source.Constructed.Control
public import Zkc.Source.Constructed.Format

@[expose] public section

namespace Zkc.Source.Constructed.Control
open Lean

structure Snapshot where
  source : String
  candidate : String
  entry : String
  role : String
  participant : String
  policy : String
  handlers : List Handler
  inputs : List String
  outputs : List String
  body : RawBody
  deriving DecidableEq, Repr

/-- A conservative structural expansion limit for the executable import profile.
It is not a native work theorem or a cryptographic adversary cost. -/
def RawBody.expansionBound : RawBody → Nat
  | .flat instructions _ => instructions.length + 1
  | .sequence _ first next => 1 + first.expansionBound + next.expansionBound
  | .branch _ yes no => 1 + max yes.expansionBound no.expansionBound
  | .loop maximum _ _ _ _ _ body next => 1 + maximum * (body.expansionBound + 1) + next.expansionBound

def RawBody.instructionCount : RawBody → Nat
  | .flat instructions _ => instructions.length
  | .sequence _ first next => first.instructionCount + next.instructionCount
  | .branch _ yes no => yes.instructionCount + no.instructionCount
  | .loop _ _ _ _ _ _ body next => body.instructionCount + next.instructionCount

def Snapshot.shapeValid (s : Snapshot) : Bool :=
  !s.entry.isEmpty && !s.role.isEmpty && !s.participant.isEmpty &&
  s.source.toList.take 7 == "sha256:".toList && s.source.length == 71 &&
  s.candidate.toList.take 7 == "sha256:".toList && s.candidate.length == 71 &&
  s.inputs.length ≤ 512 && s.outputs.length ≤ 512 && s.handlers.length ≤ 256 &&
  (s.handlers.map Handler.name).eraseDups.length == s.handlers.length &&
  s.body.instructionCount ≤ 2048 && s.body.expansionBound ≤ 65536

structure Imported (s : Snapshot) where
  program : Body s.inputs s.outputs

def Snapshot.check (s : Snapshot) : Except String (Imported s) := do
  if !s.shapeValid then throw "constructed-control-shape"
  return ⟨← s.body.elaborate s.inputs s.outputs⟩

def Snapshot.imported (s : Snapshot) (checked : s.check.isOk = true) : Imported s :=
  match eq : s.check with
  | .ok imported => imported
  | .error _ => by simp [eq, Except.isOk, Except.toBool] at checked

theorem Snapshot.imported_checked (s : Snapshot) (checked : s.check.isOk = true) :
    s.check = .ok (s.imported checked) := by
  unfold Snapshot.imported
  split
  · assumption
  · rename_i e eq
    rw [eq] at checked
    contradiction

theorem Snapshot.check_elaborate {s : Snapshot} {imported : Imported s}
    (checked : s.check = .ok imported) :
    s.body.elaborate s.inputs s.outputs = .ok imported.program := by
  unfold Snapshot.check at checked
  split at checked
  · contradiction
  · cases formed : s.body.elaborate s.inputs s.outputs with
    | error e => simp [formed] at checked; cases checked
    | ok program => simp [formed] at checked; cases checked; rfl

theorem Snapshot.check_denotation {s : Snapshot} {imported : Imported s}
    (checked : s.check = .ok imported) {I : PIR.Signature} (meaning : Meaning I)
    (values : Values meaning.Value s.inputs) :
    s.body.denote meaning s.outputs values = imported.program.denote meaning values :=
  RawBody.denote_elaborate meaning s.body imported.program (Snapshot.check_elaborate checked) values

namespace Format

def body : Nat → Json → Constructed.Format.Decode RawBody
  | 0, _ => .error .depthLimit
  | depth + 1, json => do
      match ← Source.Format.array json with
      | [.str "flat", instructions, returned] =>
          return .flat (← Constructed.Format.list Constructed.Format.instruction instructions)
            (← Constructed.Format.list Constructed.Format.natural returned)
      | [.str "sequence", intermediate, first, next] =>
          return .sequence (← Constructed.Format.list Constructed.Format.text intermediate)
            (← body depth first) (← body depth next)
      | [.str "branch", condition, yes, no] =>
          return .branch (← Constructed.Format.natural condition) (← body depth yes) (← body depth no)
      | [.str "loop", maximum, count, carried, initial, captures, captured, iteration, next] =>
          return .loop (← Constructed.Format.natural maximum) (← Constructed.Format.natural count)
            (← Constructed.Format.list Constructed.Format.text carried)
            (← Constructed.Format.list Constructed.Format.natural initial)
            (← Constructed.Format.list Constructed.Format.text captures)
            (← Constructed.Format.list Constructed.Format.natural captured)
            (← body depth iteration) (← body depth next)
      | _ => throw .shape

def snapshot (json : Json) : Constructed.Format.Decode Snapshot := do
  match ← Source.Format.array json with
  | [.str "zkc.constructed-control/0", source, candidate, entry, role, participant,
      policy, handlers, inputs, outputs, control] =>
      return ⟨← Constructed.Format.text source, ← Constructed.Format.text candidate,
        ← Constructed.Format.text entry, ← Constructed.Format.text role,
        ← Constructed.Format.text participant, ← Constructed.Format.text policy,
        ← Constructed.Format.list Constructed.Format.handler handlers,
        ← Constructed.Format.list Constructed.Format.text inputs,
        ← Constructed.Format.list Constructed.Format.text outputs, ← body 64 control⟩
  | _ => throw .shape

end Format
end Zkc.Source.Constructed.Control
