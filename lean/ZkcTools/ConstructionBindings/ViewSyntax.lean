module

public import Zkc.Construction.Participant
public import Lean

@[expose] public section

/-! Untrusted proposals for one constructed action and its existing generic
correspondence rule. Both the offline printer and elaborator use this table;
every emitted term is checked by the kernel against the actual instruction. -/
set_option autoImplicit false
namespace ZkcTools.StructuredSource.Constructed
open Zkc.Construction

def app (head : String) (arguments : List String) : String :=
  "(" ++ " ".intercalate (head :: arguments) ++ ")"
def literal {A : Type} [Repr A] (value : A) : String := "(" ++ (reprStr value).replace "\n" " " ++ ")"

def arguments := ["model", "program", "context"]

/-- Print one independent action and the corresponding generic proof rule. -/
def action (instruction : Instruction) (body : String × String) : Except String (String × String) :=
  let declared := literal instruction.results
  let references := literal instruction.operands
  let rule (name : String) (args : List String) : Except String (String × String) :=
    .ok (app ("View." ++ name) args, app ("Correspondence." ++ name) args)
  match instruction.operation, instruction.operands, instruction.body with
  | .receive site schema peer ty, [], [] =>
      rule "receive" [literal site, literal schema, literal peer, literal ty, declared]
  | .send site schema peer, [reference], [] =>
      rule "send" [literal site, literal schema, literal peer, toString reference, declared]
  | .indicesEmpty, [], [] => rule "indicesEmpty" [declared]
  | .indicesAppend, [coordinates, index], [] =>
      rule "indicesAppend" [toString coordinates, toString index, declared]
  | .observe suite template, [state, value, coordinates], [] =>
      let args := [literal suite, literal template, toString state, toString value,
        toString coordinates, declared]
      .ok (app "View.observe" ("context" :: args), app "Correspondence.observe" args)
  | .challenge suite field template, [state, coordinates], [] =>
      let args := [literal suite, literal field, literal template, toString state,
        toString coordinates, declared]
      .ok (app "View.challenge" ("context" :: args), app "Correspondence.challenge" args)
  | .localService port request template coordinates, _, [] =>
      let args := [literal port, literal request, literal template, literal coordinates,
        references, declared]
      .ok (app "View.localService" ("context" :: args), app "Correspondence.localService" args)
  | .calculate operation, _, [] =>
      let args := [literal operation, references, declared]
      .ok (app "View.calculation" ("model" :: args), app "Correspondence.calculation" args)
  | .call name, _, [] =>
      let args := [literal name, references, declared]
      .ok (app "View.helper" (["model", "program"] ++ args), app "Correspondence.helper" args)
  | .guard site, [condition], [] =>
      .ok (app "View.guard" [toString condition, declared],
       app "Correspondence.guard" [literal site, toString condition, declared])
  | .loop site maximum yielded, count :: initial, _ =>
      .ok (app "View.loop" [toString maximum, literal yielded, toString count,
        literal initial, declared, body.1],
       app "Correspondence.loop" [literal site, toString maximum, literal yielded,
        toString count, literal initial, declared, body.2])
  | _, _, _ => throw ("constructed-view-unsupported-shape: operation=" ++
      literal instruction.operation ++ "; operands=" ++ references ++ "; results=" ++
      declared ++ "; body-instructions=" ++ toString instruction.body.length)

/-- Compose a closed finite block without a generated source file. This is a
proposal only; unsupported instruction shapes refuse. Large production roots
may import a separately checked view to share their first elaboration. -/
def blockTerms (fuel : Nat) (instructions : List Instruction) : Except String (String × String) := do
  let fuel + 1 := fuel | throw "constructed-view-depth"
  let mut steps : List (String × String) := []
  for instruction in instructions do
    let body ← match instruction.operation with
      | .loop .. => blockTerms fuel instruction.body
      | _ => pure ("View.empty", "Correspondence.empty")
    steps := steps ++ [← action instruction body]
  return steps.foldr (fun step rest =>
    (app "View.sequence" [step.1, rest.1],
     app "Correspondence.sequence" [step.2, rest.2]))
    ("View.empty", "Correspondence.empty")
termination_by fuel

end ZkcTools.StructuredSource.Constructed
