import Zkc.Frontend.Written.Export
import Zkc.Frontend.Driver.Files

open Zkc.Frontend

private def generate (input root : System.FilePath) (request : Written.Request)
    (scope : String) (proof : Bool) : IO UInt32 := do
  let assembly ← Driver.assembleFiles (← Driver.readSource input)
    [input.parent.getD ".", root / "libraries", root / "examples", root / "examples/support"]
  match Written.exportSelected assembly request proof scope with
  | .ok text => IO.print text; return 0
  | .error reason => IO.eprintln reason; return 1

private def usage : IO UInt32 := do
  IO.eprintln "usage: zkc-knowledge [--target-only] [--namespace NAME] [--clause LABEL] INPUT.zkc PROJECT_ROOT SCHEME_PATH"
  IO.eprintln "       zkc-knowledge [--target-only] [--namespace NAME] --goal GOAL_PATH INPUT.zkc PROJECT_ROOT"
  return 2

private def arguments (proof : Bool) (scope : String) (label goal : Option String) : List String → IO UInt32
  | "--target-only" :: rest => arguments false scope label goal rest
  | "--namespace" :: name :: rest => arguments proof name label goal rest
  | "--clause" :: name :: rest =>
    if label.isSome || goal.isSome then usage else arguments proof scope (some name) none rest
  | "--goal" :: name :: rest =>
    if label.isSome || goal.isSome then usage else arguments proof scope none (some name) rest
  | [input, root, scheme] =>
    if goal.isSome then usage else generate input root (.scheme scheme label) scope proof
  | [input, root] =>
    match goal with
    | some name => generate input root (.goal name) scope proof
    | none => usage
  | _ => usage

def main := arguments true "WrittenKnowledge" none none
