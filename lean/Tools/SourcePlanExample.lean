import Examples.SourcePlan
import Tools.JsonSupport

/-! An executable example registry for the generic source/plan checker.
This tool checks external files and can run their logical plan with the example
bindings. Its executable, JSON parser and mathematical operation implementation
remain trusted runtime code; it does not produce a native-backend certificate.
-/

set_option autoImplicit false

open Lean Zkc.Source Zkc.Compiler Zkc.Tools SourcePlanExample

namespace SourcePlanTool

def valueJson : (ty : Ty) → Value ty → Json
  | .boolean, value => toJson value
  | .natural, value => toJson value
  | .field .five, value => toJson value.val
  | .field .seven, value => toJson value.val
  | .summary, (a, b, n) => .arr #[toJson a.val, toJson b.val, toJson n]

def process (requestPath planPath : System.FilePath) (invocation : Option (Bool × Nat)) : IO UInt32 := do
  let requestJson ← match ← readJson requestPath with
    | .error error => return ← refused error
    | .ok json => pure json
  let planJson ← match ← readJson planPath with
    | .error error => return ← refused error
    | .ok json => pure json
  let request ← match requestCodec.decode requestJson with
    | .error error => return ← refused error.code
    | .ok request => pure request
  let candidate ← match candidateCodec.decode planJson with
    | .error error => return ← refused error.code
    | .ok candidate => pure candidate
  if request.context.dependencies != dependencies then return ← refused "unresolved-dependency"
  let accepted ← match checkCandidate (language := language) request candidate with
    | .error error => return ← refused error.code
    | .ok accepted => pure accepted
  match invocation with
  | none =>
    emit (Json.mkObj [("status", .str "checked"), ("claim", .str "complete-logical-execution"),
      ("realization", .str "direct-logical-plan")])
    return 0
  | some (enabled, counter) =>
    if workBound candidate.body > 100000 then return ← refused "execution-work-limit"
    let inputs ← match bindInputs request.context.role request.context.inputs (supplied enabled counter) with
      | .error error => return ← refused error.code
      | .ok inputs => pure inputs
    let result := accepted.checked.plan.run meaning handler inputs.get 0
    let outcome := match result.outcome with
      | .returned value => .arr #[.str "returned", valueJson request.context.resultType value]
      | .stopped reason => .arr #[.str "stopped", Format.stop.encode reason]
    emit (Json.mkObj [("status", .str "executed"), ("outcome", outcome),
      ("state", toJson result.state), ("events", toJson result.events)])
    return 0

def dispatch : List String → IO UInt32
  | ["write", requestPath, planPath] => do
    IO.FS.writeFile requestPath ((requestCodec.encode request).pretty ++ "\n")
    IO.FS.writeFile planPath ((candidateCodec.encode candidate).pretty ++ "\n")
    return 0
  | ["check", requestPath, planPath] => process requestPath planPath none
  | ["run", requestPath, planPath, enabled, counter] => do
    let enabled ← match enabled with
      | "true" => pure true
      | "false" => pure false
      | _ => return ← refused "expected-boolean"
    let some counter := counter.toNat? | return ← refused "expected-natural"
    process requestPath planPath (some (enabled, counter))
  | _ => do
    (← IO.getStderr).putStrLn
      "usage: source-plan-example write|check REQUEST PLAN\n       source-plan-example run REQUEST PLAN true|false COUNTER"
    return 2

end SourcePlanTool

def main (args : List String) : IO UInt32 := do
  try SourcePlanTool.dispatch args
  catch _ => refused "io-error"
