import Examples.InteractiveRound
import Tools.JsonSupport

/-! Consumer-selected phase admission for an independently retained source and
an exported logical plan. The example profile fixes the vocabulary revision,
local role, initial phase and permitted normal-return phases. Untrusted
certificates supply only checked loop annotations, never these profile choices.
-/

set_option autoImplicit false

open Lean Zkc.Source Zkc.Compiler Zkc.Tools InteractiveRound PhaseAdmission

namespace InteractiveRoundTool

def callJson : Call → Json
  | .commit value => .arr #[.str "commit", toJson value]
  | .challenge => .arr #[.str "challenge"]
  | .respond value => .arr #[.str "respond", toJson value]

def valueJson : (ty : Ty) → Value ty → Json
  | .boolean, value => toJson value
  | .natural, value => toJson value

def process (requestPath planPath : System.FilePath) (certificatePath : Option System.FilePath)
    (invocation : Option (Bool × Nat)) : IO UInt32 := do
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
  if request.context.role != "prover" then return ← refused "unsupported-role"
  let accepted ← match checkCandidate (language := language) request candidate with
    | .error error => return ← refused error.code
    | .ok accepted => pure accepted
  let some certificatePath := certificatePath | do
    emit (Json.mkObj [("status", .str "checked"), ("claim", .str "complete-logical-execution")])
    return 0
  let json ← match ← readJson certificatePath with
    | .error error => return ← refused error
    | .ok json => pure json
  let certificate ← match (certificateCodec phaseCodec 256).decode json with
    | .error error => return ← refused error.code
    | .ok certificate => pure certificate
  let some _admitted := admit policy accepted.source certificate [.ready] [.ready]
    | return ← refused "phase-not-admitted"
  match invocation with
  | none =>
    emit (Json.mkObj [("status", .str "admitted"), ("profile", .str "interactive-round/1"),
      ("claim", .str "phase-conformance-and-normal-return")])
    return 0
  | some (enabled, value) =>
    if workBound candidate.body > 100000 then return ← refused "execution-work-limit"
    let inputs ← match bindInputs request.context.role request.context.inputs (supplied enabled value) with
      | .error error => return ← refused error.code
      | .ok inputs => pure inputs
    let result := accepted.checked.plan.run meaning (PIR.ExecutionPath.handler interaction handler)
      inputs.get (.ready, 0)
    let outcome := match result.outcome with
      | .returned value => .arr #[.str "returned", valueJson request.context.resultType value]
      | .stopped reason => .arr #[.str "stopped", Format.stop.encode reason]
    let calls := result.events.filterMap fun
      | .inl (phase, op) => some (.arr #[phaseCodec.encode phase, callJson op])
      | .inr _ => none
    let events := result.events.filterMap fun
      | .inl _ => none
      | .inr event => some (callJson event)
    emit (Json.mkObj [("status", .str "executed"), ("outcome", outcome),
      ("phase", phaseCodec.encode result.state.1), ("state", toJson result.state.2),
      ("calls", .arr calls.toArray), ("events", .arr events.toArray)])
    return 0

def dispatch : List String → IO UInt32
  | ["write", requestPath, planPath, certificatePath] => do
    IO.FS.writeFile requestPath ((requestCodec.encode request).pretty ++ "\n")
    IO.FS.writeFile planPath ((candidateCodec.encode candidate).pretty ++ "\n")
    IO.FS.writeFile certificatePath (((certificateCodec phaseCodec 256).encode certificate).pretty ++ "\n")
    return 0
  | ["check", requestPath, planPath] => process requestPath planPath none none
  | ["admit", requestPath, planPath, certificatePath] =>
    process requestPath planPath (some certificatePath) none
  | ["run", requestPath, planPath, certificatePath, enabled, value] => do
    let enabled ← match enabled with
      | "true" => pure true
      | "false" => pure false
      | _ => return ← refused "expected-boolean"
    let some value := value.toNat? | return ← refused "expected-natural"
    process requestPath planPath (some certificatePath) (some (enabled, value))
  | _ => do
    (← IO.getStderr).putStrLn
      "usage: interactive-round write REQUEST PLAN CERTIFICATE\n       interactive-round check REQUEST PLAN\n       interactive-round admit REQUEST PLAN CERTIFICATE\n       interactive-round run REQUEST PLAN CERTIFICATE true|false VALUE"
    return 2

end InteractiveRoundTool

def main (args : List String) : IO UInt32 := do
  try InteractiveRoundTool.dispatch args
  catch _ => refused "io-error"
