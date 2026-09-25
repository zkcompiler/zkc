import Examples.TablePhysical.Format
import Examples.TablePhysical.Admission
import Tools.TableAdmission
import Tools.SourceConsumer

/-! Source-relative physical checking, optional phase admission and execution.
Final scalar references are read in their actual completion store. Endpoint
execution instruments logical provider calls inside the physical interpreter.
-/

set_option autoImplicit false
open Lean Zkc.Source Zkc.Compiler Zkc.Tools TableProtocol

private def executionJson {S E : Type} {ty : Ty}
    (stateJson : S → Json) (event : E → Option Protocol.Trace)
    (out : PIR.Execution (TablePhysical.State S) E (TablePhysical.Value ty)) : Except String Json := do
  let (outcome, finalRead) ← match out.outcome with
    | .returned value => do
      let some logical := TablePhysical.decode out.state.store ty value | throw "invalid-result-reference"
      pure (Json.arr #[.str "returned", valueJson ty logical],
        TablePhysical.readCost out.state.store ty value)
    | .stopped why => pure (.arr #[.str "stopped", Format.stop.encode why], 0)
  let execution := Json.mkObj [("status", .str "executed"), ("outcome", outcome),
    ("state", stateJson out.state.logical),
    ("events", .arr ((out.events.filterMap event).map traceJson).toArray)]
  return Json.mkObj [("execution", execution), ("table-evaluations", toJson (out.state.evaluations + finalRead)),
    ("scalar-cells", toJson ((out.state.store .two).length + (out.state.store .seven).length))]

private def invoke {context : CompilationContext Ty}
    (program : Region TablePhysical.language (context.inputs.map (·.type)) context.resultType)
    (phase : Option TableAdmission.Request) (entry : Option Endpoint.Entry)
    (invocation : Json) : Except String Json := do
  let (inputs, jsonState) ← match invocation.getArr? with
    | .ok #[inputs, state] => pure (inputs, state)
    | _ => throw "invalid-invocation"
  let (state, current) ← match entry with
    | none => do pure (← decodeState jsonState, none)
    | some expected => do
      let actual ← Endpoint.decodeState jsonState
      Endpoint.validateEntry expected actual
      pure (actual.data, some actual.entry)
  let inputs ← inputs.getArr?.mapError (fun _ => "invalid-inputs")
  let supplied ← inputs.toList.mapM suppliedInput
  let values ← bindInputs context.role context.inputs supplied |>.mapError (·.code)
  let env : Environment TablePhysical.Value (context.inputs.map (·.type)) :=
    TablePhysical.inputs values.get
  match phase with
  | none =>
    executionJson stateJson some ((program.denote TablePhysical.meaning env).run
      (TablePhysical.handler Protocol.handler) {logical := state})
  | some _ =>
    let initial := current.map (·.phase) |>.getD Admission.Phase.ready
    let out := TablePhysical.Admission.run Protocol.handler program env {logical := (initial, state)}
    let stateJson := fun final => match current with
      | none => stateJson final.2
      | some actual => Endpoint.stateJson ⟨⟨actual.actor, final.1⟩, final.2⟩
    executionJson stateJson (fun | .inl _ => none | .inr event => some event) out

private def run (args : List String) : IO UInt32 := do
  let (command, sourceFile, target, input, phase) ← match args with
    | ["lower", mode, source] => pure ("lower", source, mode, "", none)
    | ["check", source, candidate] => pure ("check", source, candidate, "", none)
    | ["run", source, candidate, inputs] => pure ("run", source, candidate, inputs, none)
    | ["admit", s, p, profile, c] =>
      pure ("check", s, p, "", some (TableAdmission.Request.mk profile (← SourceConsumer.load c) none))
    | ["run-admitted", s, p, i, profile, c] =>
      pure ("run", s, p, i, some (TableAdmission.Request.mk profile (← SourceConsumer.load c) none))
    | ["admit-entry", s, p, profile, c, e] =>
      pure ("check", s, p, "", some ⟨profile, ← SourceConsumer.load c, some (← SourceConsumer.load e)⟩)
    | ["run-entry", s, p, i, profile, c, e] =>
      pure ("run", s, p, i, some ⟨profile, ← SourceConsumer.load c, some (← SourceConsumer.load e)⟩)
    | _ => return ← refused "usage: table-physical-reference lower MODE SOURCE | check SOURCE CANDIDATE | run SOURCE CANDIDATE INPUTS | admit SOURCE CANDIDATE PROFILE CERTIFICATE | run-admitted SOURCE CANDIDATE INPUTS PROFILE CERTIFICATE | admit-entry SOURCE CANDIDATE PROFILE CERTIFICATE ENTRY | run-entry SOURCE CANDIDATE INPUTS PROFILE CERTIFICATE ENTRY"
  let request ← match TablePhysical.source (← SourceConsumer.load sourceFile) with
    | .error code => return ← refused code
    | .ok request => pure request
  let candidate ← if command == "lower" then do
      let mode ← match TablePhysical.decodeMode target with
        | .error code => return ← refused code
        | .ok mode => pure mode
      pure (TablePhysical.Candidate.mk request.context (TablePhysical.propose mode request.source) .reference)
    else do
      match TablePhysical.candidateCodec.decode (← SourceConsumer.load target) with
      | .error error => return ← refused error.code
      | .ok candidate => pure candidate
  if phase.isSome && candidate.profile != .native then return ← refused "unsupported-physical-phase"
  let accepted ← match TablePhysical.admit request candidate with
    | .error code => return ← refused code
    | .ok accepted => pure accepted
  let entry ← match TableAdmission.check request.context.role accepted.logical phase with
    | .error code => return ← refused code
    | .ok entry => pure entry
  if command == "lower" then
    emit (TablePhysical.candidateCodec.encode candidate)
    return 0
  if command == "check" then
    let fields := phase.toList.flatMap fun request =>
      [("phase-profile", .str request.profile)] ++ entry.toList.map (fun entry => ("entry", Endpoint.entryJson entry))
    emit (Json.mkObj ([("status", .str "checked"), ("claim", .str "complete-logical-execution"),
      ("realization", .str candidate.profile.realization)] ++ fields))
    return 0
  if candidate.body.workBound > 100000 then return ← refused "execution-work-limit"
  SourceConsumer.report (invoke accepted.physical phase entry (← SourceConsumer.load input))

def main (args : List String) : IO UInt32 := do
  try run args catch error => refused error.toString
