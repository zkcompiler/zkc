import Tools.TableAdmission
import Tools.SourceConsumer

/-! Consumer-selected trace or stateful endpoint admission, sharing the direct
source/region checker and invocation driver with independent source libraries. -/
set_option autoImplicit false
open Lean Zkc.Source Zkc.Compiler Zkc.Tools TableProtocol

private def codec : SourceConsumer.InvocationCodec Value Protocol.State Protocol.Trace :=
  ⟨suppliedInput, decodeState, valueJson, stateJson, traceJson⟩
private def endpointCodec : SourceConsumer.InvocationCodec Value Endpoint.State Protocol.Trace :=
  ⟨suppliedInput, Endpoint.decodeState, valueJson, Endpoint.stateJson, traceJson⟩

private def run (args : List String) : IO UInt32 := do
  let (mode, source, plan, invocation, phase) ← match args with
    | ["check", s, p] => pure ("check", s, p, "", none)
    | ["run", s, p, i] => pure ("run", s, p, i, none)
    | ["admit", s, p, profile, c] => pure ("check", s, p, "", some (TableAdmission.Request.mk profile (← SourceConsumer.load c) none))
    | ["run-admitted", s, p, i, profile, c] => pure ("run", s, p, i, some (TableAdmission.Request.mk profile (← SourceConsumer.load c) none))
    | ["admit-entry", s, p, profile, c, e] =>
      pure ("check", s, p, "", some ⟨profile, ← SourceConsumer.load c, some (← SourceConsumer.load e)⟩)
    | ["run-entry", s, p, i, profile, c, e] =>
      pure ("run", s, p, i, some ⟨profile, ← SourceConsumer.load c, some (← SourceConsumer.load e)⟩)
    | _ => return ← refused "usage: table-protocol check SOURCE PLAN | run SOURCE PLAN INPUTS | admit SOURCE PLAN PROFILE CERTIFICATE | run-admitted SOURCE PLAN INPUTS PROFILE CERTIFICATE | admit-entry SOURCE PLAN PROFILE CERTIFICATE ENTRY | run-entry SOURCE PLAN INPUTS PROFILE CERTIFICATE ENTRY"
  let accepted ← match SourceConsumer.check (language := Protocol.language) types operations dependencies
      (← SourceConsumer.load source) (← SourceConsumer.load plan) with
    | .error code => return ← refused code
    | .ok value => pure value
  let entry ← match TableAdmission.check accepted.context.role accepted.region phase with
    | .error code => return ← refused code
    | .ok entry => pure entry
  if mode == "check" then
    let fields := phase.toList.flatMap fun request =>
      [("phase-profile", .str request.profile)] ++ entry.toList.map (fun entry => ("entry", Endpoint.entryJson entry))
    return ← SourceConsumer.checked fields
  if accepted.work > 100000 then return ← refused "execution-work-limit"
  let invocation ← SourceConsumer.load invocation
  match entry with
  | some entry =>
    SourceConsumer.report (SourceConsumer.execute endpointCodec accepted.context (fun actor state => do
      if actor != entry.actor then throw "endpoint-role-mismatch"
      Endpoint.validateEntry entry state)
      (fun env state => Endpoint.run (accepted.region.denote Protocol.meaning env) state) invocation)
  | none =>
    SourceConsumer.report (SourceConsumer.execute codec accepted.context (fun _ _ => pure ())
      (fun env state => (accepted.region.denote Protocol.meaning env).run Protocol.handler state) invocation)

def main (args : List String) : IO UInt32 := do
  try run args catch error => refused error.toString
