import Examples.VectorService.Format
import Tools.SourceConsumer

/-! Independent reference and consumer-installed checker for vector-service/1. -/
set_option autoImplicit false
open Lean Zkc.Source Zkc.Compiler Zkc.Tools VectorService

private def codec : SourceConsumer.InvocationCodec Value State Event :=
  ⟨suppliedInput, decodeState, valueJson, stateJson, eventJson⟩
private def run (args : List String) : IO UInt32 := do
  let (mode, source, plan, invocation) ← match args with
    | ["check", s, p] => pure ("check", s, p, "")
    | ["run", s, p, i] => pure ("run", s, p, i)
    | _ => return ← refused "usage: vector-service check SOURCE PLAN | run SOURCE PLAN INPUTS"
  let accepted ← match SourceConsumer.check (language := language) types operations dependencies
      (← SourceConsumer.load source) (← SourceConsumer.load plan) with
    | .error code => return ← refused code
    | .ok value => pure value
  if mode == "check" then return ← SourceConsumer.checked
  if accepted.work > 100000 then return ← refused "execution-work-limit"
  SourceConsumer.report (SourceConsumer.execute codec accepted.context (fun _ _ => pure ())
    (fun env state => (accepted.region.denote meaning env).run handler state)
    (← SourceConsumer.load invocation))
def main (args : List String) : IO UInt32 := do
  try run args catch error => refused error.toString
