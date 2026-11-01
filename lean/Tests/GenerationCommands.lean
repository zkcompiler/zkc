import ZkcTools.Generation.Commands

/-! A failed multi-declaration generator must roll back both thrown errors and
elaboration diagnostics. A partially installed interface is never reusable. -/
namespace Tests.GenerationCommands

open Lean Elab Command ZkcTools.Generation.Commands in
run_cmd do
  let asynchronous := Elab.async.get (← getOptions)
  atomic "synchronous-control" do
    if Elab.async.get (← getOptions) then
      throwError "generation permits delayed diagnostics"
  unless Elab.async.get (← getOptions) == asynchronous do
    throwError "generation changed the caller's options"
  for thrown in [false, true] do
    let name := mkIdent (if thrown then `Thrown else `Reported)
    let failed ← try
      atomic "transaction-control" do
        elabCommand (← `(command| def $name : Nat := 1))
        if thrown then throwError "controlled exception"
        elabCommand (← `(command| example : False := by constructor))
      pure false
    catch error =>
      if error.isRuntime || error.isInterrupt then throw error
      pure true
    unless failed do throwError "failed generation was accepted"
    if (← getEnv).contains (`Tests.GenerationCommands ++ name.getId) then
      throwError "failed generation left a declaration"

end Tests.GenerationCommands
