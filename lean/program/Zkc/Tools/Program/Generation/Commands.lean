module

public meta import Lean.Elab.Command

public meta section

/-! Transactions for commands that generate several ordinary declarations.
Lean may report an elaboration error without throwing it; neither that case
nor an exception may leave a partially installed interface in the environment. -/

namespace ZkcTools.Generation.Commands
open Lean Elab Command

/-- Restore declarations, scopes, options and local attributes on failure.
Generated declarations are checked synchronously so delayed diagnostics cannot
escape the transaction. The caller's options are restored on success as well.
Interrupts and resource exceptions propagate to the caller unchanged. -/
def atomic (description : String) (action : CommandElabM Unit) : CommandElabM Unit := do
  let saved ← get
  try
    withScope (fun scope => { scope with opts := Elab.async.set scope.opts false }) action
    let errors := (← get).messages.toList.drop saved.messages.toList.length
      |>.filter (·.severity == .error)
    unless errors.isEmpty do
      throwError "{description}: {MessageData.joinSep (errors.map (·.data)) m!"\n"}"
  catch error =>
    set saved
    throw error

/-- A missing source spelling is an error, never an empty generated term. -/
def termText (stx : Syntax) : CommandElabM String :=
  match stx.reprint with
  | some text => pure text
  | none => throwErrorAt stx "cannot print the supplied term for a generated declaration"

end ZkcTools.Generation.Commands
