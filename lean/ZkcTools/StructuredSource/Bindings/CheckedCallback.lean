module

public meta import ZkcTools.StructuredSource.Bindings.CallbackView
public meta import ZkcTools.Generation.Commands
public import Zkc.Source.Structured.Bindings.Selection

public meta section
namespace ZkcTools.StructuredSource.Bindings
open Zkc.Source.Structured.Bindings
open Lean Elab Command

def elaborateCallback (name source : String) (ordinal : Nat) (selected : RepeatSite) : CommandElabM Unit :=
  ZkcTools.Generation.Commands.atomic "checked_callback" do
    for decl in callbackDeclarations name source ordinal selected do
      match Parser.runParserCategory (← getEnv) `command decl with
      | .error reason => throwError "checked_callback: {reason}"
      | .ok stx => elabCommand stx

/-- The ordinal only selects a candidate. The resulting equality checks all
of its operand, body and continuation fields against the original. -/
elab "checked_callback " name:ident " := " body:ident " at " index:num : command => do
  let n := quote name.getId.toString
  let source := quote body.getId.toString
  let selected ← `((Zkc.Source.Structured.Bindings.checkedRepeat $index $body (by kernel_rfl)).repeatSite)
  elabCommand (← `(command| run_cmd elaborateCallback $n $source $index $selected))

end ZkcTools.StructuredSource.Bindings
