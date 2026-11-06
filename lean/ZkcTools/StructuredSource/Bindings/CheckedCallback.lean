module

public meta import ZkcTools.StructuredSource.Bindings.CallbackView
public meta import ZkcTools.Generation.Commands
public import Zkc.Source.Structured.Bindings.RepeatPrefix

public meta section
namespace ZkcTools.StructuredSource.Bindings
open Zkc.Source.Structured.Bindings
open Lean Elab Command

private def emitChecked (name : String) (declarations : List String) : CommandElabM Unit :=
  ZkcTools.Generation.Commands.atomic name do
    for declaration in declarations do
      match Parser.runParserCategory (← getEnv) `command declaration with
      | .error reason => throwError "{name}: {reason}"
      | .ok stx => elabCommand stx

def elaborateCallback (name source : String) (ordinal : Nat) (selected : RepeatSite) (withContinuation : Bool) : CommandElabM Unit :=
  emitChecked "checked_callback" (callbackDeclarations name source ordinal selected withContinuation)

/-- The ordinal only selects a candidate. The resulting equality checks all
of its operand, body and continuation fields against the original. -/
elab "checked_callback " name:ident " := " body:ident " at " index:num continuation:(&"with_continuation")? : command => do
  let n := quote name.getId.toString
  let source := quote body.getId.toString
  let materialize := quote continuation.isSome
  let selected ← `((Zkc.Source.Structured.Bindings.checkedRepeat $index $body (by kernel_rfl)).repeatSite)
  elabCommand (← `(command| run_cmd elaborateCallback $n $source $index $selected $materialize))

open Zkc.Source Zkc.Source.Structured ZkcTools.StructuredSource.Presentation

/-- Render the linear prefix once. Its complete source equality remains
kernel checked, while downstream proofs can reduce the literal typed tree. -/
def elaboratePrefix {inputs outputs : List Ty} (name occurrence linear : String)
    (body : Region protocolDialect inputs outputs) : CommandElabM Unit := do
  let commands := ["def " ++ name ++ " : Region protocolDialect " ++ typesText inputs ++
    " " ++ typesText outputs ++ " :=\n  " ++ regionText body,
    "theorem " ++ name ++ "_exact : " ++ occurrence ++ ".beforeRepeat " ++ linear ++
      " = " ++ name ++ " := by kernel_rfl"]
  emitChecked "checked_repeat_prefix" commands

elab "checked_repeat_prefix " name:ident " := " occurrence:ident " using " linear:ident : command => do
  let n := quote name.getId.toString
  let o := quote occurrence.getId.toString
  let l := quote linear.getId.toString
  let body ← `((Zkc.Source.Structured.Bindings.RepeatAt.beforeRepeat $occurrence $linear))
  elabCommand (← `(command| run_cmd elaboratePrefix $n $o $l $body))

end ZkcTools.StructuredSource.Bindings
