module

public import Zkc.Frontend.Elab.Function

@[expose] public section

set_option autoImplicit false

/-!
# The elaboration of a protocol body

The body of a protocol instance is elaborated once, to the typed tree: its ports bound at the
types of its head, its statements, and its results at the types of the head. No role takes part
in the typing: what the source writes of roles is kept on the nodes, and the placement pass
decides from it who computes what.

Every refusal of the body is reported: a statement that is refused is an error node, and the
statements after it are elaborated.
-/

namespace Zkc.Frontend.Elab

open Syntax
open Static

/-- The typed body of a protocol at the closed signature of its instance. -/
def elabProtocolBody (name : String) (signature : Typed.ProtocolSignature)
    (head : Lowered.ProtocolHead) (statements : Array Lowered.Stmt)
    (returned : Option Lowered.Expr) : ElabM Typed.ProtocolBody := do
  -- the ports: a `spec` port has no holder and is no value of deployed code
  let mut ports : Array Typed.BodyPort := #[]
  for (port, closed) in head.ports.zip signature.ports do
    let binder ← bindLocal port.binder closed.type
    if port.specification then
      modify fun state => { state with
        specificationPorts := state.specificationPorts.insert port.binder.id }
    else if port.holders.isEmpty then
      refuseHere "HO5" port.binder.span
        s!"port `{port.binder.name}` has no holders: write `{port.binder.name}: T @P`, or `spec {port.binder.name}: T`"
    ports := ports.push { binder, holders := port.holders, specification := port.specification }
  let statements ← elabStmts statements
  -- the results: one value per result of the head, the components of a returned tuple when the
  -- head has several
  let declared := signature.results
  let components : Array Lowered.Expr ← match returned, declared.size with
    | none, 0 => pure #[]
    | some value, 1 => pure #[value]
    | some value, count =>
      match value with
      | .tuple _ items _ =>
        if items.size == count then pure items
        else
          refuseHere "TY5" value.span
            s!"`{name}` returns {count} results; `{← textOf value.span}` has {items.size} components"
      | other => refuseHere "TY5" other.span s!"`{name}` returns {count} results: return a tuple of them"
    | none, _ => refuseHere "FN4" default s!"`{name}` returns its results with `return`"
  let mut results : Array Typed.BodyResult := #[]
  for (result, component) in declared.zip components do
    let value ← recovered component.span result.type (elabAt component result.type)
    results := results.push { name := result.name, value, holders := result.holders }
  return { roster := signature.roster, ports, statements, results }

end Zkc.Frontend.Elab
