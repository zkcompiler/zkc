module

public import Zkc.Frontend.Elab.Statements

@[expose] public section

set_option autoImplicit false

/-!
# The elaboration of a function body

The families of forms are tied here into one recursion, and the body of a function instance is
elaborated with its parameters bound at the types of its signature.
-/

namespace Zkc.Frontend.Elab

open Syntax
open Static

/-- The recursion between the families of forms, tied once. -/
partial def recursion (_ : Unit) : Recursion where
  expr expr expected context state :=
    (elabExpr expr expected).run { context, recursion := recursion () } state
  stmts statements context state :=
    (elabStmts statements).run { context, recursion := recursion () } state

/-- Runs an elaboration from a fresh state, after the binders of a lowered declaration: its
value, and whether a binder of deployed code binds a linear value. -/
def runElab {α : Type} (context : Context) (locals : Nat) (action : ElabM α) :
    CompileM (α × State) := do
  action.run { context, recursion := recursion () } { nextLocal := locals }

/-- An expression that stands where no statement can take its refusal (a result of the body):
when it is refused, an error node at the type expected of it. -/
def recovered (span : Span) (type : ClosedType) (action : ElabM Typed.Expr) : ElabM Typed.Expr := do
  try action
  catch
    | .abandoned => return .error (info span type) #[]
    | other => throw other

/-- The typed body of a function at the types of its signature: its parameters bound, then its
statements and its value at the result type (FN4). -/
def elabFunctionBody (parameters : Array (Lowered.Binder × ClosedType)) (result : ClosedType)
    (body : Lowered.Expr) : ElabM Typed.FunctionBody := do
  let binders ← parameters.mapM fun (binder, type) => bindLocal binder type
  match body with
  | .block _ statements value =>
    let statements ← elabStmts statements
    return { parameters := binders, statements
             result := ← recovered value.span result (elabAt value result) }
  | value =>
    return { parameters := binders, statements := #[]
             result := ← recovered value.span result (elabAt value result) }

end Zkc.Frontend.Elab
