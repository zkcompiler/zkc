module

public import Zkc.Frontend.Typed.Checked

@[expose] public section
set_option autoImplicit false
namespace Zkc.Frontend.Emit

mutual
  /-- The function instances that an expression applies, added to those found, each once. -/
  partial def calledInExpr (found : Array InstanceId) : Typed.Expr → Array InstanceId
    | .literal .. | .staticValue .. | .local .. => found
    | .apply _ callee arguments =>
      let found := match callee with
        | .instance inst => if found.contains inst then found else found.push inst
        | _ => found
      arguments.foldl calledInExpr found
    | .construct _ _ parts => parts.foldl calledInExpr found
    | .project _ target _ _ => calledInExpr found target
    | .convert _ _ value _ => calledInExpr found value
    | .conditional _ _ condition onTrue onFalse =>
      calledInExpr (calledInExpr (calledInExpr found condition) onTrue) onFalse
    | .block _ statements result => calledInExpr (statements.foldl calledInStmt found) result
    | .error _ evaluated => evaluated.foldl calledInExpr found

  partial def calledInStmt (found : Array InstanceId) : Typed.Stmt → Array InstanceId
    | .bind _ _ value _ | .unpack _ _ value _ | .update _ _ value _ => calledInExpr found value
    | .guard _ condition _ _ => calledInExpr found condition
    | .if _ condition onTrue onFalse _ =>
      onFalse.foldl calledInStmt (onTrue.foldl calledInStmt (calledInExpr found condition))
    | .match _ scrutinee _ _ cases _ =>
      cases.foldl (init := calledInExpr found scrutinee) fun found (.case _ _ _ body) =>
        body.foldl calledInStmt found
    | .for _ (.loop _ domain _ body) _ =>
      let found := match domain with
        | .range start stop _ => calledInExpr (calledInExpr found start) stop
        | .collection source _ _ => calledInExpr found source
      match body with
      | .uniform statements values => values.foldl calledInExpr (statements.foldl calledInStmt found)
      | .stepped iterations =>
        iterations.foldl (init := found) fun found (Typed.Iteration.iteration _ statements values) =>
          values.foldl calledInExpr (statements.foldl calledInStmt found)
      | .empty .. => found
    | .scope _ body => body.foldl calledInStmt found
    | .event _ _ what =>
      match what with
      | .send _ payload _ _ => calledInExpr found payload
      | .apply _ _ arguments _ _ _ => arguments.foldl calledInExpr found
      | .draw .. | .sample .. | .attempt .. => found
    | .error .. => found
end

/-- The function instances that a body applies, each once. -/
def calledIn (body : Typed.FunctionBody) : Array InstanceId :=
  calledInExpr (body.statements.foldl calledInStmt #[]) body.result

/-- The protocol instances that statements apply. -/
partial def appliedIn (found : Array InstanceId) (statements : Array Typed.Stmt) : Array InstanceId :=
  statements.foldl (init := found) fun found statement =>
    match statement with
    | .event _ _ (.apply _ callee ..) => if found.contains callee then found else found.push callee
    | .if _ _ onTrue onFalse _ => appliedIn (appliedIn found onTrue) onFalse
    | .match _ _ _ _ cases _ => cases.foldl (init := found) fun found (.case _ _ _ body) => appliedIn found body
    | .for _ (.loop _ _ _ body) _ =>
      match body with
      | .uniform statements _ => appliedIn found statements
      | .empty .. => found
      | .stepped iterations =>
        iterations.foldl (init := found) fun found (Typed.Iteration.iteration _ statements _) =>
          appliedIn found statements
    | .scope _ body => appliedIn found body
    | _ => found

/-- Runtime dependencies exclude source-only specification arguments and empty loop bodies. -/
def protocolFunctions (body : Typed.ProtocolBody) : Array InstanceId :=
  body.results.foldl (fun found result => calledInExpr found result.value)
    (body.statements.foldl calledInStmt #[])

end Zkc.Frontend.Emit
