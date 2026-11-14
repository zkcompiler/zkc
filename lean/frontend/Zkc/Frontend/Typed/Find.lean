module

public import Zkc.Frontend.Typed.Tree

@[expose] public section

set_option autoImplicit false

/-!
# The node of a number

A refusal of the core names the number of a node. This finds the node of a number in a
numbered tree: an expression or a statement, and for the first `error` node of a body its
number.
-/

namespace Zkc.Frontend.Typed

/-- A node of a tree. -/
inductive Node where
  | expr (expr : Expr)
  | stmt (stmt : Stmt)
  deriving Inhabited

mutual
  /-- The node of a number among an expression and its parts. -/
  partial def Expr.find? (id : NodeId) (expr : Expr) : Option Node :=
    if expr.info.id == id then some (.expr expr) else
    match expr with
    | .literal .. | .staticValue .. | .local .. => none
    | .apply _ _ arguments => arguments.findSome? (Expr.find? id)
    | .construct _ _ parts => parts.findSome? (Expr.find? id)
    | .project _ target _ _ => target.find? id
    | .convert _ _ value _ => value.find? id
    | .conditional _ _ condition onTrue onFalse =>
      (condition.find? id).orElse fun _ => (onTrue.find? id).orElse fun _ => onFalse.find? id
    | .block _ statements result =>
      (statements.findSome? (Stmt.find? id)).orElse fun _ => result.find? id
    | .error _ evaluated => evaluated.findSome? (Expr.find? id)

  partial def Stmt.find? (id : NodeId) (stmt : Stmt) : Option Node :=
    let own : Option NodeId := match stmt with
      | .bind mark .. | .unpack mark .. | .update mark .. | .guard mark .. | .if mark ..
      | .match mark .. | .for mark .. | .scope mark _ | .event mark .. | .error mark _ => some mark.id
    if own == some id then some (.stmt stmt) else
    match stmt with
    | .bind _ _ value _ | .unpack _ _ value _ | .update _ _ value _ => value.find? id
    | .guard _ condition _ _ => condition.find? id
    | .if _ condition onTrue onFalse _ =>
      (condition.find? id).orElse fun _ =>
        (onTrue.findSome? (Stmt.find? id)).orElse fun _ => onFalse.findSome? (Stmt.find? id)
    | .match _ scrutinee _ _ cases _ =>
      (scrutinee.find? id).orElse fun _ =>
        cases.findSome? fun (.case _ _ _ body) => body.findSome? (Stmt.find? id)
    | .for _ (.loop _ domain _ body) _ =>
      (match domain with
        | .range start stop _ => (start.find? id).orElse fun _ => stop.find? id
        | .collection source _ _ => source.find? id).orElse fun _ =>
      match body with
      | .uniform statements values | .empty statements values =>
        (statements.findSome? (Stmt.find? id)).orElse fun _ => values.findSome? (Expr.find? id)
      | .stepped iterations => iterations.findSome? fun (Iteration.iteration _ statements values) =>
          (statements.findSome? (Stmt.find? id)).orElse fun _ => values.findSome? (Expr.find? id)
    | .scope _ body => body.findSome? (Stmt.find? id)
    | .event _ _ what =>
      match what with
      | .send _ payload _ _ => payload.find? id
      | .apply _ _ arguments specification _ _ =>
        (arguments.findSome? (Expr.find? id)).orElse fun _ =>
          specification.findSome? fun (_, value) => value.find? id
      | .draw .. | .sample .. | .attempt .. => none
    | .error .. => none
end

mutual
  /-- The number of the first `error` node of an expression, in the order of the tree. -/
  partial def Expr.firstError? : Expr → Option NodeId
    | .error info _ => some info.id
    | .literal .. | .staticValue .. | .local .. => none
    | .apply _ _ arguments => arguments.findSome? Expr.firstError?
    | .construct _ _ parts => parts.findSome? Expr.firstError?
    | .project _ target _ _ => target.firstError?
    | .convert _ _ value _ => value.firstError?
    | .conditional _ _ condition onTrue onFalse =>
      condition.firstError?.orElse fun _ => onTrue.firstError?.orElse fun _ => onFalse.firstError?
    | .block _ statements result =>
      (statements.findSome? Stmt.firstError?).orElse fun _ => result.firstError?

  partial def Stmt.firstError? : Stmt → Option NodeId
    | .error mark _ => some mark.id
    | .bind _ _ value _ | .unpack _ _ value _ | .update _ _ value _ => value.firstError?
    | .guard _ condition _ _ => condition.firstError?
    | .if _ condition onTrue onFalse _ =>
      condition.firstError?.orElse fun _ =>
        (onTrue.findSome? Stmt.firstError?).orElse fun _ => onFalse.findSome? Stmt.firstError?
    | .match _ scrutinee _ _ cases _ =>
      scrutinee.firstError?.orElse fun _ =>
        cases.findSome? fun (.case _ _ _ body) => body.findSome? Stmt.firstError?
    | .for _ (.loop _ domain _ body) _ =>
      (match domain with
        | .range start stop _ => start.firstError?.orElse fun _ => stop.firstError?
        | .collection source _ _ => source.firstError?).orElse fun _ =>
      match body with
      | .uniform statements values =>
        (statements.findSome? Stmt.firstError?).orElse fun _ => values.findSome? Expr.firstError?
      | .stepped iterations => iterations.findSome? fun (Iteration.iteration _ statements values) =>
          (statements.findSome? Stmt.firstError?).orElse fun _ => values.findSome? Expr.firstError?
      | .empty .. => none
    | .scope _ body => body.findSome? Stmt.firstError?
    | .event _ _ what =>
      match what with
      | .send _ payload _ _ => payload.firstError?
      | .apply _ _ arguments specification _ _ =>
        (arguments.findSome? Expr.firstError?).orElse fun _ =>
          specification.findSome? fun (_, value) => value.firstError?
      | .draw .. | .sample .. | .attempt .. => none
end

namespace FunctionBody

/-- The node of a number in the body of a function. -/
def find? (body : FunctionBody) (id : NodeId) : Option Node :=
  (body.statements.findSome? (Stmt.find? id)).orElse fun _ => body.result.find? id

/-- The number of the first `error` node of the body. -/
def firstError? (body : FunctionBody) : Option NodeId :=
  (body.statements.findSome? Stmt.firstError?).orElse fun _ => body.result.firstError?

end FunctionBody

namespace ProtocolBody

/-- The node of a number in the body of a protocol. -/
def find? (body : ProtocolBody) (id : NodeId) : Option Node :=
  (body.statements.findSome? (Stmt.find? id)).orElse fun _ =>
    body.results.findSome? fun result => result.value.find? id

end ProtocolBody

end Zkc.Frontend.Typed
