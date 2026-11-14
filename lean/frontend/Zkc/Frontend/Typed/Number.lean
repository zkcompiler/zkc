module

public import Zkc.Frontend.Typed.Tree

@[expose] public section

set_option autoImplicit false

/-!
# The numbers of the nodes of a typed tree

Every expression and every statement of a definition gets a number: its place in the order of
the tree, depth first, a node before its parts and the parts in the order in which they stand.
The numbers of a definition are dense, from `0`.

The numbers are given after elaboration, in one walk. Elaboration types some forms more than
once (an arm at its joined type, a body once and then per iteration) and discards trees, so a
number drawn while elaborating would depend on what was tried. A number is the key of what the
passes compute for a node, and the tag by which a refusal of the core names the node.
-/

namespace Zkc.Frontend.Typed

namespace Number

abbrev NumberM := StateM NodeId

/-- The next number. -/
def next : NumberM NodeId := modifyGet fun count => (count, count + 1)

def mark (mark : Mark) : NumberM Mark := do return { mark with id := ← next }

def info (info : Info) : NumberM Info := do return { info with id := ← next }

mutual
  partial def expr : Expr → NumberM Expr
    | .literal found value => do return .literal (← info found) value
    | .staticValue found value source => do return .staticValue (← info found) value source
    | .local found binder => do return .local (← info found) binder
    | .apply found callee arguments => do
      let found ← info found
      return .apply found callee (← arguments.mapM expr)
    | .construct found what parts => do
      let found ← info found
      return .construct found what (← parts.mapM expr)
    | .project found target position name => do
      let found ← info found
      return .project found (← expr target) position name
    | .convert found conversion value quote => do
      let found ← info found
      return .convert found conversion (← expr value) quote
    | .conditional found form condition onTrue onFalse => do
      let found ← info found
      let condition ← expr condition
      let onTrue ← expr onTrue
      return .conditional found form condition onTrue (← expr onFalse)
    | .block found statements result => do
      let found ← info found
      let statements ← stmts statements
      return .block found statements (← expr result)
    | .error found evaluated => do
      let found ← info found
      return .error found (← evaluated.mapM expr)

  partial def stmts (statements : Array Stmt) : NumberM (Array Stmt) := statements.mapM stmt

  partial def stmt : Stmt → NumberM Stmt
    | .bind found binder value placement => do
      let found ← mark found
      return .bind found binder (← expr value) placement
    | .unpack found binders value placement => do
      let found ← mark found
      return .unpack found binders (← expr value) placement
    | .update found target value placement => do
      let found ← mark found
      return .update found target (← expr value) placement
    | .guard found condition reason placement => do
      let found ← mark found
      return .guard found (← expr condition) reason placement
    | .if found condition onTrue onFalse control => do
      let found ← mark found
      let condition ← expr condition
      let onTrue ← stmts onTrue
      return .if found condition onTrue (← stmts onFalse) control
    | .match found scrutinee binder «variant» cases control => do
      let found ← mark found
      let scrutinee ← expr scrutinee
      let cases ← cases.mapM fun (.case span alternatives payload body) => do
        return Case.case span alternatives payload (← stmts body)
      return .match found scrutinee binder «variant» cases control
    | .for found (.loop index domain collected body) control => do
      let found ← mark found
      let domain ← match domain with
        | .range start stop count => do
          let start ← expr start
          pure (Domain.range start (← expr stop) count)
        | .collection source item size => do pure (Domain.collection (← expr source) item size)
      let body ← match body with
        | .uniform statements values => do
          let statements ← stmts statements
          pure (LoopBody.uniform statements (← values.mapM expr))
        | .stepped iterations => do
          pure (LoopBody.stepped (← iterations.mapM fun (.iteration index statements values) => do
            let statements ← stmts statements
            return Iteration.iteration index statements (← values.mapM expr)))
        | .empty statements values => do
          let statements ← stmts statements
          pure (LoopBody.empty statements (← values.mapM expr))
      return .for found (.loop index domain collected body) control
    | .scope found body => do
      let found ← mark found
      return .scope found (← stmts body)
    | .event found number what => do
      let found ← mark found
      let what ← match what with
        | .send binder payload sender receivers => do
          pure (Event.send binder (← expr payload) sender receivers)
        | .apply results callee arguments specification roleMap order => do
          let arguments ← arguments.mapM expr
          let specification ← specification.mapM fun (port, value) => do return (port, ← expr value)
          pure (Event.apply results callee arguments specification roleMap order)
        | other => pure other
      return .event found number what
    | .error found binders => do return .error (← mark found) binders
end

def body : Body → NumberM Body
  | .function found => do
    let statements ← stmts found.statements
    return .function { found with statements, result := ← expr found.result }
  | .protocol found => do
    let statements ← stmts found.statements
    let results ← found.results.mapM fun result => do
      return { result with value := ← expr result.value }
    return .protocol { found with statements, results }
  | other => pure other

end Number

/-- A body with its nodes numbered, and the count of its nodes. -/
def Body.numbered (body : Body) : Body × Nat := (Number.body body).run 0

end Zkc.Frontend.Typed
