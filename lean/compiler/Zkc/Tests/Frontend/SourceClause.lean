import Zkc.Frontend.Written.Claim

/-!
The clause that a written soundness goal reads, as a reader of the source sees it: by the names
of the source, to compare with what a fixture says.
-/

namespace Zkc.Tests.Frontend.SourceClause
open Zkc.Frontend Zkc.Frontend.Written

/-- The head of the protocol that a root deploys, as the source wrote it. -/
def rootHead (c : AdmittedRoot) : Except String Lowered.ProtocolHead := do
  let some key := c.state.results.key? c.id | throw "missing the root"
  let some {content := .protocol head .., ..} := c.state.env.modules.lowered? key.declaration
    | throw "missing the protocol"
  return head

/-- What a reader of a selected clause sees, by the names of the source. -/
structure Seen where
  kind : String
  label : Option String
  role : String
  relation : String
  statement : List String
  witness : List String
  deriving BEq, Repr

/-- The clause from which a goal forms its claim, by the names of the source. -/
def seen (c : AdmittedRoot) (goal : String) : Except String Seen := do
  let clause ← goalClause c goal
  let head ← rootHead c
  let some application := clause.application | throw "the clause applies no relation"
  let port (operand : Lowered.Expr) : Except String String := match operand with
    | .local _ id => match head.ports.find? (·.binder.id == id) with
      | some found => pure found.binder.name
      | none => throw "an operand is no port"
    | _ => throw "an operand is no name"
  return {
    kind := if clause.kind == .proves then "proves" else "reduces"
    label := clause.label
    role := (clause.role.bind (head.roster[·]?)).getD "?"
    relation := c.state.program.nameOf application.relation
    statement := (← application.statement.mapM port).toList
    witness := (← application.witness.mapM port).toList }

/-- The names of the witness parameters of the relation that a goal's clause applies, from the
relation's declaration: the same whether the clause writes its witness operands or not. -/
def witnessParameters (c : AdmittedRoot) (goal : String) : Except String (List String) := do
  let clause ← goalClause c goal
  let some application := clause.application | throw "the clause applies no relation"
  let some {content := .function head _, ..} := c.state.env.modules.lowered? application.relation
    | throw "missing the relation's declaration"
  let some statement := head.statementParameters | throw "the clause applies no relation's declaration"
  return (head.parameters.toList.drop statement).map (·.binder.name)

end Zkc.Tests.Frontend.SourceClause
