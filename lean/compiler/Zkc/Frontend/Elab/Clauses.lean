module

public import Zkc.Frontend.Elab.Events

@[expose] public section

set_option autoImplicit false

/-!
# The conditions of a relation where a clause of a contract applies it

A `proves` clause and the source of a `reduces` clause apply a relation to ports of the
protocol. A `where` on the head of a relation is a condition of each application (SP4), and an
application in a clause is one. For a relation with such a condition, the application is taken
through what an application in an expression goes through up to its instance: its arguments are
paired with the statement and the witness of the relation, the static arguments of the relation
are inferred from the types of the operands, the relation is instantiated, and the `where` of
its head holds at that instance; when every proof argument of the relation has a value, the
condition holds at those values too. It is done at the ports of an instance of the protocol, in
a specification: the names of every role stand.

A clause is specification and runs nowhere. An application that waits for a later layer of the
language is left as it is and does not make the protocol wait. An application whose condition
does not hold, or whose relation has no instance at the operands, refuses the protocol.

Not done here. A relation without a condition is not instantiated, the operands are not
converted to the parameter types, and the body of the relation is not typed: the elaborator
does not type every specification expression of the examples yet (the sum of a table of field
elements in `Sum` of `examples/sumcheck.zkc`, the static arguments of `Outputs` of
`examples/gkr.zkc`), and a clause must not refuse a protocol for that. Also not done: the
relation of a `knowledge` clause, which is applied to its statement only; what a clause states
under the results or under the index of a loop; a formula that applies no relation; `requires`.
-/

namespace Zkc.Frontend.Elab

open Syntax
open Static

/-- What the deciding clauses of a contract state at the ports alone. -/
def decidingApplications (clauses : Array Lowered.Clause) : Array Lowered.Expr :=
  clauses.filterMap fun
    | .proves _ _ _ relation => some relation
    | .reduces _ _ _ source _ => some source
    | _ => none

/-- Whether a condition stands at the head of a declaration or of a scope around it. -/
def hasCondition (found : Declaration) : ElabM Bool := do
  let program := (← getThe Compile.State).program
  return found.scopes.any fun scope => (program.scopes[scope]?).any (·.whereClause.isSome)

/-- One application of a relation in a clause. An expression that applies no relation
declaration, or a relation without a condition, is left as it is. -/
def elabClauseApplication (expr : Lowered.Expr) : ElabM Unit := do
  let .call span callee arguments witnesses := expr | return
  let .declaration steps scopes ← calleeOf callee | return
  let some (id, _) := steps.back? | return
  let found ← liftM (declaration id : CompileM Declaration)
  let .relation node := found.node | return
  unless ← hasCondition found do return
  -- every specification-only parameter of the relation is given by a specification argument,
  -- or is the protocol's own where they share a scope (SP11)
  let state ← getThe Compile.State
  let context ← getContext
  let some entry := state.table.entries[context.instance]? | throw .abandoned
  let owner ← liftM (declaration entry.key.declaration : CompileM Declaration)
  let supplied := steps.flatMap fun (_, args) => (args.getD #[]).filterMap fun
    | .spec at_ name term => some (at_, name, term)
    | _ => none
  let env ← staticEnv
  let proofArguments ← liftM (specificationClosure env found supplied owner.scopes span : CompileM _)
  -- the instance of the relation at the types of the operands (SP6), whose `where` holds at
  -- the deployed values (SP4) and, when every proof argument has a value, at those too
  let assigned ← liftM (assignArguments env steps scopes span : CompileM _)
  let (parameters, result) ← signatureOf id
  let name ← liftM (Static.nameOf id : CompileM String)
  let paired ← pairRelationArguments name (node.statement.map (·.name.text))
    ((node.witness.getD #[]).map (·.name.text)) arguments witnesses span
  let (values, _) ← inferArguments id assigned found.file parameters result paired (some .bool) span
  let description ← liftM (describeInstance id values : CompileM String)
  let inst ← liftM (instantiate id values { description, span } : CompileM InstanceId)
  if let some closure := proofArguments then
    liftM (closure.checkApplication inst span)

/-- The conditions of the relations that the deciding clauses apply, at the ports of an
instance. Every refused clause is reported, and one refused clause refuses them all. -/
def elabClauses (signature : Typed.ProtocolSignature) (head : Lowered.ProtocolHead)
    (clauses : Array Lowered.Clause) : ElabM Unit := do
  for (port, closed) in head.ports.zip signature.ports do
    discard <| bindLocal port.binder closed.type
    if port.specification then
      modify fun state => { state with
        specificationPorts := state.specificationPorts.insert port.binder.id }
  let mut refused := false
  for expr in decidingApplications clauses do
    try elabClauseApplication expr
    catch
      | .abandoned => refused := true
      | .waiting _ | .staticIndex _ => pure ()
      | other => throw other
  if refused then throw .abandoned

end Zkc.Frontend.Elab
