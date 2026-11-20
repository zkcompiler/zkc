module

public import Zkc.Frontend.Elab.Events

@[expose] public section

set_option autoImplicit false

/-!
# The relation applications of a contract's deciding clauses

A `proves` clause and the source of a `reduces` clause apply a relation to ports of the
protocol. Such an application is an application like any other: its arguments are paired with
the statement and the witness of the relation, the static arguments of the relation are
inferred from the types of the operands, the relation is instantiated, the `where` of its head
holds at that instance (SP4), the operands have the types of its parameters, and its body is
typed. When every proof argument of the relation has a value, the `where` holds at those values
too. It is typed here, at the ports of an instance of the protocol, in a specification: the
names of every role stand.

A clause is specification and runs nowhere, so an operand or a body of a relation that waits
for a later layer of the language leaves the clause as it is and does not make the protocol
wait. A condition that cannot be evaluated is not taken to hold: the clause waits for it, and
the protocol with it. An application that is refused refuses the protocol.

Not typed here: the relation of a `knowledge` clause, which is applied to its statement only;
what a clause states under the results or under the index of a loop; a formula that applies no
relation; and `requires`.
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

/-- One application of a relation in a clause. An expression that applies no relation
declaration is left as it is. -/
def elabClauseApplication (expr : Lowered.Expr) : ElabM Unit := do
  let .call span callee arguments witnesses := expr | return
  let .declaration steps scopes ← calleeOf callee | return
  let some (id, _) := steps.back? | return
  let found ← liftM (declaration id : CompileM Declaration)
  let .relation node := found.node | return
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
  -- the static arguments of the relation, from the types of the operands (SP6); an operand of
  -- a later layer leaves the clause as it is
  let assigned ← liftM (assignArguments env steps scopes span : CompileM _)
  let (parameters, result) ← signatureOf id
  let name ← liftM (Static.nameOf id : CompileM String)
  let paired ← pairRelationArguments name (node.statement.map (·.name.text))
    ((node.witness.getD #[]).map (·.name.text)) arguments witnesses span
  let inferred ← try
      pure (some (← inferArguments id assigned found.file parameters result paired (some .bool) span))
    catch
      | .waiting _ | .staticIndex _ => pure none
      | other => throw other
  let some (values, _) := inferred | return
  -- the instance of the relation, whose `where` holds at the deployed values (SP4) and, when
  -- every proof argument has a value, at those too; a condition that cannot be evaluated is
  -- not taken to hold
  let description ← liftM (describeInstance id values : CompileM String)
  let inst ← liftM (instantiate id values { description, span } : CompileM InstanceId)
  unless ((← getThe Compile.State).table.content? inst) matches some (.signature _ (some _)) do
    waitFor (← liftM (signatureWait inst : CompileM String))
  if let some closure := proofArguments then
    liftM (closure.checkApplication inst span)
  -- the operands at the parameter types of the instance, and the body of the relation, which
  -- may wait for a later layer
  try discard <| callDeclaration id assigned paired (some .bool) span
  catch
    | .waiting _ | .staticIndex _ => pure ()
    | other => throw other

/-- The relation applications of the deciding clauses, at the ports of an instance. Every
refused clause is reported, and one refused clause refuses them all. -/
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
      | other => throw other
  if refused then throw .abandoned

end Zkc.Frontend.Elab
