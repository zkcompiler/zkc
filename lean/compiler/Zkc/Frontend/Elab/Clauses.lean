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
too, and the body of the relation is typed at them. It is typed here, at the ports of an
instance of the protocol, in a specification: the names of every role stand.

A clause is specification and runs nowhere, so an operand or a body of a relation that waits
for a later layer of the language leaves the clause as it is and does not make the protocol
wait. An operand that waits is met before the instance of the relation: the `where` of the
relation is then not checked. A condition that cannot be evaluated is not taken to hold: the
clause waits for it, and the protocol with it. An application that is refused refuses the
protocol.

Not typed here: the relation of a `knowledge` clause, which is applied to its statement only;
what a clause states under the results or under the index of a loop; a formula that applies no
relation; and `requires`.
-/

namespace Zkc.Frontend.Elab

open Syntax
open Static

/-- What a deciding clause of a contract states at the ports alone. -/
def decidingApplication? : Lowered.Clause → Option Lowered.Expr
  | .proves _ _ _ relation => some relation
  | .reduces _ _ _ source _ => some source
  | _ => none

/-- What the deciding clauses of a contract state at the ports alone. -/
def decidingApplications (clauses : Array Lowered.Clause) : Array Lowered.Expr :=
  clauses.filterMap decidingApplication?

/-- A step of the typing of a clause that may wait for a later layer of the language. A reader
of contracts leaves such a clause as it is (`none`); a consumer that needs the typed clause
is told why it waits. -/
def unlessWaiting {α : Type} (lenient : Bool) (step : ElabM α) : ElabM (Option α) := do
  try pure (some (← step))
  catch
    | failure@(.waiting _) | failure@(.staticIndex _) => if lenient then pure none else throw failure
    | other => throw other

/-- One application of a relation in a clause, typed: the call of the instance of the relation
on the operands, which are the statement operands alone where the clause is written short.
None for an expression that applies no relation declaration, and for a clause that waits when
`lenient`. -/
def elabClauseApplication (expr : Lowered.Expr) (lenient : Bool := true) :
    ElabM (Option Typed.Expr) := do
  let .call span callee arguments witnesses := expr | return none
  let .declaration steps scopes ← calleeOf callee | return none
  let some (id, _) := steps.back? | return none
  let found ← liftM (declaration id : CompileM Declaration)
  let .relation node := found.node | return none
  -- every specification-only parameter of the relation is given by a specification argument,
  -- or is the protocol's own where they share a scope (SP11)
  let proofArguments ← callProofArguments steps found span
  let env ← staticEnv
  -- the static arguments of the relation, from the types of the operands (SP6); an operand of
  -- a later layer leaves the clause as it is
  let assigned ← liftM (assignArguments env steps scopes span : CompileM _)
  let (parameters, result) ← signatureOf id
  let name ← liftM (Static.nameOf id : CompileM String)
  -- the short application says that some witness exists (SX3): its statement is paired and
  -- typed, and the typed application then has the statement operands alone
  let paired ← pairRelationArguments name (node.statement.map (·.name.text))
    ((node.witness.getD #[]).map (·.name.text)) arguments witnesses span (atTop := true)
  let some (values, _) ← unlessWaiting lenient
      (inferArguments id assigned found.file parameters result paired (some .bool) span)
    | return none
  -- the instance of the relation, whose `where` holds at the deployed values (SP4); a condition
  -- that cannot be evaluated is not taken to hold
  let description ← liftM (describeInstance id values : CompileM String)
  let inst ← liftM (instantiate id values { description, span } : CompileM InstanceId)
  unless ((← getThe Compile.State).table.content? inst) matches some (.signature _ (some _) _) do
    waitFor (← liftM (signatureWait inst : CompileM WaitReason))
  -- the operands at the parameter types of the instance, and the body of the relation. When
  -- every proof argument has a value, the call reaches the relation at those values: its
  -- `where` holds there, and its body is typed there, where an index, a size or a condition
  -- can depend on a proof argument. A body that waits for a later layer leaves the clause as
  -- it is
  unlessWaiting lenient (callDeclaration id assigned paired (some .bool) span proofArguments)

/-- The relation applications of the deciding clauses, at the ports of an instance: each typed
application with the place of its clause in the contract; of the clause at the place `only`
alone, when it is given. Every refused clause is reported, and one refused clause refuses them
all. -/
def elabClauses (signature : Typed.ProtocolSignature) (head : Lowered.ProtocolHead)
    (clauses : Array Lowered.Clause) (lenient : Bool := true) (only : Option Nat := none) :
    ElabM (Array (Nat × Typed.Expr)) := do
  for (port, closed) in head.ports.zip signature.ports do
    discard <| bindLocal port.binder closed.type
    if port.specification then
      modify fun state => { state with
        specificationPorts := state.specificationPorts.insert port.binder.id }
  let mut refused := false
  let mut typed := #[]
  for (clause, place) in clauses.zipIdx do
    if only.any (· != place) then continue
    let some expr := decidingApplication? clause | continue
    try
      if let some application ← elabClauseApplication expr lenient then
        typed := typed.push (place, application)
    catch
      | .abandoned => refused := true
      | other => throw other
  if refused then throw .abandoned
  return typed

end Zkc.Frontend.Elab
