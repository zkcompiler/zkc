module

public import Zkc.Frontend.Semantics.Instantiate.Roots
public import Zkc.Frontend.Emit.Function
public import Zkc.Frontend.Emit.Protocol

@[expose] public section

set_option autoImplicit false

/-!
# The bodies of instances

The body of every function and protocol instance is typed once, on demand: a call types its
callee's body before it uses the result, inside the frame of the callee's instance. A body reached
again while it is being typed is a definition that reaches itself through bodies (NL1), with the
chain of instances through which it was reached.

A function instance is elaborated to the typed tree and checked (`Emit.functionBody`), and so
is a protocol instance, with the passes that place its roles (`Emit.protocolBody`); the tree is
kept with the instance.
-/

namespace Zkc.Frontend.Typing

open Syntax
open Instances
open Static

/-- Records what the typing of a body has come to, in its entry of the table of bodies. -/
def setBody (inst : InstanceId) (body : BodyState) : CompileM Unit :=
  let state : QueryState BodyState := match body with
    | .inProgress => .inProgress
    | .failed => .failed
    | .waiting reason => .waiting reason
    | .exhausted exhaustion => .exhausted exhaustion
    | other => .done other
  modifyResults (·.modifyBodies (·.setStateOf inst state))

mutual
  /-- Types the body of a function instance once (NL1 through bodies). -/
  partial def typeBody (inst : InstanceId) (place : Span) : CompileM Unit := do
    let state ← get
    match state.results.body? inst with
    | some .inProgress =>
      let some instanceKey := state.table.allocatedKey? inst | throw .abandoned
      let description ← describeInstance instanceKey.declaration instanceKey.arguments
        instanceKey.specification instanceKey.owner
      refuseRecursion description place
    | some _ => useQueryReads ⟨.body, inst⟩; return
    | none => pure ()
    let some entry := state.table.entryAt? inst | return
    let .done _ := entry.state | return
    let description ← describeInstance entry.key.declaration entry.key.arguments
      entry.key.specification entry.key.owner
    -- the request for the body: entered in progress, recorded with the request that asks for it,
    -- and on the stack while the body is typed
    let requester ← currentRequest?
    let reference : QueryRef := ⟨.body, inst⟩
    let requested : ChainFrame := { subject := .ofText description, span := place }
    modifyResults fun results =>
      let results := results.modifyBodies fun bodies =>
        (bodies.intern inst requested requester).1
      match requester with
      | some requester => results.addRequest requester reference
      | none => results
    -- a request deeper than the budget of the chain is not computed: it is exhausted (SP10)
    if ← beyondDepth then
      setBody inst (.exhausted (← logExhaustion .instantiationDepth requested))
      return
    try
      let outcome ← withRequest reference (typeInstance inst)
      setBody inst outcome
      if let .done _ := outcome then
        modifyResults (·.addFinished inst)
    catch failure =>
      match failure with
      | .waiting reason => setBody inst (.waiting reason)
      | .staticIndex name => setBody inst (.waiting s!"the index `{name}` in a static position")
      | .exhausted exhaustion => setBody inst (.exhausted exhaustion)
      | _ =>
        setBody inst .failed
        throw failure

  /-- The body of an instance: of a function, or of a protocol. -/
  partial def typeInstance (inst : InstanceId) : CompileM BodyState := do
    let state ← get
    let instanceKey := state.table.allocatedKey! inst
    let found ← declaration instanceKey.declaration
    match found.node with
    | .«def» _ | .memberDef _ | .relation _ | .law _ | .member (.lawMember _) =>
      Emit.functionBody inst typeBody
    | .protocol _ => Emit.protocolBody inst typeBody
    | _ => return .waiting s!"a call of {Names.kindWord found.kind}"
end

/-- Supply static evaluation with the ordinary body query, including while checking
signatures requested by that query, and with the typing of what a contract applies where a
specification is closed. Re-entering a body goes through the usual cycle check. -/
partial def withProtocolBodies (context : Compile.Context) : Compile.Context :=
  {context with
    protocolBody := fun inst place => typeBody inst place (withProtocolBodies context)
    contractClauses := fun inst values _ =>
      (Emit.typeClauses inst values typeBody) (withProtocolBodies context)}

/-- The typed applications of the deciding clauses of a protocol instance at values of its
specification-only parameters, each with the place of its clause in the contract
(`Emit.typedClauses`); of the clause at the place `only` alone, when it is given, so that a
clause that the consumer does not read cannot make the request wait. The instances that it makes
enter the state, so a consumer that states a claim runs it on a state of its own. A clause that
waits makes the request wait. -/
def typedClauses (inst : InstanceId) (values : Array Nat) (only : Option Nat := none) :
    CompileM (Array (Nat × Typed.Expr)) :=
  fun context =>
    (Emit.typedClauses inst values typeBody (lenient := false) (only := only))
      (withProtocolBodies context)

/-- The checks of FN5 that need no body: a kernel stands on a deployed `def` with a body. -/
def checkKernels : CompileM Unit := do
  let program ← program
  for index in [0:program.declarations.size] do
    let found := program.declarations[index]!
    unless inPackage program found.file do continue
    let name := program.nameOf index
    match found.node with
    | .«def» node =>
      let some kernel := node.kernel | continue
      if node.modifier matches some (.spec _) then
        logError "FN5" kernel.span
          (.ofText s!"`{name}` is a specification function: it runs nowhere, and a kernel is an implementation of deployed code") (origin := .instances)
      else if !(node.binding matches .body _) then
        logError "FN5" kernel.span (.ofText "a kernel is attached to a `def` with a body") (origin := .instances)
    | .memberDef node =>
      let some kernel := node.kernel | continue
      if node.spec then
        logError "FN5" kernel.span
          (.ofText s!"`{name}` is a specification function: it runs nowhere, and a kernel is an implementation of deployed code") (origin := .instances)
      else if !(node.binding matches .body _) then
        logError "FN5" kernel.span (.ofText "a kernel is attached to a `def` with a body") (origin := .instances)
    | _ => pure ()

def typeRequestedBody (cursor : Nat) : CompileM Unit := do
  let state ← get
  let index := state.table.requestedIds[cursor]!
  let entry := state.table.entryAt! index
  if let (none, some found) := (entry.key.view, state.program.declarations[entry.key.declaration]?) then
    if found.kind == .function || found.kind == .functionDefinition || found.kind == .relation
        || found.kind == .law || found.kind == .lawMember || found.kind == .protocol then
      let place := (found.name.map (·.span)).getD default
      endItem (typeBody index place)
    -- the laws of a module instance are typed at it (SP10); a module that a parameter stands
    -- for in an opaque typing (SP12) is no instance of the program, and has no laws of its own
    -- and its function members, called or not (SP7 item 7)
    if found.kind == .«module» && entry.key.opaqueFor.isNone then
      endItem (moduleLaws index)
      endItem (typeModuleMembers index)

/-- Both tables extend the same key prefix. Bring the private requests up to the latest
allocation before evaluating them, then return only the extended prefix to the live table.
Requests appended during this batch belong at the current tail of the combined queue. -/
def layoutBodies (batch : Compile.DefaultBodyBatch) :
    CompileM (Option Compile.DefaultBodyBatch) := do
  let live ← get
  let tail := batch.results.instanceCount
  let results := batch.results.modifySignatures (·.reserveNewKeys live.table)
  let work : CompileM Unit := do
    for cursor in [batch.firstPrivate:tail] do typeRequestedBody cursor
  let (_, trial) := work.run (← read) {env := {modules := live.modules, results}}
  modifyResults (·.modifySignatures (·.reserveNewKeys trial.table))
  if tail < trial.results.instanceCount then
    return some ⟨live.results.instanceCount, tail, trial.results⟩
  return none

/-- Types the body of every instance of the table that is not typed yet, the instances that
typing adds included. -/
def typeBodies : CompileM Unit := do
  let mut cursor := 0
  if !(← get).defaultBodyBatches.isEmpty then
    let mut batches ← modifyGet fun s => (s.defaultBodyBatches, {s with defaultBodyBatches := ∅})
    while let some (batch, rest) := batches.dequeue? do
      for i in [cursor:batch.afterRequests] do typeRequestedBody i
      cursor := batch.afterRequests
      -- A private tail cannot affect a package once all ordinary requests have run.
      if cursor == (← getResults).instanceCount then return
      batches := rest
      if let some more ← layoutBodies batch then batches := batches.enqueue more
  while cursor < (← getResults).instanceCount do
    typeRequestedBody cursor
    cursor := cursor + 1

/-- The phase of types: the checks of kernels, and the body of every instance that the roots
reach. -/
def typeProgram : CompileM Unit := do
  checkKernels
  typeBodies

end Zkc.Frontend.Typing
