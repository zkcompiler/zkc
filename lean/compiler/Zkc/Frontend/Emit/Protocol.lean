module

public import Zkc.Frontend.Elab.Protocol
public import Zkc.Frontend.Elab.Clauses
public import Zkc.Frontend.Elab.Linear
public import Zkc.Frontend.Passes.Placement
public import Zkc.Frontend.Passes.Events
public import Zkc.Frontend.Emit.Function

@[expose] public section

set_option autoImplicit false

/-!
# The body of a protocol instance by the typed tree

The body of a protocol instance is elaborated once to the typed tree, with every refusal
reported. The passes read the numbered tree: the roles of every statement, the uses of linear
values, the occurrences of the events. A body that passes is checked by the core for its
facts, each role with its own (`Emit.checkProtocol`), and a refusal is worded at its node:
when the same code is computed by another role that has the fact, the refusal says so (TY4).

What the session keeps of the instance is read from the tree and from the lowering of the
check: its ports and results with their holders, its sites in the order of their numbers, its
flows, its specification arguments, and what it waits for.
-/

namespace Zkc.Frontend.Emit

open Syntax
open Static
open Typing (ProtocolCode BodyState SiteEntry FlowEntry SpecificationArgument)

/-- The passes over the numbered tree of a protocol body: the roles, the uses of linear values,
and the occurrences of its events. Their refusals are logged. -/
def checkedProtocol (definition : Typed.Definition) (body : Typed.ProtocolBody) :
    CompileM Typed.Checked := do
  let results := (← get).results
  let calleeStops (inst : InstanceId) : Bool :=
    match results.body? inst with
    | some (.done code) => code.canStop
    | _ => false
  let mut signatures : Std.HashMap InstanceId Typed.ProtocolSignature := {}
  for callee in appliedIn #[] body.statements do
    let signature ← recoverWith (some <$> Elab.protocolSignatureOf callee) (fun _ => pure none)
      (waits := true)
    if let some signature := signature then signatures := signatures.insert callee signature
  let roles ← Passes.placeRoles
    { roster := body.roster, calleeStops, signatureOf := (signatures[·]?) } body
  -- the uses of linear values, in deployed code (LN1, LN2)
  unless definition.specificationOnly || definition.body.hasError do
    if let .error (span, message) := Linear.checkProtocol body then
      logError "LN2" span (.ofText message)
  return { definition, roles, events := Passes.occurrences body }

/-- The statement of a body that computes a node: the binding, level of a pattern, update or
guard around it, with the roles that compute it. -/
partial def computingStatement? (roles : Typed.Roles) (node : Typed.NodeId)
    (statements : Array Typed.Stmt) : Option (Typed.Stmt × RoleSet) :=
  statements.findSome? fun statement =>
    match statement with
    | .bind mark .. | .unpack mark .. | .update mark .. | .guard mark .. =>
      if (statement.find? node).isSome then (roles.computing[mark.id]?).map fun set => (statement, set)
      else none
    | .if _ _ onTrue onFalse _ =>
      (computingStatement? roles node onTrue).orElse fun _ => computingStatement? roles node onFalse
    | .match _ _ _ _ cases _ =>
      cases.findSome? fun (.case _ _ _ body) => computingStatement? roles node body
    | .for _ (.loop _ _ _ body) _ =>
      match body with
      | .uniform inner _ => computingStatement? roles node inner
      | .stepped iterations =>
        iterations.findSome? fun (Typed.Iteration.iteration _ inner _) => computingStatement? roles node inner
      | .empty .. => none
    | .scope _ body => computingStatement? roles node body
    | _ => none

/-- Logs the refusals of facts of a protocol body, each worded at its node. A refusal at a role
of code that another role computes with the fact says which role has it (TY4). A loop whose
count a participant does not know to be bounded is CT4. -/
def reportProtocolFindings (body : Typed.ProtocolBody) (roles : Typed.Roles)
    (found : List Finding) : CompileM Unit := do
  let roleName (role : Nat) : String := (body.roster[role]?).getD s!"role{role}"
  let mut reported : Array (Option Typed.NodeId) := #[]
  for finding in found do
    -- one refusal per node: the copies of a statement at several roles are one statement
    if reported.contains finding.node then continue
    reported := reported.push finding.node
    let node := finding.node.bind body.find?
    match finding.explained.requirement, node, finding.role with
    | .maximum, some (.stmt (.for mark (.loop _ domain _ _) _)), some role =>
      let bound ← match domain with
        | .range _ stop _ => textAt stop.span
        | .collection source _ _ => textAt source.span
      logError "CT4" mark.span (.ofText
        s!"the count of this loop has no static bound at {roleName role}: `{bound}` is a `nat`; write `guard @{roleName role} {bound} <= N` first, or take it from an `index<N>`")
        (origin := .instances)
    | _, _, _ =>
      let worded ← word node finding.explained
      -- a role that computes the same statement and has the fact
      let other : Option (Typed.Stmt × Nat) := do
        let failing ← finding.role
        let id ← finding.node
        let (statement, computing) ← computingStatement? roles id body.statements
        let passing ← computing.toArray.find? fun role =>
          role != failing && !found.any fun entry =>
            entry.role == some role && (entry.node.bind fun inner => statement.find? inner).isSome
        return (statement, passing)
      let aboutFacts := ["TY5", "TY7", "TY8"].contains worded.rule
      match other, finding.role with
      | some (.bind mark _ value _, holder), some role =>
        if aboutFacts then
          logError "TY4" mark.span (.ofText
            s!"`{roleName role}` computes `{← textAt value.span}` without a fact that `{roleName holder}` holds: {worded.message}; or restrict the binder to `@{roleName holder}`")
            (origin := .instances)
        else logError worded.rule worded.span (.ofText worded.message) (origin := .instances)
      -- a statement that binds nothing: the same refusal, saying which role lacks the fact
      | some (_, holder), some role =>
        if aboutFacts then
          logError "TY4" worded.span (.ofText
            s!"`{roleName role}` computes this without a fact that `{roleName holder}` holds: {worded.message}")
            (origin := .instances)
        else logError worded.rule worded.span (.ofText worded.message) (origin := .instances)
      | _, _ => logError worded.rule worded.span (.ofText worded.message) (origin := .instances)

/-- What the session keeps of a checked protocol body. `keys` are the keys of its sites in the
order of their numbers, as the lowering of its check numbered them. -/
def protocolSummary (description : String) (head : Lowered.ProtocolHead) (checked : Typed.Checked)
    (body : Typed.ProtocolBody) (origin : DefinitionOrigin)
    (resolved : Array (Typing.ResolvedPlace × ParameterRef)) (waiting : Option String) :
    CompileM ProtocolCode := do
  -- one input per holder of each deployed port, numbered by its place among the deployed ports
  -- (`Typed.ProtocolBody.deployedPorts`); one output per holder of each result
  let mut inputs : Array (ClosedType × Nat) := #[]
  let mut inputPorts : Array Nat := #[]
  let mut agreements : Array (Bool × Array Nat) := #[]
  for (port, number) in body.deployedPorts.zipIdx do
    let holders := port.holders.toArray
    if holders.size > 1 then
      agreements := agreements.push (false, (Array.range holders.size).map (inputs.size + ·))
    for holder in holders do
      inputs := inputs.push (port.binder.type, holder)
      inputPorts := inputPorts.push number
  let mut outputs : Array (ClosedType × Nat) := #[]
  for result in body.results do
    let holders := result.holders.toArray
    if holders.size > 1 then
      agreements := agreements.push (true, (Array.range holders.size).map (outputs.size + ·))
    for holder in holders do outputs := outputs.push (result.value.type, holder)
  let mut sites := #[]
  let mut flows := #[]
  let mut nestedDraw := none
  let mut specificationArguments : Array SpecificationArgument := #[]
  -- A source operation such as broadcast can have several parts at the same instruction.
  -- Preserve ambiguous node origins so the uniqueness check below still rejects them.
  let mut byNode : Std.HashMap Typed.NodeId (Option Nat) := {}
  for (node, instruction) in origin.nodes.zipIdx do
    byNode := byNode.insert node (if byNode.contains node then none else some instruction)
  for occurrence in checked.events do
    let .event node id what iteration nested true := occurrence | continue
    let some (some instruction) := byNode[node]?
      | throw (.defect "expected one emitted instruction for the source event")
    let event := head.events[id]?
    let site (part : String) : SiteEntry :=
      { event := id, part, name := event.bind (·.name)
        place := (event.map (·.span)).getD default, iteration := iteration, instruction }
    let n := sites.size
    match what with
    | .send _ payload _ receivers =>
      let some sender := checked.roles.senders[node]? | throw (.defect "unplaced send")
      for receiver in receivers do
        let part := if receivers.size ≤ 1 then "value" else s!"to {body.roster[receiver]!}"
        flows := flows.push (.exchange sender receiver payload.type sites.size)
        sites := sites.push (site part)
    | .draw _ law owner receivers =>
      if nested && nestedDraw.isNone then nestedDraw := some (site "value").place
      let row ← internRow (← vocabularyRow law.request) (site "value").place
      sites := sites.push (site "value")
      flows := flows.push (.draw owner receivers row n)
    | .apply _ callee _ _ roleMap .. =>
      if nestedDraw.isNone then
        if let some (.protocol inner) := (← getResults).body? callee then
          if inner.nestedDraw.isSome || inner.flows.any (fun | .draw .. => true | _ => false) then
            nestedDraw := some (site "value").place
      sites := sites.push (site "value")
      flows := flows.push (.apply callee roleMap)
      if let some attached := origin.specification.find? (·.instruction.number == instruction) then
        for (port, expr) in attached.arguments do
          specificationArguments := specificationArguments.push
            {site := n, port, text := ← textAt expr.span, type := ← renderTypeM expr.type, place := expr.span}
    | .sample .. | .attempt .. => sites := sites.push (site "value")
  return { name := description, roles := body.roster, inputs, inputPorts, outputs, agreements
           sites, flows, nestedDraw, specificationArguments, resolved
           waiting, specificationOnly := head.specification }

/-- The body of a protocol that a body applies, asked for from the place of the application: a
callee that is refused abandons the statement that applies it, without a diagnostic of its
own, and a callee that waits makes its caller wait. -/
def calleeBody (typeBody : InstanceId → Span → CompileM Unit) (inst : InstanceId) (place : Span) :
    CompileM Unit := do
  typeBody inst place
  match (← getResults).body? inst with
  | some (.protocol code) => if let some reason := code.waiting then throw (.waiting reason)
  | some (.waiting reason) => throw (.waiting reason)
  | some (.exhausted exhaustion) => throw (.exhausted exhaustion)
  | some .failed => throw .abandoned
  | _ => pure ()

/-- The typed tree of a protocol body at an environment, numbered, with what the passes make of
it. Every refusal of the body is logged. -/
def elaborateProtocol (inst : InstanceId) (description name : String) (env : Env)
    (head : Lowered.ProtocolHead) (statements : Array Lowered.Stmt)
    (returned : Option Lowered.Expr) (locals : Nat) (typeBody : InstanceId → Span → CompileM Unit)
    (resolutions : Std.HashMap Typing.ResolvedPlace ParameterRef) («opaque» : Bool := false) :
    CompileM (Typed.Checked × Typed.ProtocolBody × Array Typing.PlaceTyping) := do
  let context : Elab.Context :=
    { env, «instance» := inst, name := description, typeBody
      specification := head.specification, resolutions, «opaque», roster := some head.roster
      protocolBody := calleeBody typeBody }
  -- the head at the values of the environment: those of the instance, or the opaque ones
  let signature ← Elab.protocolSignatureIn head env
  let (body, elaborated) ← Elab.runElab context locals
    (Elab.elabProtocolBody name signature head statements returned)
  let (numbered, nodes) := (Typed.Body.protocol body).numbered
  let definition : Typed.Definition :=
    { «instance» := inst, body := numbered, locals := elaborated.nextLocal, nodes
      specificationOnly := head.specification }
  let .protocol body := numbered | throw (.defect "a protocol body that is no protocol body")
  return (← checkedProtocol definition body, body, elaborated.resolved)

/-- The elaboration of what the deciding clauses of the contract of a protocol instance apply
(`Elab.elabClauses`), at static values of the protocol and at values of its specification-only
parameters: each typed application with the place of its clause in the contract, and the
typings of the places that the opaque elaboration resolved. `only` is the place of the one
clause to type, when a consumer reads one. The instances of relations that it asks for enter
the state in which it runs. A clause that waits for a later layer is left out when `lenient`,
and makes the typing wait otherwise. -/
def elaborateClauses (inst : InstanceId) (arguments : Array StaticValue) (specification : Array Nat)
    (typeBody : InstanceId → Span → CompileM Unit)
    (resolutions : Std.HashMap Typing.ResolvedPlace ParameterRef) (lenient : Bool)
    («opaque» : Bool := false) (only : Option Nat := none) :
    CompileM (Array (Nat × Typed.Expr) × Array Typing.PlaceTyping) := do
  let state ← get
  let some instanceKey := state.table.allocatedKey? inst | throw .abandoned
  let modules ← getModules
  let some contract := modules.indexes.contracts[instanceKey.declaration]? | return (#[], #[])
  let some clauses := modules.lowered? contract | return (#[], #[])
  let .contract node := clauses.content | return (#[], #[])
  if clauses.refused || (Elab.decidingApplications node.clauses).isEmpty then return (#[], #[])
  let some lowered := modules.lowered? instanceKey.declaration | return (#[], #[])
  let .protocol head _ _ := lowered.content | return (#[], #[])
  let found ← declaration instanceKey.declaration
  let description ← describeInstance instanceKey.declaration instanceKey.arguments specification
    instanceKey.owner
  let env := instanceEnv state.program found arguments specification
  let context : Elab.Context :=
    { env, «instance» := inst, name := description, typeBody, specification := true
      resolutions, «opaque», roster := some head.roster, protocolBody := calleeBody typeBody }
  let signature ← Elab.protocolSignatureIn head env
  let (typed, elaborated) ← Elab.runElab context clauses.locals
    (Elab.elabClauses signature head node.clauses lenient only)
  return (typed, elaborated.resolved)

/-- The places of an instance's code that its opaque typing resolved to members of an interface
(SP12), as the instance keeps them: those of its body and of its contract. -/
def keptResolutions (inst : InstanceId) : CompileM (Std.HashMap Typing.ResolvedPlace ParameterRef) := do
  match (← getResults).body? inst with
  | some (.protocol code) =>
    return code.resolved.foldl (init := {}) fun map (place, reference) => map.insert place reference
  | _ => return {}

/-- What the deciding clauses of the contract of a protocol instance apply, typed at values of
the instance's specification-only parameters, in the state in which it runs
(`elaborateClauses`). Where no resolutions are given, those that the instance keeps are used:
a goal types the contract of an instance whose body was typed before. -/
def typedClauses (inst : InstanceId) (specification : Array Nat)
    (typeBody : InstanceId → Span → CompileM Unit)
    (resolutions : Std.HashMap Typing.ResolvedPlace ParameterRef := {}) (lenient : Bool := true)
    (only : Option Nat := none) : CompileM (Array (Nat × Typed.Expr)) := do
  let some instanceKey := (← get).table.allocatedKey? inst | throw .abandoned
  let resolutions ← if resolutions.isEmpty then keptResolutions inst else pure resolutions
  let (typed, _) ← elaborateClauses inst instanceKey.arguments specification typeBody resolutions
    lenient (only := only)
  return typed

/-- An elaboration of clauses run aside, on a copy of the state: only its diagnostics are kept.
The instances of relations that it asks for must not enter the program: deployed definitions
are numbered by their instances, and what a specification says does not change the identity
of deployed code. -/
def aside {α : Type} (attempt : CompileM α) (keepReads : Bool := false) : CompileM α := do
  let saved ← get
  let (result, after) := (captureModuleReads attempt).run (← read) saved
  match result with
  | .ok (value, reads) =>
    if keepReads then
      modify fun s => {s with moduleReads := s.moduleReads ++ detachedModuleReads saved after reads}
    return value
  | .error failure =>
    modify fun s => {s with log := after.log}
    throw failure

/-- The check of what the deciding clauses of a contract apply, at values of the instance's
specification-only parameters, run aside. -/
def typeClauses (inst : InstanceId) (specification : Array Nat)
    (typeBody : InstanceId → Span → CompileM Unit)
    (resolutions : Std.HashMap Typing.ResolvedPlace ParameterRef := {}) : CompileM Unit := do
  discard <| aside (typedClauses inst specification typeBody resolutions) (← read).allClauseReads

/-- The opaque typing of what the deciding clauses of the contract of a protocol generic over a
module parameter apply (SP12), run aside: the typings of the places that it resolves. A
contract is typed twice as a body is, so a clause reads of a type member what its interface
declares and no more, and calls the members that a body may call. -/
def opaqueClauseTypings (inst : InstanceId) (opaqueArguments : Array StaticValue)
    (specification : Array Nat) (typeBody : InstanceId → Span → CompileM Unit) :
    CompileM (Array Typing.PlaceTyping) :=
  aside do
    let (_, typings) ← elaborateClauses inst opaqueArguments specification typeBody {} true
      («opaque» := true)
    return typings

/-- The code of a protocol instance: its lowered body elaborated at the instance, checked by the
passes and by the core, and what the session keeps of it. `typeBody` asks for the body of a
callee from the place of a call or of an application. -/
def protocolBody (inst : InstanceId) (typeBody : InstanceId → Span → CompileM Unit) :
    CompileM BodyState := do
  let state ← get
  let some instanceKey := state.table.allocatedKey? inst | throw .abandoned
  let found ← declaration instanceKey.declaration
  let name := state.program.nameOf instanceKey.declaration
  let description ← describeInstance instanceKey.declaration instanceKey.arguments
    instanceKey.specification instanceKey.owner
  let some lowered := (← getModules).lowered? instanceKey.declaration
    | throw (.defect "a declaration without its lowered form")
  let .protocol head statements returned := lowered.content
    | throw (.defect "a protocol instance of a declaration that is no protocol")
  let place := (found.name.map (·.span)).getD default
  let env := instanceEnv state.program found instanceKey.arguments instanceKey.specification
  -- a protocol generic over a module parameter is elaborated twice: the opaque elaboration
  -- first, whose resolutions the elaboration at the instance uses (SP12)
  let resolutions : Std.HashMap Typing.ResolvedPlace ParameterRef ←
    if ← genericOverModule found then do
      let (opaqueArguments, over) ← opaqueValues found instanceKey.arguments
      let frame : ChainFrame :=
        { subject := .ofText s!"the opaque typing of `{name}` over {", ".intercalate over.toList}"
          span := place }
      withChainFrame frame do
        let opaqueEnv := instanceEnv state.program found opaqueArguments instanceKey.specification
        let (_, _, typings) ← elaborateProtocol inst description name opaqueEnv head
          statements returned[0]? lowered.locals typeBody {} («opaque» := true)
        -- the contract in the opaque typing too: its places are resolved as the body's are
        let clauseTypings ← opaqueClauseTypings inst opaqueArguments instanceKey.specification typeBody
        placeResolutions name found instanceKey.arguments (typings ++ clauseTypings)
    else pure {}
  let errors := (← get).log.errors
  if let .protocol node := found.node then Passes.checkSiteNames node
  let (checked, body, _) ← elaborateProtocol inst description name env head statements
    returned[0]? lowered.locals typeBody resolutions
  -- the tree and its tables are kept, also of a body that is refused: the tools read them
  let requested : ChainFrame := { subject := .ofPart (.instance inst), span := place }
  modifyResults fun results => { results with
    checked := (results.checked.intern inst requested none).1.setStateOf inst (.done checked)
    trees := (results.trees.intern inst requested none).1.setStateOf inst (.done checked.definition) }
  if (← get).log.errors > errors || checked.definition.body.hasError then throw .abandoned
  -- what the contract applies, at the values of the instance
  typeClauses inst instanceKey.specification typeBody resolutions
  -- the facts of the body, by the core, each role with its own
  let outcome ← match checkProtocol (← get) inst with
    | .ok outcome => pure outcome
    | .error (.defect message) => throw (.defect message)
    | .error (.exhausted exhaustion) => throw (.exhausted exhaustion)
    -- a form of a later layer in the body: the instance waits for it
    | .error (.waiting reason) | .error (.noCoreForm reason) => throw (.waiting reason)
  unless outcome.findings.isEmpty do
    reportProtocolFindings body checked.roles outcome.findings
    throw .abandoned
  -- a function that the body calls and that waits keeps the packages of the protocol waiting
  let called := body.results.foldl (fun found result => calledInExpr found result.value)
    (body.statements.foldl calledInStmt #[])
  let results ← getResults
  let waiting := called.findSome? fun callee =>
    match results.body? callee with
    | some (.done code) => code.waiting
    | _ => none
  return .protocol (← protocolSummary description head checked body outcome.origin resolutions.toArray waiting)

end Zkc.Frontend.Emit
