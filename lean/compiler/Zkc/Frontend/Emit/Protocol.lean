module

public import Zkc.Frontend.Elab.Protocol
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

/-- The protocol instances that statements apply. -/
partial def appliedIn (found : Array InstanceId) (statements : Array Typed.Stmt) : Array InstanceId :=
  statements.foldl (init := found) fun found statement =>
    match statement with
    | .event _ _ (.apply _ callee ..) => if found.contains callee then found else found.push callee
    | .if _ _ onTrue onFalse _ => appliedIn (appliedIn found onTrue) onFalse
    | .match _ _ _ _ cases _ => cases.foldl (init := found) fun found (.case _ _ _ body) => appliedIn found body
    | .for _ (.loop _ _ _ body) _ =>
      match body with
      | .uniform statements _ | .empty statements _ => appliedIn found statements
      | .stepped iterations =>
        iterations.foldl (init := found) fun found (Typed.Iteration.iteration _ statements _) =>
          appliedIn found statements
    | .scope _ body => appliedIn found body
    | _ => found

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
  return { definition, roles, occurrences := Passes.occurrences body }

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

mutual
  /-- The flows of statements, each with the key of its site: an exchange per receiver of a
  send, a draw, an application. -/
  partial def flowsOf (context : Named.ProtocolContext) (statements : Array Typed.Stmt) :
      CompileM (Array (Zkc.Core.SiteKey × FlowEntry)) := do
    let mut flows := #[]
    for statement in statements do flows := flows ++ (← flowsOfStmt context statement)
    return flows

  partial def flowsOfStmt (context : Named.ProtocolContext) :
      Typed.Stmt → CompileM (Array (Zkc.Core.SiteKey × FlowEntry))
    | .event mark event what => do
      let key (part : String) : Zkc.Core.SiteKey := (context.site mark.id event part).key
      match what with
      | .send _ payload _ receivers =>
        let some sender := context.roles.senders[mark.id]? | return #[]
        return receivers.map fun receiver =>
          let part := if receivers.size ≤ 1 then "value"
            else s!"to {(context.roster[receiver]?).getD "?"}"
          (key part, .exchange sender receiver payload.type 0)
      | .draw _ law owner receivers =>
        let row ← internRow (← vocabularyRow law.request)
        return #[(key "value", .draw owner receivers row 0)]
      | .apply _ callee _ _ roleMap _ => return #[(key "value", .apply callee roleMap)]
      | .sample .. | .attempt .. => return #[]
    | .if _ _ onTrue onFalse _ => do return (← flowsOf context onTrue) ++ (← flowsOf context onFalse)
    | .match _ _ _ _ cases _ => do
      let mut flows := #[]
      for (.case _ _ _ body) in cases do flows := flows ++ (← flowsOf context body)
      return flows
    | .for _ (.loop _ _ _ body) _ => do
      match body with
      | .uniform inner _ => flowsOf context inner
      | .stepped iterations =>
        let mut flows := #[]
        for (Typed.Iteration.iteration _ inner _) in iterations do flows := flows ++ (← flowsOf context inner)
        return flows
      | .empty .. => return #[]
    | .scope _ body => flowsOf context body
    | _ => return #[]
end

/-- The specification arguments of the applications of statements, each with the key of the
site of its application. -/
partial def specificationArgumentsOf (context : Named.ProtocolContext) (statements : Array Typed.Stmt) :
    CompileM (Array (Zkc.Core.SiteKey × SpecificationArgument)) := do
  let mut found := #[]
  for statement in statements do
    match statement with
    | .event mark event (.apply _ _ _ specification _ _) =>
      for (port, value) in specification do
        found := found.push ((context.site mark.id event "value").key,
          { site := 0, port, text := ← textAt value.span, type := ← renderTypeM value.type
            place := value.span })
    | .if _ _ onTrue onFalse _ =>
      found := found ++ (← specificationArgumentsOf context onTrue) ++ (← specificationArgumentsOf context onFalse)
    | .match _ _ _ _ cases _ =>
      for (.case _ _ _ body) in cases do found := found ++ (← specificationArgumentsOf context body)
    | .for _ (.loop _ _ _ body) _ =>
      match body with
      | .uniform inner _ => found := found ++ (← specificationArgumentsOf context inner)
      | .stepped iterations =>
        for (Typed.Iteration.iteration _ inner _) in iterations do
          found := found ++ (← specificationArgumentsOf context inner)
      | .empty .. => pure ()
    | .scope _ body => found := found ++ (← specificationArgumentsOf context body)
    | _ => pure ()
  return found

/-- What the session keeps of a checked protocol body. `keys` are the keys of its sites in the
order of their numbers, as the lowering of its check numbered them. -/
def protocolSummary (description : String) (head : Lowered.ProtocolHead) (checked : Typed.Checked)
    (body : Typed.ProtocolBody) (keys : List Zkc.Core.SiteKey)
    (resolved : Array (Typing.ResolvedPlace × ParameterRef)) (waiting : Option String) :
    CompileM ProtocolCode := do
  -- one input per holder of each port that is not `spec`, one output per holder of each result
  let mut inputs : Array (ClosedType × Nat) := #[]
  let mut inputPorts : Array Nat := #[]
  let mut agreements : Array (Bool × Array Nat) := #[]
  let mut number := 0
  for port in body.ports do
    if port.specification then continue
    let holders := port.holders.toArray
    if holders.size > 1 then
      agreements := agreements.push (false, (Array.range holders.size).map (inputs.size + ·))
    for holder in holders do
      inputs := inputs.push (port.binder.type, holder)
      inputPorts := inputPorts.push number
    number := number + 1
  let mut outputs : Array (ClosedType × Nat) := #[]
  for result in body.results do
    let holders := result.holders.toArray
    if holders.size > 1 then
      agreements := agreements.push (true, (Array.range holders.size).map (outputs.size + ·))
    for holder in holders do outputs := outputs.push (result.value.type, holder)
  -- the sites in the order of their numbers
  let sites : Array SiteEntry := keys.toArray.map fun key =>
    let event := head.events[key.event]?
    { event := key.event, part := key.part, name := event.bind (·.name)
      place := (event.map (·.span)).getD default, iteration := key.iteration.toArray }
  let numberOf (key : Zkc.Core.SiteKey) : Nat := (keys.findIdx? (· == key)).getD keys.length
  -- every flow and every specification argument is at a site of the body
  let known (key : Zkc.Core.SiteKey) : CompileM Unit := do
    unless keys.contains key do
      throw (.defect s!"an event of `{description}` at a site that its body does not have")
  let context : Named.ProtocolContext :=
    { roster := body.roster, roles := checked.roles, occurrences := checked.occurrences
      events := head.events, loops := #[], callee := fun _ => throw (.defect "no package") }
  -- the flows in the order of the sites
  let found ← flowsOf context body.statements
  for (key, _) in found do known key
  let flows := (found.map fun (key, flow) =>
    (numberOf key, match flow with
      | .exchange sender receiver type _ => FlowEntry.exchange sender receiver type (numberOf key)
      | .draw owner receivers law _ => .draw owner receivers law (numberOf key)
      | other => other)).qsort (·.1 < ·.1)
  let specificationArguments := (← specificationArgumentsOf context body.statements).map
    fun (key, argument) => { argument with site := numberOf key }
  return { name := description, roles := body.roster, inputs, inputPorts, outputs, agreements
           sites, flows := flows.map (·.2), specificationArguments, resolved
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
    (resolutions : Std.HashMap Typing.ResolvedPlace ParameterRef) :
    CompileM (Typed.Checked × Typed.ProtocolBody × Array (Typing.ResolvedPlace × ParameterRef)) := do
  let context : Elab.Context :=
    { env, «instance» := inst, name := description, typeBody
      specification := head.specification, resolutions, roster := some head.roster
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

/-- The code of a protocol instance: its lowered body elaborated at the instance, checked by the
passes and by the core, and what the session keeps of it. `typeBody` asks for the body of a
callee from the place of a call or of an application. -/
def protocolBody (inst : InstanceId) (typeBody : InstanceId → Span → CompileM Unit) :
    CompileM BodyState := do
  let state ← get
  let some entry := state.table.entries[inst]? | throw .abandoned
  let found ← declaration entry.key.declaration
  let name := state.program.nameOf entry.key.declaration
  let description ← describeInstance entry.key.declaration entry.key.arguments
    entry.key.specification entry.key.owner
  let some lowered := (← getModules).lowered? entry.key.declaration
    | throw (.defect "a declaration without its lowered form")
  let .protocol head statements returned := lowered.content
    | throw (.defect "a protocol instance of a declaration that is no protocol")
  let place := (found.name.map (·.span)).getD default
  let env := instanceEnv state.program found entry.key.arguments entry.key.specification
  -- a protocol generic over a module parameter is elaborated twice: the opaque elaboration
  -- first, whose resolutions the elaboration at the instance uses (SP12)
  let resolutions : Std.HashMap Typing.ResolvedPlace ParameterRef ←
    if ← genericOverModule found then do
      let (opaqueArguments, over) ← opaqueValues found entry.key.arguments
      let frame : ChainFrame :=
        { subject := .ofText s!"the opaque typing of `{name}` over {", ".intercalate over.toList}"
          span := place }
      withChainFrame frame do
        let opaqueEnv := instanceEnv state.program found opaqueArguments entry.key.specification
        let (_, _, resolved) ← elaborateProtocol inst description name opaqueEnv head
          statements returned[0]? lowered.locals typeBody {}
        pure (resolved.foldl (init := {}) fun map (place, reference) => map.insert place reference)
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
  -- the facts of the body, by the core, each role with its own
  let outcome ← match checkProtocol (← get) inst checked with
    | .ok outcome => pure outcome
    | .error (.defect message) => throw (.defect message)
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
  let keys := outcome.keys
  return .protocol (← protocolSummary description head checked body keys resolutions.toArray waiting)

end Zkc.Frontend.Emit
