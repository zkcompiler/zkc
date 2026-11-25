module

public import Zkc.Frontend.Elab.Terms
public import Zkc.Frontend.Static.Specification

@[expose] public section

set_option autoImplicit false

/-!
# The elaboration of events

The events of a protocol body (EV1 to EV8): `send`, `draw`, `sample`, `attempt` and the
application of a protocol. Each is typed once. What depends on roles beyond what the source
writes is not decided here: who sends a payload that names no sender, whether the roles that an
event names hold what it reads, and who computes an argument, are the placement pass's (HO1,
HO2, EV5).

An application binds one name per result of its callee (RM3). Bound by one name `y`, a callee
with one result gives `y` that result; with several, `y.r` reads the result `r`, and `y` alone
is no value; with none, `y` names the site and is no value. Bound by a tuple pattern, the
results are taken in the order of the callee's head.
-/

namespace Zkc.Frontend.Elab

open Syntax
open Static

/-- The name of a role of the protocol whose body is elaborated. -/
def roleName (role : Nat) : ElabM String := do
  return ((((← getContext).roster).getD #[])[role]?).getD s!"role{role}"

/-- Roles as a message writes them: `P`, or `P, V`. -/
def roleNames (roles : Array Nat) : ElabM String := do
  return ", ".intercalate (← roles.mapM roleName).toList

/-- Whether a type is a law (TY15): `bool`, an `index<n>` with `0 < n`, a field, a
`nonzero<F>`, a type of sort `Group`, a tuple of laws, or `[L; n]` with `L` a law or `n == 0`. -/
partial def isLawType (type : ClosedType) : ElabM Bool := do
  match type with
  | .bool => return true
  | .index bound => return 0 < bound
  | .nonzero field => return ((← family field) matches .field)
  | .tuple components _ => components.allM isLawType
  | .seq element (some size) => if size == 0 then return true else isLawType element
  | .seq _ none | .nat => return false
  | other => return (← family other).isElement

/-- The sampling row of a law: the uniform distribution on its type, one row at the type, a
tuple or a collection of laws included (TY15). -/
def lawOf (type : ClosedType) (place : Span) : ElabM Typed.RowRef := do
  let typeText ← renderTypeE type
  if let .index 0 := type then
    refuseHere "TY15" place
      s!"`{typeText}` is not a law: `index<0>` has no value, so no distribution of total mass one"
  unless ← isLawType type do
    refuseHere "TY15" place
      s!"`{typeText}` is not a law: it has no uniform distribution: a law is `bool`, an `index<n>`, a field, a `nonzero<F>`, a group, or a tuple or sized collection of laws"
  return { name := "law.uniform", statics := #[.type type] }

/-- The closed signature of a protocol head in an environment of static values. -/
def protocolSignatureIn (head : Lowered.ProtocolHead) (env : Env) :
    CompileM Typed.ProtocolSignature := do
  let mut ports : Array Typed.Port := #[]
  for port in head.ports do
    if port.readers.isSome then throw (.waiting "a handle port `@H -> R` (layer D)")
    let type ← evalType env port.type
    ports := ports.push { name := port.binder.name, span := port.binder.span, type
                          holders := port.holders, isPrivate := port.isPrivate
                          specification := port.specification }
  let mut results : Array Typed.ResultPort := #[]
  for result in head.results do
    if result.readers.isSome then throw (.waiting "a handle result `@H -> R` (layer D)")
    let type ← evalType env result.type
    results := results.push { name := result.name.text, type, holders := result.holders }
  return { roster := head.roster, ports, results, events := head.events
           specification := head.specification }

/-- The closed signature of a protocol instance: its head at the values of the instance. -/
def protocolSignatureOf (inst : InstanceId) : CompileM Typed.ProtocolSignature := do
  let state ← get
  let some entry := state.table.entries[inst]? | throw .abandoned
  let found ← declaration entry.key.declaration
  let some lowered := (← getModules).lowered? entry.key.declaration | throw .abandoned
  let .protocol head _ _ := lowered.content | throw .abandoned
  protocolSignatureIn head (instanceEnv state.program found entry.key.arguments entry.key.specification)

def protocolSignature (inst : InstanceId) : ElabM Typed.ProtocolSignature :=
  liftM (protocolSignatureOf inst : CompileM Typed.ProtocolSignature)

/-- Binds the name of an event to a value of a type, when the event has a name. -/
def eventBinder (binder : Option Lowered.Binder) (type : ClosedType) : ElabM (Option Typed.Binder) :=
  match binder with
  | some binder => some <$> bindLocal binder type
  | none => pure none

/-- A name that is no value of deployed code, bound so that a use of it is refused with what
it is. -/
def bindValueless (binder : Lowered.Binder) (what : String) : ElabM Unit := do
  discard <| bindLocal binder .unit
  modify fun state => { state with valueless := state.valueless.insert binder.id what }

/-- An application of a protocol (RM1 to RM3, SP6, SX4): the callee's instance, its roles mapped
by name, its arguments against its ports, its specification arguments, and one binder per
result. -/
def elabApplication (span : Span) (event : EventId) (binder : Option Lowered.Binder)
    (callee : Lowered.Reference) (arguments : Array Lowered.Argument)
    (written : Array (Name × Nat)) : ElabM (Array Typed.Stmt) := do
  let .reference calleeSpan _ := callee
  let calleeText ← textOf calleeSpan
  let .declaration steps scopes ← calleeOf callee
    | refuseHere "EV1" span s!"`{calleeText}` is no protocol: an event stands on its own `<-` line"
  let some (id, _) := steps.back? | throw .abandoned
  let found ← liftM (declaration id : CompileM Declaration)
  unless found.kind == .protocol do
    if found.kind == .function then
      refuseHere "EV1" span s!"`{calleeText}` is a function: bind it with `=`"
    refuseHere "EV1" span s!"`{calleeText}` is {Names.kindWord found.kind}: only a protocol is applied"
  let .protocol head _ _ := (← loweredOf id).content | throw .abandoned
  -- the specification ports take a specification argument each (SX4, RM3)
  let specificationNames := (head.ports.filter (·.specification)).map (·.binder.name)
  let mut namedSpec := #[]
  for argument in arguments do
    match argument with
    | .spec argumentSpan given value =>
      unless specificationNames.contains given.text do
        refuseHere "RM3" argumentSpan s!"`{calleeText}` has no specification port `{given.text}`"
      namedSpec := namedSpec.push (.named argumentSpan given value)
    | .named argumentSpan .. | .positional argumentSpan .. =>
      unless namedSpec.isEmpty do
        refuseHere "RM3" argumentSpan "value arguments precede specification arguments"
  let specValues ← match Lowered.pairValueArguments calleeText specificationNames namedSpec span with
    | .ok values => pure values
    | .error (where_, message) => refuseHere "SX4" where_ message
  -- every specification-only parameter of the callee is given by a specification argument, and a
  -- deployed static argument reads none (SP11); a parameter of a scope that the caller shares
  -- with the callee is the caller's own
  let state ← getThe Compile.State
  let context ← getContext
  let caller := state.program.declarations[state.table.entries[context.instance]!.key.declaration]!
  let supplied := steps.flatMap fun (_, args) => (args.getD #[]).filterMap fun
    | .spec at_ name term => some (at_, name, term)
    | _ => none
  let env ← staticEnv
  let proofArguments ← liftM (specificationClosure env found supplied caller.scopes span : CompileM _)
  -- a specification argument that reads the index of a loop typed as one loop is remembered:
  -- the loop refuses it when it stays one loop
  for (at_, _, term) in supplied do
    for binder in term.locals do
      if (← get).indices.contains binder then
        modify fun state => { state with proofIndexReads := state.proofIndexReads.push (binder, at_) }
  deployedStaticArguments steps
  -- the role map, by name (RM1)
  let roster := context.roster.getD #[]
  let mut explicitRoles : Std.HashMap String Nat := {}
  for (name, role) in written do
    unless head.roster.contains name.text do
      refuseHere "RM1" name.span s!"`{calleeText}` has no role {name.text}"
    if explicitRoles.contains name.text then
      refuseHere "RM1" name.span s!"the role map of `{calleeText}` binds {name.text} twice"
    explicitRoles := explicitRoles.insert name.text role
  let mut roleMap : Array Nat := #[]
  for name in head.roster do
    match explicitRoles[name]? with
    | some role => roleMap := roleMap.push role
    | none =>
      match roster.findIdx? (· == name) with
      | some index => roleMap := roleMap.push index
      | none =>
        refuseHere "RM1" span
          s!"role {name} of `{calleeText}` has no namesake in `{context.name}`: write `@({name} = …)`"
  for index in [0:roleMap.size] do
    if (roleMap.extract 0 index).contains roleMap[index]! then
      refuseHere "RM1" span s!"the role map of `{calleeText}` gives {← roleName roleMap[index]!} two roles"
  -- the arguments against the ports that are not specification ports, in order or by name (RM3),
  -- and the static arguments that they decide (SP6)
  let ports := head.ports.filter (!·.specification)
  let deployed := arguments.filter fun | .spec .. => false | _ => true
  let paired ← pairArguments calleeText (ports.map (·.binder.name)) deployed none span
  let assigned ← liftM (assignArguments env steps scopes span : CompileM _)
  let (values, states) ← inferArguments id assigned found.file
    (ports.map fun port => (port.binder.name, port.type)) none paired none span
  let description ← liftM (describeInstance id values : CompileM String)
  liftM (checkSelectedModules steps values span : CompileM Unit)
  let inst ← liftM (instantiate id values { description, span } : CompileM InstanceId)
  if let some closure := proofArguments then
    liftM (closure.checkApplication inst span)
  let signature ← protocolSignature inst
  let portTypes := (signature.ports.filter (!·.specification)).map (·.type)
  let typed ← finishArguments paired states portTypes
  let operands ← (typed.zip (targetsOf paired portTypes)).mapM fun (use, (target, place, quote)) =>
    convertTo use target place quote
  -- the order in which the arguments are written (HO4)
  let order := (List.range paired.size).toArray.qsort fun i j =>
    paired[i]!.span.startByte < paired[j]!.span.startByte
  -- the body of the callee, before its results are used
  liftM (context.protocolBody inst span)
  -- the specification arguments: typed against their ports at the callee's instance, in a
  -- specification, where the names of every role stand (SX4)
  let mut specification : Array (String × Typed.Expr) := #[]
  for port in signature.ports.filter (·.specification), value in specValues do
    let typedValue ← withContext (fun context => { context with specification := true })
      (elabAt value port.type)
    specification := specification.push (port.name, typedValue)
  -- one binder per result (RM3)
  let results := signature.results
  let apply (binders : Array (Option Typed.Binder)) : Typed.Stmt :=
    .event span event (.apply binders inst operands specification roleMap order proofArguments)
  match binder with
  | none =>
    if let some first := results[0]? then
      refuseHere "EV1" span s!"`{calleeText}` returns {first.name}; bind its result: `x <- {calleeText}(…)`"
    return #[apply #[]]
  | some binder =>
    match binder.origin, results with
    | .written, #[] =>
      -- the name names the site
      bindValueless binder s!"the site of an application of `{calleeText}`, which returns nothing"
      return #[apply #[]]
    | .written, #[result] => return #[apply #[some (← bindLocal binder result.type)]]
    | .discarded, _ =>
      unless results.isEmpty do
        refuseHere "TY13" span s!"the results of `{calleeText}` are bound by one name or a tuple pattern"
      return #[apply #[]]
    | _, _ =>
      -- several results, or a pattern: one binder per result, read by `y.r` or taken by the
      -- levels of the pattern that follow
      let mut bound : Array (String × Typed.Binder) := #[]
      for result in results do
        let made ← freshBinder s!"{binder.name}.{result.name}" binder.span result.type .patternValue
        bound := bound.push (result.name, made)
      bindValueless binder s!"the results of an application of `{calleeText}`"
      modify fun state => { state with results := state.results.insert binder.id bound }
      return #[apply (bound.map fun (_, made) => some made)]

/-- An event of a protocol body. -/
def elabEvent (span : Span) (event : EventId) (binder : Option Lowered.Binder)
    (type : Option Lowered.TypeTerm) (roles : Option RoleSet) (what : Lowered.Event) :
    ElabM (Array Typed.Stmt) := do
  if (← getContext).roster.isNone then
    refuseHere "FN1" span "an event stands only in a protocol body; a `def` runs inside one role"
  match what with
  | .oracleSend .. => waitFor "an oracle send (layer D)"
  | .query .. => waitFor "a `query` (layer D)"
  | .openClaims .. => waitFor "an `open` (layer D)"
  | .send payload sender receivers =>
    if roles.isSome then
      refuseHere "HO5" span "the binder of a `send` takes no `@`: the event determines its holders"
    -- the payload, at a written type when one is written; the name has the type on the wire at
    -- every holder, the sender included (TY14)
    let typed ← match type with
      | some written => elabAt payload (← liftM (evalType (← staticEnv) written : CompileM ClosedType))
      | none => elabExpr payload none
    let bound ← eventBinder binder typed.type
    return #[.event span event (.send bound typed sender receivers)]
  | .draw law owner receivers =>
    if roles.isSome then
      refuseHere "HO5" span "the binder of a `draw` takes no `@`: the event determines its holders"
    if receivers.contains owner then
      refuseHere "EV6" span
        s!"{← roleName owner} draws and receives; a coin that nobody else receives is a `sample`"
    let lawType ← liftM (evalType (← staticEnv) law : CompileM ClosedType)
    let row ← lawOf lawType (Lowered.Expr.span (.type law))
    let bound ← eventBinder binder lawType
    return #[.event span event (.draw bound row owner receivers)]
  | .sample law =>
    let message := "the binder of a `sample` names its one role: `s @P <- sample T`"
    let some written := roles | refuseHere "HO5" span message
    let #[role] := written.toArray | refuseHere "HO5" span message
    let lawType ← liftM (evalType (← staticEnv) law : CompileM ClosedType)
    let row ← lawOf lawType (Lowered.Expr.span (.type law))
    let bound ← eventBinder binder lawType
    return #[.event span event (.sample bound row role)]
  | .attempt =>
    if roles.isNone then
      refuseHere "HO5" span "the binder of an `attempt` names its one role: `k @P <- attempt`"
    waitFor "`attempt`, which is not elaborated yet"
  | .apply callee arguments roleMap => elabApplication span event binder callee arguments roleMap

end Zkc.Frontend.Elab
