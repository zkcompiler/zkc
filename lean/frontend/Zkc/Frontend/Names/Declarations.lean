module

public import Zkc.Frontend.Names.Terms

@[expose] public section

set_option autoImplicit false

/-!
# Resolution and lowering of declarations

Each declaration is resolved and lowered in its environment, reached or not (SP7): its parameter
scope, its signature and its body, with the local names that the production binds. A member
definition of an implementing module has in scope the static parameters that the interface gives
the member, under their names, and not its own name (SP8). A contract reads the static parameters
and the ports of its protocol, the results in `ensures` and on the right of `reduces`, and in a
clause `… at i` the names visible at the loop `i` (SX5). A goal reads the words of GL2, a label
after `clause` and roles after `corrupted`.

A kind that is not lowered yet (a module, an interface, a member that declares no definition, a
contract, a scheme, a goal, an oracle function) keeps its resolved names as lowered terms. The
path and the name of a `use` are lowered too, so that every resolution of the program stands in
the lowered form.
-/

namespace Zkc.Frontend.Names

open Syntax
open Lowered (Binder)

/-- An environment with the facts of the `where` clauses of its scopes. -/
def makeEnv (owner : Owner) (file : FileId) (ns : NamespaceId) (scopes : Array ScopeId)
    (excluded? : Option DeclarationId := none) (host? : Option DeclarationId := none) :
    ResolveM Env := do
  let program := (← get).program
  let base : Env := { plainEnv program owner file ns scopes with excluded?, host? }
  let mut facts := #[]
  for scope in scopes do
    if let some whereClause := (program.scopes[scope]?).bind (·.whereClause) then
      facts := facts ++ (← factsOf base whereClause)
  return { base with facts }

/-- A path as a lowered term: its reference, or an error when it does not resolve. -/
def pathTerm (env : Env) (path : Path) (position : Position := .plain) : ResolveM Lowered.Expr := do
  match (← resolvePath env path position).2 with
  | some reference => return .reference reference
  | none => return .error path.span

def resolveBound (env : Env) (bound : Bound) : ResolveM Lowered.Bound := do
  let sorts ← bound.sorts.mapM fun
    | .nat span => pure (Lowered.SortTerm.nat span)
    | .linear span => pure (Lowered.SortTerm.linear span)
    | .path path => do
      return .reference ((← resolvePath env path .plain).2.getD (.reference path.span #[]))
  return { span := bound.span, sorts }

/-- The terms that a bound names. -/
def boundTerms (bound : Lowered.Bound) : Array Lowered.Expr :=
  bound.sorts.filterMap fun
    | .reference reference => some (.reference reference)
    | _ => none

/-- The static parameters of one list: their bounds. A list names a parameter once (NL2). -/
def resolveParameters (env : Env) (parameters : Array StaticParam) :
    ResolveM (Array (Option Lowered.Bound)) := do
  let mut seen : Std.HashMap String Span := {}
  let mut bounds := #[]
  for parameter in parameters do
    if let some earlier := seen[parameter.name.text]? then
      refuseAt env.owner "NL2" parameter.name.span
        s!"`{parameter.name.text}` is already a static parameter at line {earlier.startLine}; a name is bound once"
    seen := seen.insert parameter.name.text parameter.name.span
    bounds := bounds.push (← parameter.bound.mapM (resolveBound env))
  return bounds

def resolveWhere (env : Env) (whereClause : Where) : ResolveM (Array Lowered.Constraint) :=
  whereClause.constraints.mapM fun
    | .bound span subject bound => do
      let subject ← resolveExprAt env .plain subject
      return Lowered.Constraint.bound span subject (← resolveBound env bound).sorts
    | .compare span operator left right => do
      let left ← resolveExprAt env .plain left
      return .compare span (operatorOfCompare operator) left (← resolveExprAt env .plain right)

def resolveOptionalWhere (env : Env) (whereClause : Option Where) :
    ResolveM (Array Lowered.Constraint) :=
  match whereClause with
  | some whereClause => resolveWhere env whereClause
  | none => pure #[]

def resolveStaticParams (env : Env) (parameters : Option StaticParams) :
    ResolveM (Array (Option Lowered.Bound)) :=
  match parameters with
  | some parameters => resolveParameters env parameters.params
  | none => pure #[]

/-- The parameters of a definition: each type, then its name. -/
def bindParams (env : Env) (parameters : Array Param) : ResolveM (Array Lowered.Parameter) :=
  parameters.mapM fun parameter => do
    let type ← resolveType env parameter.type
    return { binder := ← bindLocal env parameter.name, type }

def resolvePrimitive (env : Env) (primitive : Primitive) : ResolveM (Array Lowered.StaticArgument) :=
  primitive.args.mapM (resolveStaticArg env)

/-- The terms of static arguments. -/
def argumentTerms (arguments : Array Lowered.StaticArgument) : Array Lowered.Expr :=
  arguments.filterMap fun
    | .term _ _ term | .spec _ _ term => some term
    | .inferred .. => none

def resolveDefBinding (env : Env) : DefBinding → ResolveM Lowered.FunctionBody
  | .body body => do return .body (← resolveBody env body)
  | .primitive primitive => do
    return .primitive primitive.span primitive.row.content (← resolvePrimitive env primitive)
  | .external external => return .external external.span external.name.content

/-- A protocol head: its static parameters, its ports, which it binds, the types of its results,
and its `where`; the bounds and constraints of its scope beside it. -/
def resolveHead (env : Env) (head : ProtocolHead) (specification : Bool) :
    ResolveM (Lowered.ProtocolHead × Array (Option Lowered.Bound) × Array Lowered.Constraint) := do
  modify fun state => { state with roster := head.roles.map (·.text) }
  let bounds ← resolveStaticParams env head.staticParams
  let ports ← head.ports.mapM fun
    | .port _ name type placement isPrivate => do
      let type ← resolveType env type
      let holders ← holdersOf placement.holders
      let readers ← placement.readers.mapM holdersOf
      return ({ binder := ← bindLocal env name, type, holders, readers, isPrivate } : Lowered.Port)
    | .spec _ name type => do
      let type ← resolveType env type
      return { binder := ← bindLocal env name, type, holders := .empty, specification := true }
  let resultPort (result : Result) : ResolveM Lowered.ResultPort := do
    return { name := result.name, type := ← resolveType env result.type
             holders := ← holdersOf result.placement.holders
             readers := ← result.placement.readers.mapM holdersOf }
  let results ← match head.results with
    | some (.one result) => do pure #[← resultPort result]
    | some (.several _ results) => results.mapM resultPort
    | none => pure #[]
  let constraints ← resolveOptionalWhere env head.whereClause
  return ({ roster := head.roles.map (·.text), ports, results, events := #[], specification },
    bounds, constraints)

def resolveLaw (env : Env) (law : Law) :
    ResolveM (Lowered.Content × Array (Option Lowered.Bound) × Array Lowered.Constraint) := do
  let bounds ← resolveStaticParams env law.staticParams
  let parameters ← bindParams env law.params
  let constraints ← resolveOptionalWhere env law.whereClause
  let body ← resolveBody env law.body
  return (.function { parameters, result := some (.bool law.span), specification := true } (.body body),
    bounds, constraints)

def resolveDef (env : Env) (node : Def) :
    ResolveM (Lowered.Content × Array (Option Lowered.Bound) × Array Lowered.Constraint) := do
  let bounds ← resolveStaticParams env node.staticParams
  let parameters ← bindParams env node.params
  let result ← node.result.mapM (resolveType env)
  let constraints ← resolveOptionalWhere env node.whereClause
  let body ← resolveDefBinding env node.binding
  let head : Lowered.FunctionHead :=
    { parameters, result, specification := node.modifier matches some (.spec _)
      kernel := node.kernel.map (·.name.content) }
  return (.function head body, bounds, constraints)

/-! ## Contracts -/

mutual
  partial def patternNames : Pattern → Array String
    | .name name => #[name.text]
    | .wildcard _ => #[]
    | .tuple _ items => items.foldl (init := #[]) fun names item => names ++ patternNames item
    | .record _ _ fields => fields.foldl (init := #[]) fun names field =>
        match field with
        | .fieldPattern _ name none => names.push name.text
        | .fieldPattern _ _ (some pattern) => names ++ patternNames pattern

  partial def casePatternNames : CasePattern → Array String
    | .pattern pattern => patternNames pattern
    | .variant _ _ payload => (payload.getD #[]).foldl (init := #[]) fun names item =>
        names ++ casePatternNames item
    | .tuple _ items => items.foldl (init := #[]) fun names item => names ++ casePatternNames item
    | .number _ | .trueLiteral _ | .falseLiteral _ => #[]
end

/-- For each loop of a body whose index is one name, the names visible at the loop: those bound
before it, its index, and its collected names. -/
partial def loopScopes (statements : Array Stmt) (names : Array String)
    (scopes : Std.HashMap String (Array String)) :
    Array String × Std.HashMap String (Array String) := Id.run do
  let mut names := names
  let mut scopes := scopes
  for statement in statements do
    match statement with
    | .binding _ pattern _ _ _ | .eventStmt (.bound _ _ pattern _ _ _) =>
      names := names ++ patternNames pattern
    | .mutDecl _ name _ _ _ => names := names.push name.text
    | .«if» _ _ thenSuite elseBranch =>
      scopes := (loopScopes thenSuite names scopes).2
      match elseBranch with
      | some (.suite _ suite) => scopes := (loopScopes suite names scopes).2
      | some (.elseIf statement) => scopes := (loopScopes #[statement] names scopes).2
      | none => pure ()
    | .«match» _ _ cases =>
      for case in cases do
        let .«case» _ pattern body := case
        scopes := (loopScopes body (names ++ casePatternNames pattern) scopes).2
    | .«for» _ pattern _ collected body =>
      let index := patternNames pattern
      let collectedNames := (collected.getD #[]).map (·.name.text)
      if let .name loop := pattern then
        unless scopes.contains loop.text do
          scopes := scopes.insert loop.text (names ++ index ++ collectedNames)
      scopes := (loopScopes body (names ++ index) scopes).2
      names := names ++ collectedNames
    | _ => pure ()
  return (names, scopes)

/-- Runs `action` with these names added to the local names that are not already in scope. -/
def withNames {α : Type} (names : Array String) (action : ResolveM α) : ResolveM α := do
  pushSuite
  for name in names do
    unless (← get).locals.contains name do discard <| addLocal name default
  let result ← action
  popSuite
  return result

def resolveExtractor (env : Env) : Extractor → ResolveM (Array Lowered.Expr)
  | .path path => do return #[← pathTerm env path]
  | .external _ _ => return #[]

def resolveClause (env : Env) (results : Array String)
    (loops : Std.HashMap String (Array String)) : Clause → ResolveM (Array Lowered.Expr)
  | .requires _ _ condition | .proves _ _ _ condition | .charge _ _ condition => do
    return #[← resolveExpr env condition]
  | .ensures _ _ condition => do return #[← withNames results (resolveExpr env condition)]
  | .invariant _ _ condition loop | .through _ condition loop =>
    -- a loop that is not one of the protocol is refused with the clause (SX6)
    match loops[loop.text]? with
    | some names => do return #[← withNames names (resolveExpr env condition)]
    | none => pure #[]
  | .reduces _ _ _ source target => do
    let source ← resolveExpr env source
    return #[source, ← withNames results (resolveExpr env target)]
  | .knowledge _ _ relation extractor alternative => do
    let mut names := #[← resolveExpr env relation]
    names := names ++ (← resolveExtractor env extractor)
    if let some alternative := alternative then
      names := names.push (← resolveExpr env alternative.relation)
      if let some path := alternative.extractor then names := names.push (← pathTerm env path)
    return names
  | .zeroKnowledge _ _ simulator _ => resolveExtractor env simulator

def resolveContract (id : DeclarationId) (declaration : Declaration) (node : Contract) :
    ResolveM (Array Lowered.Expr) := do
  let program := (← get).program
  let outer ← makeEnv (.declaration id) declaration.file declaration.namespace declaration.scopes
  startLocals
  let (target, reference) ← resolvePath outer node.target .plain
  let targetName : Lowered.Expr := match reference with
    | some reference => .reference reference
    | none => .error node.target.span
  let .declaration protocolId := target | return #[targetName]
  let some callee := program.declarations[protocolId]? | return #[targetName]
  let (ports, results, body) : Array Name × Array String × Array Stmt := match callee.node with
    | .protocol protocol =>
      (protocol.head.ports.map (fun
          | .port _ name _ _ _ => name
          | .spec _ name _ => name),
        match protocol.head.results with
        | some (.one result) => #[result.name.text]
        | some (.several _ results) => results.map (·.name.text)
        | none => #[],
        protocol.body)
    | .«def» function => (function.params.map (·.name), #[], #[])
    | .relation relation =>
      (relation.statement.map (·.name) ++ (relation.witness.getD #[]).map (·.name), #[], #[])
    | _ => (#[], #[], #[])
  let env ← makeEnv (.declaration id) declaration.file declaration.namespace callee.scopes
  startLocals
  for port in ports do discard <| addLocal port.text port.span
  let loops := (loopScopes body (ports.map (·.text)) {}).2
  let mut names := #[targetName]
  for clause in node.clauses do names := names ++ (← resolveClause env results loops clause)
  return names

/-! ## Schemes and goals -/

def resolveScheme (env : Env) (node : Scheme) : ResolveM (Array Lowered.Expr) := do
  let mut names := #[← pathTerm env node.protocol]
  for line in node.lines do
    match line with
    | .construction _ (.derived _ suite) => names := names.push (← pathTerm env suite)
    | .construction _ _ | .prover _ _ | .offline _ _ | .ideal _ _ => pure ()
    | .context _ _ type => names := names.push (.type (← resolveType env type))
    | .commit _ subject scheme _ =>
      if let .term term := subject then names := names.push (← resolveExprAt env .plain term)
      names := names.push (← pathTerm env scheme)
    | .pin _ _ hash _ => names := names.push (← pathTerm env hash)
    | .grind _ bits _ => names := names.push (← resolveExprAt env .plain bits)
    | .retry _ count _ => names := names.push (← resolveExprAt env .plain count)
    | .samples _ derivation => names := names.push (← pathTerm env derivation)
    | .layout _ layout adjustments =>
      names := names.push (← pathTerm env layout)
      for adjustment in adjustments.getD #[] do
        if let .recover _ _ recovery := adjustment then
          names := names.push (← pathTerm env recovery)
  return names

/-- The arguments of a goal whose values are words (GL2): which word stands there is checked
with the goal. -/
def wordArguments : Array String := #["stage", "statement", "decisions"]

/-- A value of an argument of a goal. A single name is a label after `clause`, a role after
`corrupted`, a word after `stage`, `statement` and `decisions` and wherever it is a word of GL2;
otherwise a path. -/
partial def resolveGoalValue (env : Env) (argument : String) : GoalValue → ResolveM (Array Lowered.Expr)
  | .tuple _ items => do
    let mut names := #[]
    for item in items do names := names ++ (← resolveGoalValue env argument item)
    return names
  | .path _ path args => do
    let mut names := #[]
    match path.plainName? with
    | some name =>
      if argument == "clause" then names := names.push (.reference (oneStep path.span (.label name.text)))
      else if argument == "corrupted" then
        names := names.push (.reference (oneStep path.span (.role name.text)))
      else if wordArguments.contains argument || goalWords.contains name.text then
        names := names.push (.reference (oneStep path.span (.word name.text)))
      else names := names.push (← pathTerm env path)
    | none => names := names.push (← pathTerm env path)
    if let some args := args then
      let (arguments, witnesses) ← resolveCallArgs env .value args
      for argument in arguments ++ witnesses.getD #[] do
        match argument with
        | .positional _ value | .named _ _ value | .spec _ _ value => names := names.push value
    return names

def resolveGoal (env : Env) (node : Goal) : ResolveM (Array Lowered.Expr) := do
  let mut names := #[← pathTerm env node.property, ← pathTerm env node.scheme]
  for argument in node.args do
    match argument with
    | .named _ name value => names := names ++ (← resolveGoalValue env name.text value)
    | .spec _ _ size => names := names.push (← resolveExprAt env .plain size)
  if let some ceiling := node.ceiling then names := names.push (← resolveExpr env ceiling)
  return names

/-! ## Declarations -/

/-- The scope of a member of an interface that a member definition defines: the member's own
static parameters are in scope in the definition under the names the interface gives them. -/
def memberScope (declaration : Declaration) (name : String) : ResolveM (Option ScopeId) := do
  let program := (← get).program
  let some ns := program.namespaces[declaration.namespace]? | return none
  let known ← moduleKnown ns.owner
  let some member ← findMember (← closure known.interfaces) name | return none
  return (program.declarations[member]?).bind (·.ownScope)

/-- What a declaration is, lowered, with the bounds and the constraints of its own scope. -/
def declarationContent (id : DeclarationId) (declaration : Declaration) :
    ResolveM (Lowered.Content × Array (Option Lowered.Bound) × Array Lowered.Constraint) := do
  let program := (← get).program
  let owner := Owner.declaration id
  let ownParameters : Array StaticParam :=
    ((declaration.ownScope.bind fun scope => program.scopes[scope]?).map (·.parameters)).getD #[]
  let ownWhere : Option Where :=
    declaration.ownScope.bind fun scope => (program.scopes[scope]?).bind (·.whereClause)
  let standard ← makeEnv owner declaration.file declaration.namespace declaration.scopes
  match declaration.node with
  | .file _ =>
    let env ← makeEnv owner declaration.file (declaration.inner.getD declaration.namespace)
      declaration.scopes
    let bounds ← resolveParameters env ownParameters
    return (.unlowered #[], bounds, ← resolveOptionalWhere env ownWhere)
  | .«module» (.«module» _ _ _ _ bound _ body) =>
    let host := if hasNoBody declaration then some id else none
    let env ← makeEnv owner declaration.file (declaration.inner.getD declaration.namespace)
      declaration.scopes (host? := host)
    let bounds ← resolveParameters env ownParameters
    let mut names := #[]
    if let some bound := bound then names := names ++ boundTerms (← resolveBound env bound)
    let constraints ← resolveOptionalWhere env ownWhere
    match body with
    | .primitive primitive => names := names ++ argumentTerms (← resolvePrimitive env primitive)
    | .suite _ | .asset _ => pure ()
    return (.unlowered names, bounds, constraints)
  | .interface _ =>
    let env ← makeEnv owner declaration.file (declaration.inner.getD declaration.namespace)
      declaration.scopes
    let bounds ← resolveParameters env ownParameters
    return (.unlowered #[], bounds, ← resolveOptionalWhere env ownWhere)
  | .member member =>
    match member with
    | .typeMember _ _ parameters bound =>
      let bounds ← resolveStaticParams standard parameters
      let names := match ← bound.mapM (resolveBound standard) with
        | some bound => boundTerms bound
        | none => #[]
      return (.unlowered names, bounds, #[])
    | .natMember .. => return (.unlowered #[], #[], #[])
    | .moduleMember _ _ bound => return (.unlowered (boundTerms (← resolveBound standard bound)), #[], #[])
    | .defMember _ modifier _ parameters params result whereClause =>
      let bounds ← resolveStaticParams standard parameters
      let parameters ← bindParams standard params
      let result ← result.mapM (resolveType standard)
      let constraints ← resolveOptionalWhere standard whereClause
      return (.function { parameters, result, specification := modifier matches some (.spec _) } .absent,
        bounds, constraints)
    | .protocolMember head =>
      let (head, bounds, constraints) ← resolveHead standard head false
      return (.protocol head #[] #[], bounds, constraints)
    | .lawMember law => resolveLaw standard law
  | .typeDecl node =>
    match node with
    | .type _ _ _ parameters value =>
      let bounds ← resolveStaticParams standard parameters
      match value with
      | .type type => return (.alias (← resolveType standard type), bounds, #[])
      | .primitive primitive =>
        let arguments ← resolvePrimitive standard primitive
        return (.vocabularyType primitive.row.content arguments, bounds, #[])
    | .specType _ _ _ parameters _ =>
      return (.unlowered #[], ← resolveStaticParams standard parameters, #[])
  | .struct node =>
    let bounds ← resolveStaticParams standard node.staticParams
    let fields ← node.fields.mapM fun field => do return (field.name, ← resolveType standard field.type)
    return (.record node.linear fields, bounds, #[])
  | .enum node =>
    let bounds ← resolveStaticParams standard node.staticParams
    let alternatives ← node.alternatives.mapM fun alternative => do
      return (alternative.name, ← alternative.payload.mapM (resolveType standard))
    return (.«variant» alternatives, bounds, #[])
  | .«def» node => resolveDef standard node
  | .oracleDef node =>
    let bounds ← resolveStaticParams standard node.staticParams
    let parameters ← bindParams standard node.params
    let mut names : Array Lowered.Expr := parameters.map (.type ·.type)
    names := names.push (← pathTerm standard node.kind)
    let constraints ← resolveOptionalWhere standard node.whereClause
    pushSuite
    discard <| bindLocal standard node.position
    names := names.push (← resolveExpr standard node.row)
    popSuite
    return (.unlowered names, bounds, constraints)
  | .protocol node =>
    let (head, bounds, constraints) ← resolveHead standard node.head node.spec
    let body ← resolveStmts standard node.body
    let results ← node.result.mapM (resolveExpr standard)
    let events := (← get).events
    return (.protocol { head with events } body results.toArray, bounds, constraints)
  | .relation node =>
    let bounds ← resolveStaticParams standard node.staticParams
    let statement ← bindParams standard node.statement
    let witness ← bindParams standard (node.witness.getD #[])
    let constraints ← resolveOptionalWhere standard node.whereClause
    let head : Lowered.FunctionHead :=
      { parameters := statement ++ witness, result := some (.bool node.span)
        statementParameters := some statement.size, specification := true }
    match node.binding with
    | .body body => return (.function head (.body (← resolveBody standard body)), bounds, constraints)
    | .external external =>
      return (.function head (.external external.span external.name.content), bounds, constraints)
  | .staticName node => return (.staticName (← resolveExprAt standard .plain node.size), #[], #[])
  | .law node => resolveLaw standard node
  | .contract node => return (.unlowered (← resolveContract id declaration node), #[], #[])
  | .scheme node => return (.unlowered (← resolveScheme standard node), #[], #[])
  | .goal node => return (.unlowered (← resolveGoal standard node), #[], #[])
  | .moduleMember node => return (.unlowered #[← pathTerm standard node.path], #[], #[])
  | .memberDef node =>
    let scopes := match ← memberScope declaration node.name.text with
      | some scope => declaration.scopes.push scope
      | none => declaration.scopes
    let env ← makeEnv owner declaration.file declaration.namespace scopes (excluded? := some id)
    let binders ← node.params.mapM fun binder => bindLocal env binder
    return (.memberDefinition binders (← resolveDefBinding env node.binding), #[], #[])

/-- Resolves and lowers a declaration: its lowered form, and that of its own parameter scope. -/
def resolveDeclaration (id : DeclarationId) : ResolveM (Lowered.Declaration × Option Lowered.Scope) := do
  let program := (← get).program
  let some declaration := program.declarations[id]? | return ({ id, content := .unlowered #[] }, none)
  startDeclaration
  let (content, bounds, constraints) ← declarationContent id declaration
  let state ← get
  let scope := declaration.ownScope.map fun scope => ({ id := scope, bounds, constraints } : Lowered.Scope)
  return ({ id, locals := state.binders.size, binders := state.binders, content
            refused := state.refusals.contains (.declaration id), unknownRoles := state.unknownRoles },
    scope)

/-- The parameters and the `where` of a section, lowered. -/
def resolveSection (id : ScopeId) : ResolveM (Option Lowered.Scope) := do
  let program := (← get).program
  let some scope := program.scopes[id]? | return none
  let env ← makeEnv (.scope id) scope.file scope.namespace (chainOf program id)
  startDeclaration
  let bounds ← resolveParameters env scope.parameters
  let constraints ← resolveOptionalWhere env scope.whereClause
  return some { id, bounds, constraints }

/-- The path of a `use` and the name it binds, as lowered terms. A path is written once for the
names that one `use` lists: it is resolved and lowered with the first of them, and the others
keep only their names. -/
def resolveImport (id : ImportId) (first : Bool) : ResolveM (Array Lowered.Expr) := do
  let program := (← get).program
  let some entry := program.imports[id]? | return #[]
  let env := importEnv program id
  let found? ← importFound id
  if first then
    for current in segmentsOf entry.path do
      if let some args := segmentArgs current then
        let lowered ← resolveStaticArgs env args
        let .staticArgs span _ := args
        modify fun state => { state with
          importArguments := state.importArguments.insert (entry.file, span.startByte) lowered }
  let mut names := #[]
  if first then
    if let some segments := (← get).importPaths[id]? then
      unless segments.isEmpty do
        names := names.push (.reference (← lowerSegments env entry.path.span segments {}))
  let some found := found? | return names
  if let .poisoned := found.target then return names
  match entry.selected, entry.path with
  | some _, _ =>
    names := names.push (.reference (← lowerSegments env entry.name.span found.segments {}))
  | none, .path span _ =>
    if entry.name.span.startByte < span.startByte || entry.name.span.startByte >= span.stopByte then
      names := names.push (.reference (← lowerSegments env entry.name.span found.segments {}))
  return names

end Zkc.Frontend.Names
