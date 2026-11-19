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

/-- An extractor or simulator names executable code. A member left open by a static
parameter can only be classified when that parameter is instantiated. -/
def resolveAlgorithm (env : Env) (path : Path) : ResolveM Lowered.Expr := do
  let (target, some reference) ← resolvePath env path .plain | return .error path.span
  let program := (← get).program
  let executable : Bool := match target with
    | .declaration id | .member id => (program.declarations[id]?).any fun decl =>
      match decl.node with
      | .«def» f => !(f.modifier matches some (.spec _))
      | .member (.defMember _ modifier ..) => !(modifier matches some (.spec _))
      | .memberDef f => !f.spec
      | _ => false
    | .«open» => true
    | _ => false
  unless executable do
    refuseAt env.owner "SX6" path.span "the function after `by` must be an executable def"
  return .reference reference

def resolveExtractor (env : Env) : Extractor → ResolveM (AlgorithmRef Lowered.Expr)
  | .path path => do return .path (← resolveAlgorithm env path)
  | .external span name => return .external span name

/-- A proposition may be a Boolean expression or a relation application. Each extracted
knowledge branch names the relation for which its algorithm supplies a witness. -/
inductive ClauseOperand where
  | proposition
  | knowledge (requireWitness : Bool)

def checkClauseCall (env : Env) (span : Span) (use : ClauseOperand)
    (callee : Lowered.Reference) (arguments : Array Lowered.Argument)
    (witnesses : Option (Array Lowered.Argument)) : ResolveM Unit := do
  let knowledge := use matches .knowledge _
  if knowledge && witnesses.isSome then
    return ← refuseAt env.owner "SX6" span "apply the knowledge relation to its statement arguments only"
  if callee.lastStep? matches some (.member _ none) then return
  let program := (← get).program
  let relation : Option Relation := do
    let id ← callee.declaration?
    let .relation r := (← program.declarations[id]?).node | none
    return r
  let some r := relation | do
    if knowledge then refuseAt env.owner "SX6" span "the knowledge clause must apply a relation"
    else if witnesses.isSome then refuseAt env.owner "SX3" span "only a relation takes witness arguments"
    return
  let witnessCount := (r.witness.getD #[]).size
  unless arguments.size == r.statement.size && witnesses.all (·.size == witnessCount) do
    return ← refuseAt env.owner "SX3" span
      s!"the relation `{r.name.text}` takes {r.statement.size} statement arguments and {witnessCount} witness arguments"
  let checkNames (params : Array Param) (args : Array Lowered.Argument) := do
    if args.any (fun | .named .. | .spec .. => true | _ => false) then
      if let .error (at_, message) := Lowered.pairValueArguments r.name.text (params.map (·.name.text)) args span then
        refuseAt env.owner "FN6" at_ message
  checkNames r.statement arguments
  for ws in witnesses do checkNames (r.witness.getD #[]) ws
  if (use matches .knowledge true) && witnessCount == 0 then
    refuseAt env.owner "SX6" span "an extracted alternative needs a relation with a witness"

def resolveOperand (env : Env) (expr : Expr) (use : ClauseOperand) : ResolveM Lowered.Expr := do
  let term ← resolveExpr env expr
  match term with
  | .error _ => pure ()
  | .call _ callee args witnesses => checkClauseCall env expr.span use callee args witnesses
  | _ =>
    if use matches .knowledge _ then
      refuseAt env.owner "SX6" expr.span "the knowledge clause must apply a relation"
  return term

/-- Resolve SX6 against the placements of this clause's own inputs and results. Local
binders introduced by expressions and specification-only ports impose no role constraint. -/
def resolveDecidingRole (env : Env) (head : Option ProtocolHead) (span : Span)
    (role : Option Name) (terms : Array Lowered.Expr) : ResolveM (Option Nat) := do
  let some head := head | return none
  -- Role eligibility assumes well-formed operands, in particular a valid witness split.
  if (← get).refusals.contains env.owner then return none
  let locals := (← get).locals
  let mut placements : Std.HashMap LocalId Placement := {}
  let insert (table : Std.HashMap LocalId Placement) (name : Name) (p : Placement) :=
    (locals[name.text]?).elim table fun binding => table.insert binding.binder p
  for port in head.ports do
    if let .port _ name _ placement _ := port then placements := insert placements name placement
  let results := match head.results with
    | some (.one result) => #[result]
    | some (.several _ many) => many
    | none => #[]
  for result in results do placements := insert placements result.name result.placement
  let contains (name : String) : Holders → Bool
    | .role r => r.text == name
    | .roles _ rs => rs.any (·.text == name)
  let program := (← get).program
  let oracle := program.modules["zkc::oracle"]?
  let projectsData : Step → Bool
    | .entry "zkc::oracle" "data" => true
    | .declaration id => (program.declarations[id]?).any fun d =>
      program.nameOf id == "data" && (program.namespaces[d.namespace]?).any (fun ns => some ns.owner == oracle)
    | _ => false
  let reads (term : Lowered.Expr) := term.mapLocalReads (fun id data => (id, data)) projectsData
  let mut statement := #[]
  let mut witness := #[]
  for term in terms do
    match term with
    | .call sp callee args (some ws) =>
      statement := statement ++ reads (.call sp callee args none)
      for w in ws do
        match w with
        | .positional _ e | .named _ _ e | .spec _ _ e => witness := witness ++ reads e
    | _ => statement := statement ++ reads term
  let eligible := head.roles.filter fun r =>
    let holds (use : LocalId × Bool) (wanted : Bool) :=
      (placements[use.1]?).all fun p =>
        let reader := p.readers.any (contains r.text)
        let visible := reader || (!(use.2 && p.readers.isSome) && contains r.text p.holders)
        visible == wanted
    statement.all (holds · true) && witness.all (holds · false)
  let chosen : Option Name := match role with
    | some name => eligible.find? (fun r : Name => r.text == name.text)
    | none => if eligible.size == 1 then eligible[0]? else none
  let some chosen := chosen | do
    refuseAt env.owner "SX6" span "name an eligible deciding role that sees every statement operand and holds no witness operand"
    return none
  return head.roles.findIdx? (fun r : Name => r.text == chosen.text)

def resolveClause (env : Env) (head : Option ProtocolHead) (results : Array String)
    (loops : Std.HashMap String (Array String)) (clause : Clause) : ResolveM Lowered.Clause := do
  let atLoop (loop : Name) (condition : Expr) (action : ResolveM Lowered.Expr) := do
    let some names := loops[loop.text]? | do
      refuseAt env.owner "SX6" loop.span s!"no loop is indexed by `{loop.text}` in the contract target"
      return Lowered.Expr.error condition.span
    withNames names action
  match clause with
  | .requires sp label e => return .requires sp label (← resolveExpr env e)
  | .charge sp site bound => return .charge sp site (← resolveExpr env bound)
  | .ensures sp label e => return .ensures sp label (← withNames results (resolveExpr env e))
  | .invariant sp label e loop =>
    return .invariant sp label (← atLoop loop e (resolveExpr env e)) loop
  | .through sp e loop =>
    return .through sp (← atLoop loop e (resolveOperand env e .proposition)) loop
  | .proves sp role label e =>
    let e ← resolveOperand env e .proposition
    return .proves sp (← resolveDecidingRole env head sp role #[e]) label e
  | .reduces sp role label source target =>
    let source ← resolveOperand env source .proposition
    withNames results do
      let target ← resolveOperand env target .proposition
      return .reduces sp (← resolveDecidingRole env head sp role #[source, target]) label source target
  | .knowledge sp label relation extractor alternative =>
    let relation ← resolveOperand env relation (.knowledge false)
    let algorithm ← resolveExtractor env extractor
    let alternative ← alternative.mapM fun branch => do
      let needsWitness := extractor matches .path _
      let term ← resolveOperand env branch.relation (.knowledge needsWitness)
      let path ← branch.extractor.mapM (resolveAlgorithm env)
      if needsWitness && path.isNone then
        refuseAt env.owner "SX6" branch.relation.span "name the extractor for this alternative with `by`"
      return ⟨branch.span, term, path⟩
    return .knowledge sp label relation algorithm alternative
  | .zeroKnowledge sp label simulator abilities =>
    return .zeroKnowledge sp label (← resolveExtractor env simulator) abilities

def resolveContract (id : DeclarationId) (declaration : Declaration) (node : Contract) :
    ResolveM Lowered.Contract := do
  let program := (← get).program
  let outer ← makeEnv (.declaration id) declaration.file declaration.namespace declaration.scopes
  startLocals
  let (target, reference) ← resolvePath outer node.target .plain
  let targetName : Lowered.Expr := match reference with
    | some reference => .reference reference
    | none => .error node.target.span
  let .declaration protocolId := target | return ⟨node.span, targetName, #[]⟩
  let some callee := program.declarations[protocolId]? | return ⟨node.span, targetName, #[]⟩
  if callee.file != declaration.file || callee.namespace != declaration.namespace then
    refuseAt outer.owner "SX5" node.target.span "the contract must be in the module that defines its target"
  else if (← get).contractOwners.contains protocolId then
    refuseAt outer.owner "SX5" node.target.span "a declaration has more than one contract"
  else
    modify fun s => { s with contractOwners := s.contractOwners.insert protocolId }
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
    | .«def» function =>
      let statements := match function.binding with
        | .body (.statements _ body _) => body
        | _ => #[]
      (function.params.map (·.name), #[], statements)
    | .relation relation =>
      (relation.statement.map (·.name) ++ (relation.witness.getD #[]).map (·.name), #[], #[])
    | _ => (#[], #[], #[])
  let env ← makeEnv (.declaration id) declaration.file declaration.namespace callee.scopes
  startLocals
  for port in ports do discard <| addLocal port.text port.span
  let loops := (loopScopes body (ports.map (·.text)) {}).2
  let head := match callee.node with | .protocol protocol => some protocol.head | _ => none
  return ⟨node.span, targetName, ← node.clauses.mapM (resolveClause env head results loops)⟩

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
partial def resolveGoalValue (env : Env) (argument : String) : GoalValue → ResolveM Lowered.GoalValue
  | .tuple sp items => do return .tuple sp (← items.mapM (resolveGoalValue env argument))
  | .path sp path args => do
    let ref ← match path.plainName? with
      | some name =>
        if argument == "clause" then pure (.reference (oneStep path.span (.label name.text)))
        else if argument == "corrupted" then pure (.reference (oneStep path.span (.role name.text)))
        else if wordArguments.contains argument || goalWords.contains name.text then
          pure (.reference (oneStep path.span (.word name.text)))
        else pathTerm env path
      | none => pathTerm env path
    return .path sp ref (← args.mapM (resolveCallArgs env .value))

def resolveGoal (env : Env) (node : Goal) : ResolveM Lowered.Goal := do
  let property ← pathTerm env node.property
  let scheme ← pathTerm env node.scheme
  let args ← node.args.mapM fun
    | .named sp name value => return GoalArgForm.named sp name (← resolveGoalValue env name.text value)
    | .spec sp name size => return .spec sp name (← resolveExprAt env .plain size)
  return ⟨node.span, node.pub, node.name, property, scheme, args, ← node.ceiling.mapM (resolveExpr env)⟩

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
  | .contract node => return (.contract (← resolveContract id declaration node), #[], #[])
  | .scheme node => return (.unlowered (← resolveScheme standard node), #[], #[])
  | .goal node => return (.goal (← resolveGoal standard node), #[], #[])
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
