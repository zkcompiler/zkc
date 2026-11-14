module

public import Zkc.Frontend.Static.Infer

@[expose] public section

set_option autoImplicit false

/-!
# Roots, default instances, and the checks of declarations

What is checked of a declaration of the package whatever its instances are: a `where` calls no
function and names no run-time value (SP4); the specification-only parameters stand last and occur in no
deployed type (SP11); a row of the vocabulary that a library under `zkc::` binds is in the
vocabulary, and a module bound to an asset has an interface of naturals and data (NL9); and, when
`zkc::algebra` is of the package, each type of the vocabulary has the members and meets the
conditions of each of its sorts (SP3, SP4).

The package is the given files; a library module that a path reaches is not of it. The roots are
every declaration of the package without static parameters, every comment
`// instantiate: m<args>` of the package and the protocol instance that each scheme of the package
names, with the suite of its `construction` line (SC5). A public declaration of the package with static
parameters that no root reaches is checked at its default instances (SP7): each natural at 0 to 3 and at the largest value that a
`where` bound admits, each type at `bool` or at the representative of its sort, each module at
the first implementing module of the program with its static arguments solved against the bound;
an instance whose `where` does not hold is skipped.
-/

namespace Zkc.Frontend.Instances

open Syntax
open Names (segmentsOf segmentArgs segmentName kindWord)
open Static
open Static.Infer (startProblem writtenTerms matchTerm retry parameterOf exprParameters)

/-- The calls of an expression, method calls included. -/
partial def callsOf : Expr → Array Expr
  | expr@(.call _ _ args) => #[expr] ++ argsCalls args
  | expr@(.method _ target _ _ args) => #[expr] ++ callsOf target ++ argsCalls args
  | .ifExpr _ a b c => callsOf a ++ callsOf b ++ callsOf c
  | .orExpr _ a b | .andExpr _ a b | .compare _ _ a b | .sum _ _ a b | .product _ _ a b
  | .power _ a b | .innerProduct _ _ a b | .index _ a b | .repetition _ a b => callsOf a ++ callsOf b
  | .notExpr _ a | .unary _ a | .paren _ a | .field _ a _ | .position _ a _ => callsOf a
  | .tuple _ components => components.foldl (init := #[]) fun acc (.component _ _ value) =>
      acc ++ callsOf value
  | .list _ elements => elements.foldl (init := #[]) fun acc element => acc ++ callsOf element
  | _ => #[]
where
  argsCalls : CallArgs → Array Expr
    | .callArgs _ arguments witnesses =>
      (arguments ++ witnesses.getD #[]).foldl (init := #[]) fun acc argument =>
        match argument with
        | .positional _ value | .named _ _ value | .spec _ _ value => acc ++ callsOf value

/-- The name of what a scope belongs to, for messages. -/
def scopeOwnerName (state : Compile.State) (scope : ScopeId) : String :=
  let program := state.program
  match state.scopeOwners[scope]? with
  | some owner => program.nameOf owner
  | none => match program.scopes[scope]? with
    | some entry => match program.namespaces[entry.namespace]? with
      | some ns => program.nameOf ns.owner
      | none => "?"
    | none => "?"

/-- SP4 and SP11 on every parameter scope. -/
def checkScopes : CompileM Unit := do
  let program ← program
  for scopeId in [0:program.scopes.size] do
    let scope := program.scopes[scopeId]!
    unless inPackage program scope.file do continue
    let owner := scopeOwnerName (← get) scopeId
    -- the specification-only parameters stand last (SP11)
    let mut seenSpec : Option StaticParam := none
    for parameter in scope.parameters do
      if parameter.spec then seenSpec := some parameter
      else if let some spec := seenSpec then
        logError "SP11" parameter.name.span
          (.ofText s!"the specification-only parameters stand last: write `<{parameter.name.text}: nat, spec {spec.name.text}: nat>`") (origin := .instances)
    let some whereClause := scope.whereClause | continue
    let env : Env := { file := scope.file }
    for constraint in whereClause.constraints do
      let sides := match constraint with
        | .bound _ subject _ => #[subject]
        | .compare _ _ left right => #[left, right]
      for side in sides do
        for call in callsOf side do
          let callee := match call with
            | .call _ callee _ => some callee
            | _ => none
          let isSize ← match callee with
            | some path => do
              let steps ← recover (stepsOf env path) (pure #[])
              pure (steps.any (·.step == .sizeOperator))
            | none => pure false
          unless isSize do
            logError "SP4" (Syntax.Expr.span call)
              (.ofText s!"the `where` of `{owner}` calls `{exprText call}`: a constraint is over static terms, and a call is not one") (origin := .instances)
        for path in exprPaths side do
          let steps ← recover (stepsOf env path) (pure #[])
          if let some { step := .«local», .. } := steps[0]? then
            logError "SP4" path.span
              (.ofText s!"`{exprText (.path path.span path)}` is a run-time value: a constraint of the `where` of `{owner}` is over static terms") (origin := .instances)

/-- Whether a declaration is deployed code: neither a specification item nor a member of an
interface (SX1). -/
def isDeployed (declaration : Declaration) : Bool :=
  match declaration.node with
  | .«def» node => match node.modifier with
    | some (.spec _) => false
    | _ => true
  | .protocol node => !node.spec
  | .struct _ | .enum _ | .staticName _ | .«module» _ | .oracleDef _ => true
  | .typeDecl (.type ..) => true
  | _ => false

/-- A specification-only parameter in a type of deployed code is refused (SP11 item 2). The
types are read in their lowered form. -/
def checkSpecificationTypes (declarationId : DeclarationId) : CompileM Unit := do
  let state ← get
  let declaration ← declaration declarationId
  unless isDeployed declaration do return
  let env : Env := { file := declaration.file }
  let some lowered := (← getModules).lowered? declarationId | return
  let mut types : Array (Lowered.TypeTerm × Option String) := #[]
  let mut sizes : Array Lowered.Expr := #[]
  match declaration.node, lowered.content with
  | .«def» _, .function head _ =>
    types := head.parameters.map (·.type, none)
    if let some result := head.result then types := types.push (result, none)
  | .protocol _, .protocol head _ _ =>
    for port in head.ports do
      unless port.specification do types := types.push (port.type, some port.binder.name)
    for result in head.results do types := types.push (result.type, some result.name.text)
  | .struct _, .record _ fields => types := fields.map fun (_, type) => (type, none)
  | .enum _, .«variant» alternatives =>
    types := alternatives.foldl (init := #[]) fun acc (_, payload) => acc ++ payload.map (·, none)
  | .typeDecl (.type _ _ _ _ (.type _)), .alias type => types := #[(type, none)]
  | .staticName _, .staticName value => sizes := #[value]
  | .oracleDef node, .unlowered names =>
    -- the lowered names of an oracle function start with the types of its parameters
    types := (names.extract 0 node.params.size).filterMap fun
      | .type type => some (type, none)
      | _ => none
  | _, _ => pure ()
  let check (reference : Lowered.Reference) (port : Option String) : CompileM Unit := do
    let .reference span _ := reference
    let some first := reference.firstParameter? | return
    let spec := ((state.program.scopes[first.scope]?).bind (·.parameters[first.index]?)).any (·.spec)
    if spec then
      let name ← sourceText env span
      match port with
      | some port =>
        refuse "SP11" span
          s!"`{name}` is a specification-only static parameter; it does not occur in the type of the port `{port}`"
      | none =>
        refuse "SP11" span
          s!"`{name}` is a specification-only static parameter; it does not occur in a type, a size or a static argument of deployed code"
  for (type, port) in types do
    for reference in type.references do recover (check reference port) (pure ())
  for size in sizes do
    for reference in size.references do recover (check reference none) (pure ())

/-- Each type of the vocabulary has the type and natural members of each of its sorts, and meets
the `where` of each (SP3, SP4). -/
def checkVocabulary : CompileM Unit := do
  let state ← get
  let program := state.program
  for entry in (← getVocabulary).types do
    for sortName in entry.sorts do
      let some (sort, _) := state.sortNames.toList.find? (·.2 == sortName) | continue
      let sortDeclaration ← declaration sort
      let type : ClosedType := .nominal entry.row #[]
      let rendered := renderType state type
      let frame : ChainFrame :=
        { subject := .ofText s!"the vocabulary type `{rendered}` of sort `{sortName}`"
          span := (sortDeclaration.name.map (·.span)).getD default }
      recover (fallback := pure ()) <| withChainFrame frame do
        for member in (state.members[sortDeclaration.inner.getD 0]?).getD #[] do
          let memberDeclaration ← declaration member
          let memberName := program.nameOf member
          let given := match memberDeclaration.kind with
            | .typeMember => entry.typeMembers.any (·.1 == memberName)
            | .naturalMember => entry.naturalMembers.any (·.1 == memberName)
            | _ => true
          unless given do
            logError "SP3" ((memberDeclaration.name.map (·.span)).getD default)
              (.ofText s!"`{rendered}` is of sort `{sortName}`, and the vocabulary gives it no `{memberName}`") (origin := .instances)
        let some whereClause := (sortDeclaration.ownScope.bind fun scope =>
          program.scopes[scope]?).bind (·.whereClause) | return
        let env : Env := { file := sortDeclaration.file, self? := some (.type type) }
        for constraint in whereClause.constraints do
          let outcome ← try checkWrittenConstraint env constraint rendered
            catch failure => match failure with
              | .waiting _ => pure none
              | other => throw other
          if let some message := outcome then
            logError "SP4" (writtenConstraintSpan constraint) (.ofText message) (origin := .instances)

/-- The kinds of declarations that have instances. -/
def hasInstances : DeclarationKind → Bool
  | .alias | .vocabularyType | .specType | .record | .«variant» | .function | .oracleFunction
  | .protocol | .relation | .staticName | .«module» | .law => true
  | _ => false

/-- Whether a declaration is a member of an interface. -/
def inInterface (program : Program) (declaration : Declaration) : Bool :=
  (program.namespaces[declaration.namespace]?).any fun ns =>
    (program.declarations[ns.owner]?).any (·.kind == .interface)

/-- The instance that a comment `// instantiate: m<args>` asks for. -/
def instantiateDirective (file : FileId) (term : Expr) : CompileM Unit := do
  let env : Env := { file }
  let .path span path := term
    | refuse "GR5" (Syntax.Expr.span term) s!"`{exprText term}` names no declaration to instantiate"
  match ← evalWrittenPath env path with
  | .declarations steps scopes =>
    let some (id, _) := steps.back? | throw .abandoned
    let values ← bindArguments env steps scopes span
    let inst ← instantiate id values { description := s!"instantiate: {exprText term}", span }
    addRoot inst .directive
  | _ => refuse "GR5" span s!"`{exprText term}` names no declaration to instantiate"

/-- The suite of the `construction` line of a scheme (SC5): a scheme has one `construction` line,
and the suite of `derived(S)` is a module that implements `zkc::construction::Suite`. A suite of
the catalogue gives its row; a suite in source, and the constructions `interactive` and
`authored`, are not constructed here: the reason is returned. -/
def schemeSuite (env : Env) (node : Syntax.Scheme) : CompileM (Except String String) := do
  let constructions : Array (Span × Syntax.Construction) := node.lines.filterMap fun
    | .construction span construction => some (span, construction)
    | _ => none
  if constructions.isEmpty then
    refuse "SC5" node.name.span s!"scheme `{node.name.text}` has no `construction` line: a scheme has one"
  if let some (span, _) := constructions[1]? then
    refuse "SC5" span s!"scheme `{node.name.text}` has a second `construction` line: a scheme has one"
  let notSuite (span : Span) : CompileM (Except String String) :=
    refuse "SC5" span "the suite of `derived` is a path to a module that implements `zkc::construction::Suite`; a catalogue suite is a module of `zkc::suites`"
  let first : Option (Span × Syntax.Construction) := constructions[0]?
  match first with
  | some (_, .derived _ path) =>
    -- a suite in source is not instantiated here: its bodies are typed when it is constructed
    let .declarations steps _ ← evalWrittenPath env path | notSuite path.span
    let some (id, _) := steps.back? | throw .abandoned
    let found ← declaration id
    match found.node with
    | .«module» (.«module» _ _ _ _ _ _ (.primitive primitive)) =>
      let .«module» inst ← evalWrittenAny env (.path path.span path) | notSuite path.span
      let state ← get
      let some { state := .done (.data (.«module» interfaces _)), .. } := state.table.entries[inst]?
        | return .error s!"the suite `{exprText (.path path.span path)}` is not evaluated"
      unless interfaces.any (fun (id, _) => qualifiedName state.program id == "zkc::construction::Suite") do
        let _ ← notSuite path.span
      return .ok primitive.row.content
    | .«module» _ =>
      return .error s!"the suite `{exprText (.path path.span path)}` is written in source; a suite in source is not constructed yet"
    | _ => notSuite path.span
  | some (_, .interactive _) => return .error "the construction is `interactive`; only `construction derived` with a suite of the catalogue is constructed"
  | some (_, .authored _) => return .error "the construction is `authored`; only `construction derived` with a suite of the catalogue is constructed"
  | none => throw .abandoned

/-- The first line of a scheme that the construction does not take, as a reason: `context`,
`commit`, `pin`, `grind`, `retry`, `samples`, `offline`, `ideal`, a `layout` line with entries
or of a layout other than `zkc::layout::canonical`. -/
def schemeWaits (env : Env) (node : Syntax.Scheme) : CompileM (Option String) := do
  for line in node.lines do
    match line with
    | .context .. => return some "its `context` line: a context in the statement is not constructed yet"
    | .commit .. => return some "its `commit` line: a commitment scheme is not constructed yet (layer D)"
    | .pin .. => return some "its `pin` line: a pinned send is not constructed yet"
    | .grind .. => return some "its `grind` line: grinding is not constructed yet"
    | .retry .. => return some "its `retry` line: attempts are not constructed yet"
    | .samples .. => return some "its `samples derived by` line: derived samples are not constructed yet"
    | .offline .. => return some "its `offline` line: an offline role is not constructed yet"
    | .ideal .. => return some "its `ideal` line: an ideal role is not constructed yet"
    | .layout _ _ (some _) =>
      return some "its `layout` line with `carry` or `recover`: carried and recovered sites are not constructed yet"
    | .layout _ path none =>
      -- the layout is named, not instantiated
      let text := exprText (.path path.span path)
      let some thing ← recover (some <$> evalWrittenPath env path) (pure none) (waits := true)
        | return some s!"its layout `{text}`, which is not resolved"
      let state ← get
      let name := match thing with
        | .declarations steps _ => steps.back?.map fun (id, _) => qualifiedName state.program id
        | _ => none
      unless name == some "zkc::layout::canonical" do
        return some s!"its layout `{text}`: only `zkc::layout::canonical` is constructed"
    | _ => pure ()
  return none

/-- The protocol instance that a scheme names: a root of the package; and the scheme, with the
suite of its `construction` line (`schemeSuite`) and the first line that waits (`schemeWaits`).
The construction reads the rest (`Zkc.Frontend.Semantics.Scheme`). -/
def schemeProtocol (file : FileId) (node : Syntax.Scheme) : CompileM Unit := do
  let env : Env := { file }
  let path := node.protocol
  match ← evalWrittenPath env path with
  | .declarations steps scopes =>
    let some (id, _) := steps.back? | throw .abandoned
    let values ← bindArguments env steps scopes path.span
    let text := exprText (.path path.span path)
    let inst ← instantiate id values { description := s!"scheme {node.name.text} = {text}", span := path.span }
    addRoot inst
    let suite ← schemeSuite env node
    let waits ← schemeWaits env node
    let scheme : SchemeEntry :=
      { name := node.name.text, span := node.span, protocol := inst, lines := node.lines, suite, waits }
    modifyResults fun results => { results with schemes := results.schemes.push scheme }
  | _ => pure ()

/-- The values of a sort's default representative (SP7), for a type parameter with this bound. -/
def defaultType (env : Env) (bound : Option Bound) : CompileM (Option ClosedType) := do
  let state ← get
  let some bound := bound | return some .bool
  let sorts ← (← boundInterfaces env bound).filterMapM fun (id, _) => pure (state.sortNames[id]?)
  if sorts.isEmpty then return some .bool
  let vocabulary ← getVocabulary
  for sort in sorts do
    let some row := vocabulary.representative? sort | continue
    if sorts.all fun other => hasSort vocabulary (.nominal row #[]) other then
      return some (.nominal row #[])
  return none

mutual
/-- The default value of a parameter alone: `bool` or a representative, 0, or the first module
of the program that implements its bound. -/
partial def defaultValue (env : Env) (reference : ParameterRef) (parameter : StaticParam) :
    CompileM (Option StaticValue) := do
  match ← parameterClass reference with
  | .natural => return some (.natural 0)
  | .type => return (← defaultType env parameter.bound).map StaticValue.type
  | .«module» => defaultModule env parameter.bound

/-- The first module of the program, the given files first, that names every interface of a
bound, with its static arguments solved against the bound (SP6) and the others at their
defaults. -/
partial def defaultModule (env : Env) (bound : Option Bound) : CompileM (Option StaticValue) := do
  let state ← get
  let program := state.program
  let some bound := bound | return none
  let mut required : Array (DeclarationId × Array StaticValue) := #[]
  for (_, path) in ← boundInterfaces env bound do
    required := required.push (← writtenInterface env path)
  let some (firstRequired, _) := required[0]? | return none
  for index in (state.implementers[firstRequired]?).getD #[] do
    let candidate := program.declarations[index]!
    let some candidateBound := Names.implementing? candidate | continue
    let candidateEnv : Env := { file := candidate.file }
    let named ← boundInterfaces candidateEnv candidateBound
    unless required.all (fun (id, _) => named.any (·.1 == id)) do continue
    let mut problem ← startProblem index {}
    let context : Static.Infer.Context := .context candidate.file []
    for (id, values) in required do
      let some (_, path) := named.find? (·.1 == id) | continue
      let some resolution := state.resolutions.find? candidate.file path | continue
      let some last := resolution.segments.back? | continue
      let interfaceDeclaration ← declaration id
      let written ← writtenTerms id last.staticArgs (fun _ => false)
      let parameters := deployedParameters program interfaceDeclaration
      for ((reference, _), value) in parameters.zip values do
        if let some (_, term) := written.find? (·.1 == reference) then
          problem ← matchTerm problem context term value
    problem ← retry problem
    let mut values := #[]
    let mut complete := true
    for (reference, parameter) in deployedParameters program candidate do
      match problem.known[reference]? with
      | some value => values := values.push value
      | none =>
        if (← parameterClass reference) == .«module» then complete := false
        else match ← defaultValue candidateEnv reference parameter with
          | some value => values := values.push value
          | none => complete := false
    unless complete do continue
    let found ← recover (waits := true) (fallback := pure none) do
      let inst ← instantiate index values
        { description := "", span := (candidate.name.map (·.span)).getD default }
      let mut meets := true
      for (id, args) in required do
        unless ← implements inst id args do meets := false
      return if meets then some (StaticValue.«module» inst) else none
    if let some value := found then return some value
  return none
end

/-- The largest value that a `where` of a declaration's scopes admits for a natural parameter,
by a bound without natural parameters. -/
def largestBound (env : Env) (declaration : Declaration) (reference : ParameterRef) :
    CompileM (Option Nat) := do
  let modules ← getModules
  let mut result : Option Nat := none
  for scope in declaration.scopes do
    let some lowered := modules.loweredScope? scope | continue
    for constraint in lowered.constraints do
      let .compare _ operator left right := constraint | continue
      let (term, strict) := match parameterOf left, parameterOf right, operator with
        | some l, _, .lessEqual => if l == reference then (some right, false) else (none, false)
        | some l, _, .less => if l == reference then (some right, true) else (none, false)
        | _, some r, .greaterEqual => if r == reference then (some left, false) else (none, false)
        | _, some r, .greater => if r == reference then (some left, true) else (none, false)
        | _, _, _ => (none, false)
      let some term := term | continue
      -- a term without natural parameters
      let mut natural := false
      for other in exprParameters term do
        if (← parameterClass other) == .natural then natural := true
      if natural then continue
      let value ← recover (some <$> evalSize env term) (pure none) (waits := true)
      if let some value := value then
        let admitted := if strict then (if value == 0 then none else some (value - 1)) else some value
        if let some admitted := admitted then
          result := some (match result with
            | some earlier => min earlier admitted
            | none => admitted)
  return result

/-- The combinations of natural values of SP7: all of them for up to three naturals; beyond,
the four with all equal at 0 to 3, and each natural at each of its other values with the others
at 1. -/
def combinations (choices : Array (Array Nat)) : Array (Array Nat) := Id.run do
  if choices.size <= 3 then
    let mut result : Array (Array Nat) := #[#[]]
    for options in choices do
      result := result.foldl (init := #[]) fun acc start =>
        acc ++ options.map (start.push ·)
    return result
  let mut result : Array (Array Nat) := #[]
  for value in [0, 1, 2, 3] do result := result.push (Array.replicate choices.size value)
  for index in [0:choices.size] do
    for value in choices[index]! do
      if value == 1 then continue
      let combination := (Array.replicate choices.size 1).set! index value
      unless result.contains combination do result := result.push combination
  return result

/-- Whether a declaration is a specification item that reads specification-only parameters as
static naturals: a `spec def`, a relation, a law (SP11). -/
def readsSpecification (declaration : Declaration) : Bool :=
  match declaration.node with
  | .«def» node => (node.modifier matches some (.spec _))
  | .relation _ | .law _ => true
  | _ => false

/-- The values of the specification-only parameters of a specification item typed without a
goal: 0, 1, 2 and 3, combined as the naturals of SP7 are (SP11). A deployed declaration and an
item without such parameters have one, empty. -/
def specificationChoices (program : Program) (declaration : Declaration) : Array (Array Nat) :=
  let parameters := specificationParameters program declaration
  if parameters.isEmpty || !readsSpecification declaration then #[#[]]
  else combinations (parameters.map fun _ => #[0, 1, 2, 3])

/-- The default values of a declaration's static parameters that `fixed` does not give (SP7), in
the order of its parameters, or why it has none: each type parameter at the representative of its
bound, each natural at 0 to 3 and at the largest value a `where` admits, combined, and each module
parameter at the first module that implements its bound. -/
def defaultCombinations (declarationId : DeclarationId) (fixed : StaticEnvironment := {}) :
    CompileM (Except String (Array (Array StaticValue))) := do
  let program ← program
  let declaration ← declaration declarationId
  let name := program.nameOf declarationId
  let parameters := deployedParameters program declaration
  let env0 : Env := { file := declaration.file, values := fixed }
  -- types
  let mut typeValues : Std.HashMap ParameterRef StaticValue := fixed
  for (reference, parameter) in parameters do
    if fixed.contains reference then continue
    if (← parameterClass reference) == .type then
      match ← defaultType env0 parameter.bound with
      | some type => typeValues := typeValues.insert reference (.type type)
      | none => return .error s!"no type of the vocabulary has every sort of `{parameter.name.text}`"
  -- naturals
  let typeEnv : Env := { env0 with values := typeValues }
  let mut naturals : Array ParameterRef := #[]
  let mut choices : Array (Array Nat) := #[]
  for (reference, _) in parameters do
    if fixed.contains reference then continue
    if (← parameterClass reference) == .natural then
      let mut options := #[0, 1, 2, 3]
      if let some largest ← largestBound typeEnv declaration reference then
        unless options.contains largest do options := options.push largest
      naturals := naturals.push reference
      choices := choices.push options
  let mut result := #[]
  for combination in combinations choices do
    let mut values := typeValues
    for (reference, value) in naturals.zip combination do values := values.insert reference (.natural value)
    -- modules, in order, at the values so far
    for (reference, parameter) in parameters do
      if fixed.contains reference then continue
      if (← parameterClass reference) == .«module» then
        let moduleValue ← recover (defaultModule { env0 with values } parameter.bound) (pure none)
          (waits := true)
        match moduleValue with
        | some value => values := values.insert reference value
        | none => return .error s!"no module of the program implements the bound of a module parameter of `{name}`"
    result := result.push (parameters.map fun (reference, _) => values.getD reference default)
  return .ok result

/-- The default instances of a public declaration that no root reaches (SP7), as many as the
budget allows: past it, the check of the declaration is incomplete and refuses nothing. -/
def defaultInstances (declarationId : DeclarationId) : CompileM Unit := do
  let program ← program
  let declaration ← declaration declarationId
  let limit := (← read).options.budgets.defaultInstances
  let place := (declaration.name.map (·.span)).getD default
  let noDefault (reason : String) : CompileM Unit := do
    let entry : DefaultReport := { declaration := declarationId, count := 0, first := none, none? := some reason }
    modifyResults fun results => { results with defaults := results.defaults.push entry }
  let combinationsOrReason ← defaultCombinations declarationId
  let .ok valueCombinations := combinationsOrReason
    | match combinationsOrReason with
      | .error reason => noDefault reason
      | .ok _ => pure ()
  let mut count := 0
  let mut first : Option String := none
  for ordered in valueCombinations do
    for specification in specificationChoices program declaration do
      if count == limit then
        modifyResults fun results => { results with
          defaults := results.defaults.push { declaration := declarationId, count, first } }
        let exhaustion ← logExhaustion .defaultInstances
          { subject := .ofText (program.nameOf declarationId), span := place }
        throw (.exhausted exhaustion)
      let description ← describeInstance declarationId ordered specification
      try
        let inst ← instantiate declarationId ordered { description, span := place } (isDefault := true)
          specification
        addRoot inst .defaultInstance
        count := count + 1
        if first.isNone then first := some description
      catch failure =>
        match failure with
        | .skipped => pure ()
        | .waiting _ | .staticIndex _ | .exhausted _ => count := count + 1
        | .abandoned =>
          count := count + 1
          if first.isNone then first := some description
        | .defect _ => throw failure
  let entry : DefaultReport := { declaration := declarationId, count, first }
  modifyResults fun results => { results with defaults := results.defaults.push entry }

/-- The instances of a law at which it is typed (SP10): its scope's values fixed, as the module
instance gives them; its own static parameters at their default values (SP7); `Self` the module
instance, for a law of an interface. A law whose `where` does not hold at an instance is not typed
there. The instances are roots. -/
def lawInstances (lawId : DeclarationId) (fixed : StaticEnvironment) (owner : Option InstanceId) :
    CompileM Unit := do
  let program ← program
  let law ← declaration lawId
  let .ok valueCombinations ← defaultCombinations lawId fixed | return
  for ordered in valueCombinations do
    for specification in specificationChoices program law do
      let description ← describeInstance lawId ordered specification owner
      try
        let inst ← instantiate lawId ordered
          { description, span := (law.name.map (·.span)).getD default } (isDefault := true)
          specification owner
        unless (← get).roots.contains inst do addRoot inst .defaultInstance
      catch failure =>
        match failure with
        | .skipped | .waiting _ | .staticIndex _ | .abandoned | .exhausted _ => pure ()
        | .defect _ => throw failure

/-- The laws typed at a module instance (SP7 item 7, SP10): every law of the interfaces it
implements, with `Self` the instance, and every law of its own, at its values. -/
def moduleLaws (inst : InstanceId) : CompileM Unit := do
  let state ← get
  let program := state.program
  let some entry := state.table.entries[inst]? | return
  let some (.«module» interfaces _) := state.table.content? inst | return
  let some found := program.declarations[entry.key.declaration]? | return
  let lawsOf (namespaceId : Option NamespaceId) (kind : DeclarationKind) : Array DeclarationId :=
    match namespaceId.bind (state.members[·]?) with
    | some members => members.filter fun id => (program.declarations[id]?).any (·.kind == kind)
    | none => #[]
  for (interface, args) in interfaces do
    let some interfaceDeclaration := program.declarations[interface]? | continue
    let fixed : StaticEnvironment := ((deployedParameters program interfaceDeclaration).zip args).foldl
      (init := {}) fun map ((reference, _), value) => map.insert reference value
    for law in lawsOf interfaceDeclaration.inner .lawMember do
      endItem (lawInstances law fixed (some inst))
  let fixed : StaticEnvironment := ((deployedParameters program found).zip entry.key.arguments).foldl
    (init := {}) fun map ((reference, _), value) => map.insert reference value
  for law in lawsOf found.inner .law do
    endItem (lawInstances law fixed none)

/-- The function members of a module instance, instantiated whether or not anything calls them
(SP7 item 7): a member with static parameters of its own at their default values where the
member's `where` holds. -/
def typeModuleMembers (inst : InstanceId) : CompileM Unit := do
  let state ← get
  let program := state.program
  let some entry := state.table.entries[inst]? | return
  let some (.«module» interfaces members) := state.table.content? inst | return
  for (name, value) in members do
    let .definition definition := value | continue
    let some found := program.declarations[definition]? | continue
    unless found.kind == .functionDefinition do continue
    -- the member that an interface declares, and the values of its own static parameters
    let declared := interfaces.findSome? fun (interface, args) => do
      let inner ← (program.declarations[interface]?).bind (·.inner)
      let .declaration member ← (program.namespaces[inner]?).bind (·.names[name]?) | none
      return (interface, member, args)
    let some (interface, member, args) := declared | continue
    let some interfaceDeclaration := program.declarations[interface]? | continue
    let some memberDeclaration := program.declarations[member]? | continue
    let interfaceParameters := deployedParameters program interfaceDeclaration
    let fixed : StaticEnvironment := (interfaceParameters.zip args).foldl (init := {})
      fun map ((reference, _), value) => map.insert reference value
    let ownValues : Array (Array StaticValue) ←
      if (ownParameters program memberDeclaration).isEmpty then pure #[#[]]
      else match ← defaultCombinations member fixed with
        | .ok combinations => pure (combinations.map (·.extract interfaceParameters.size))
        | .error _ => pure #[]
    for own in ownValues do
      -- a default value at which the member's `where` does not hold is skipped (SP7)
      let env : Env :=
        { instanceEnv program memberDeclaration (args ++ own) with self? := some (.«module» inst) }
      let holds ← recover (skipped := true) (waits := true) (fallback := pure false) do
        checkWheres env memberDeclaration name true (fun _ => pure false)
        pure true
      if holds then
        endItem do
          discard <| instantiate definition (entry.key.arguments ++ own)
            { description := name, span := (found.name.map (·.span)).getD default }

/-! ## The opaque typing (SP12) -/

/-- The interfaces that a bound names, with those that their `where` requires of `Self`. -/
partial def requiredInterfaces (env : Env) (bound : Bound) : CompileM (Array DeclarationId) := do
  let program ← program
  let mut result : Array DeclarationId := #[]
  let mut pending := (← boundInterfaces env bound).map (·.1)
  while !pending.isEmpty do
    let id := pending.back!
    pending := pending.pop
    if result.contains id then continue
    result := result.push id
    let some found := program.declarations[id]? | continue
    let some whereClause := (found.ownScope.bind fun scope => program.scopes[scope]?).bind (·.whereClause)
      | continue
    for constraint in whereClause.constraints do
      if let .bound _ (.path _ subject) required := constraint then
        let steps ← recover (stepsOf { file := found.file } subject) (pure #[])
        let kinds : List Step := (steps.map (·.step)).toList
        if kinds matches [Step.self _] then
          for (other, _) in ← boundInterfaces { file := found.file } required do
            pending := pending.push other
  return result

/-- The sorts of a bound, with those that a sort's `where` requires of `Self` (SP12 item 1). -/
def boundSorts (env : Env) (bound : Bound) : CompileM (Array String) := do
  let state ← get
  return (← requiredInterfaces env bound).filterMap (state.sortNames[·]?)

/-- The module instance that a module parameter stands for in the opaque typing (SP12): the
module it stands for at the instance, with the interfaces that the parameter's bound requires,
and each type member of them that `equated` does not name a fresh type, with the sorts of the
bound that the interface writes on it. It is no root and has no package. -/
def opaqueModule (reference : ParameterRef) (equated : Array String) (real : InstanceId) :
    CompileM InstanceId := do
  let state ← get
  let program := state.program
  let some entry := state.table.entries[real]? | throw .abandoned
  let key : InstanceKey := { entry.key with opaqueFor := some (reference, equated), owner := none }
  if let some existing := state.table.find? key then return existing
  let some (.«module» interfaces members) := state.table.content? real
    | throw (.waiting "a module whose members are not evaluated")
  let some scope := program.scopes[reference.scope]? | throw .abandoned
  let some parameter := scope.parameters[reference.index]? | throw .abandoned
  let required ← match parameter.bound with
    | some bound => requiredInterfaces { file := scope.file } bound
    | none => pure #[]
  let kept := interfaces.filter fun (id, _) => required.contains id
  let inst ← modifyGetResults fun results =>
    let table := results.signatures
    let results := { results with signatures := {} }
    let (table, inst, _) := table.intern key { subject := .ofText "", span := default } none
    (inst, { results with signatures := table })
  -- the type members of the interfaces kept, with the sorts of their bounds
  let mut typeMembers : Array (String × Array String) := #[]
  for (interface, _) in kept do
    let some inner := (program.declarations[interface]?).bind (·.inner) | continue
    for member in ((← get).members[inner]?).getD #[] do
      let some found := program.declarations[member]? | continue
      let .member (.typeMember _ name _ bound) := found.node | continue
      let sorts ← match bound with
        | some bound => boundSorts { file := found.file } bound
        | none => pure #[]
      typeMembers := typeMembers.push (name.text, sorts)
  let opaqueMembers := members.map fun (name, value) =>
    match (typeMembers.find? (·.1 == name)).map (·.2) with
    | some sorts =>
      if equated.contains name then (name, value)
      else match value with
        | .type _ => (name, .type (.opaque inst name #[] sorts))
        | .definition _ => (name, .opaqueType sorts)
        | other => (name, other)
    | none => (name, value)
  modifyResults (·.modifySignatures (·.setState inst (.done (.data (.«module» kept opaqueMembers)))))
  return inst

/-- The checks of declarations, the roots, and the instances that comments ask for. -/
def checkProgram (instantiations : Array (FileId × Expr)) : CompileM Unit := do
  let program ← program
  let own (declaration : Declaration) : Bool := inPackage program declaration.file
  checkScopes
  for id in [0:program.declarations.size] do
    unless own program.declarations[id]! do continue
    endItem (checkSpecificationTypes id)
    endItem (checkBindings id)
  if let some algebra := program.modules["zkc::algebra"]? then
    if (program.declarations[algebra]?).any own then endItem checkVocabulary
  for id in [0:program.declarations.size] do
    let declaration := program.declarations[id]!
    unless own declaration && hasInstances declaration.kind && !inInterface program declaration do
      continue
    unless (deployedParameters program declaration).isEmpty do continue
    for specification in specificationChoices program declaration do
      endItem do
        let inst ← instantiate id #[]
          { description := ← describeInstance id #[] specification
            span := (declaration.name.map (·.span)).getD default } (specification := specification)
        addRoot inst
  for (file, term) in instantiations do
    if inPackage program file then endItem (instantiateDirective file term)
  for id in [0:program.declarations.size] do
    let declaration := program.declarations[id]!
    if let .scheme node := declaration.node then
      if own declaration then endItem (schemeProtocol declaration.file node)

/-- The default instances of the public declarations that no root reaches (SP7). A root reaches
a declaration through signatures and through bodies, so this runs after the bodies of what the
roots reach are typed: a declaration that only a body reaches is reached, and has no default
instance. -/
def defaultProgram : CompileM Unit := do
  let program ← program
  let own (declaration : Declaration) : Bool := inPackage program declaration.file
  let reached : Std.HashSet DeclarationId :=
    (← get).table.entries.foldl (init := {}) fun set entry => set.insert entry.key.declaration
  for id in [0:program.declarations.size] do
    let declaration := program.declarations[id]!
    unless own declaration && declaration.pub && hasInstances declaration.kind &&
        !inInterface program declaration do
      continue
    if (deployedParameters program declaration).isEmpty || reached.contains id then continue
    endItem (defaultInstances id)

end Zkc.Frontend.Instances
