module

public import Zkc.Frontend.Static.Basic

@[expose] public section

set_option autoImplicit false

/-!
# Static values and instances

A static term is evaluated in a static environment, which gives a value to every parameter of
the chain of an instance (§5 of the reference's rules SP7, TY2, TY3): as a type, a natural or a
module, by the parameter it is bound to (GR5). A size is evaluated in the naturals, bottom up,
with the conditions of TY2. A type expression is evaluated to a closed type: an alias to its
definition, a record or a variant to the number of its instance, a type of the vocabulary to its
row and static arguments. A member of a static thing at an instance is read from the vocabulary
for a type of a sort (a sized collection of elements of a `Group` is a `Group`, TY11), and from
the member table of the module instance for a module.

An instantiation (SP7) interns the key of the declaration at its values. A request for a key in
progress is a declaration that reaches itself (NL1). A type or a module bound to the vocabulary or
to an asset is checked as NL9 states when it is instantiated, whichever module declares it. An instance checks the bounds of its
parameters, outermost scope first (SP3), evaluates every `where` in order (SP4), and evaluates the
types of its signature, fields or payloads (TY2). An implementing module also defines the
members of the interfaces it names, in the forms of SP8, and meets the `where` of each of them;
its member table is built from its definitions, or from the vocabulary's row when it is bound to
the vocabulary. Bodies are not looked at here.

Every term is read in its lowered form: the terms of a signature and of a scope from the lowered
declarations and scopes of the store of files, and a term that typing reads from the syntax is
lowered apart first (`evalWrittenType` and its neighbours). A local name in a term is a static
name or an index of the environment, by the name the source writes at its place.

Entry points for the typing of bodies: `instantiate`, `bindArguments`, `evalType`, `evalTerm`,
`evalSize`, `memberOfValue`, and their forms over the syntax.
-/

namespace Zkc.Frontend.Static

open Syntax
open Names (segmentsOf segmentArgs segmentName kindWord)

/-- What the steps of a path stand for so far. -/
inductive Thing where
  | value (value : StaticValue)
  /-- The declarations passed through, each with the static arguments written on its segment;
  the last is the one the path names. `scopes` holds the values that the path gives scopes of
  its chain without writing them: a member of a module instance has the instance's values. -/
  | declarations (steps : Array (DeclarationId × Option (Array Lowered.StaticArgument)))
      (scopes : Std.HashMap ScopeId (Array StaticValue))
  /-- A local name: a run-time value. -/
  | runtime (name : String)
  /-- Something that is no static thing: a function, an alternative. -/
  | other (what : String)
  deriving Inhabited

/-- The values of an instance, by the scopes of the declaration's chain. -/
def valuesByScope (program : Program) (declaration : Declaration) (values : Array StaticValue) :
    Std.HashMap ScopeId (Array StaticValue) := Id.run do
  let mut result : Std.HashMap ScopeId (Array StaticValue) := {}
  let mut index := 0
  for (reference, _) in deployedParameters program declaration do
    let value := values[index]?.getD default
    result := result.insert reference.scope ((result.getD reference.scope #[]).push value)
    index := index + 1
  return result

/-- The environment of an instance: its values, and the values of its specification-only
parameters, which a specification item reads as static naturals (SP11). -/
def instanceEnv (program : Program) (declaration : Declaration) (values : Array StaticValue)
    (specification : Array Nat := #[]) : Env :=
  let parameters := deployedParameters program declaration
  let deployed := (parameters.zip values).foldl (init := {}) fun map ((reference, _), value) =>
    map.insert reference value
  { file := declaration.file
    values := ((specificationParameters program declaration).zip specification).foldl
      (init := deployed) fun map ((reference, _), value) => map.insert reference (.natural value) }

/-- Whether a static term names a specification-only parameter. -/
def mentionsSpecParameter (term : Lowered.Expr) : CompileM Bool := do
  let state ← get
  for (.reference _ segments) in term.references do
    for (.segment step _ _) in segments do
      if let .parameter reference := step then
        let spec := ((state.program.scopes[reference.scope]?).bind
          (·.parameters[reference.index]?)).any (·.spec)
        if spec then return true
  return false

/-- The source text at a place of the file of an environment: what a message quotes, and the
name of a local name. -/
def sourceText (env : Env) (place : Span) : CompileM String := do
  let some record := (← getModules).records[env.file]? | return "?"
  let bytes := record.source.tree.source
  if place.stopByte.toNat ≤ bytes.size && place.startByte ≤ place.stopByte then
    return (String.fromUTF8? (bytes.extract place.startByte.toNat place.stopByte.toNat)).getD "?"
  return "?"

def constraintSpan : Lowered.Constraint → Span
  | .bound span .. | .compare span .. => span

def writtenConstraintSpan : Constraint → Span
  | .bound span .. | .compare span .. => span

def sortSpan : Lowered.SortTerm → Span
  | .nat span | .linear span | .reference (.reference span _) => span

def compareText : Operator → String
  | .equal => " == " | .notEqual => " != " | .less => " < " | .lessEqual => " <= "
  | .greater => " > " | .greaterEqual => " >= " | _ => " ? "

/-- What a local name stands for: a static name, the index of a loop typed per iteration, or a
run-time value. -/
def localThing (env : Env) (place : Span) : CompileM Thing := do
  let name ← sourceText env place
  if let some value := env.locals[name]? then return .value (.natural value)
  if env.indices.contains name then throw (.staticIndex name)
  return .runtime name

/-- A term read as a type (GR5): types, `[T; n]`, `[T]`, tuples, paths and local names. -/
partial def asType : Lowered.Expr → Option Lowered.TypeTerm
  | .reference reference => some (.reference reference)
  | .local span binder => some (.local span binder)
  | .type type => some type
  | .repetition span element count => do return .sequence span (← asType element) (some count)
  | .list span #[element] => do return .sequence span (← asType element) none
  | .tuple span components names => do return .tuple span (← components.mapM asType) names
  | .error span => some (.error span)
  | _ => none

/-! ## Lowering what is read from the syntax -/

/-- Lowers what a later phase reads from the syntax, from the tables of resolutions. -/
def lowerWritten {α : Type} (action : Names.Written.WrittenM α) : CompileM α := do
  let modules ← getModules
  return Names.Written.lowerApart modules.program modules.tables action

/-- The steps of a path as typing reads them, with their static arguments lowered. -/
def lowerSteps (env : Env) (steps : Array (DeclarationId × Option StaticArgs)) :
    CompileM (Array (DeclarationId × Option (Array Lowered.StaticArgument))) :=
  lowerWritten (steps.mapM fun (id, args) => do
    return (id, ← args.mapM (Names.Written.staticArguments env.file)))


/-- The members of the interfaces of a module instance, or nothing when it has none yet. -/
def moduleMembers (inst : InstanceId) : CompileM (Option (Array (String × MemberValue))) := do
  match (← get).table.content? inst with
  | some (.«module» _ members) => return some members
  | _ => return none

/-- Whether a type is linear: a linear record, or a collection, a tuple or a variant with a
linear component (LN1). -/
partial def isLinear (state : Compile.State) : ClosedType → Bool
  | .record id => match state.table.content? id with
    | some (.record linear fields) => linear || fields.any (isLinear state ·.2)
    | _ => false
  | .variant id => match state.table.content? id with
    | some (.«variant» alternatives) => alternatives.any fun (_, payload) => payload.any (isLinear state)
    | _ => false
  | .seq element _ => isLinear state element
  | .tuple components _ => components.any (isLinear state)
  | _ => false

/-- A row of the vocabulary bound by a library under `zkc::` is in the vocabulary; a row of a
project is reported, and a module bound to an asset has an interface of naturals and of data
without parameters (NL9). -/
def checkBindings (declarationId : DeclarationId) : CompileM Unit := do
  let state ← get
  let program := state.program
  let declaration ← declaration declarationId
  let some file := program.files[declaration.file]? | return
  let library := (file.path[0]?) == some "zkc"
  let name := program.nameOf declarationId
  let unknownRow (row : StringLiteral) (what : String) : CompileM Unit := do
    if library then refuse "NL9" row.span s!"`{row.content}` is not a row of the vocabulary"
    else report s!"{file.name}: `{name}` is bound to `{row.content}`, which is not a {what} of the vocabulary: its signature is taken as written"
  match declaration.node with
  | .typeDecl (.type _ _ _ _ (.primitive primitive)) =>
    if ((← getVocabulary).type? primitive.row.content).isNone then unknownRow primitive.row "type"
  | .«module» (.«module» _ _ moduleName _ (some bound) _ body) =>
    match body with
    | .primitive primitive =>
      if ((← getVocabulary).module? primitive.row.content).isNone then unknownRow primitive.row "module"
    | .asset _ =>
      for (interface, _) in ← boundInterfaces { file := declaration.file } bound do
        let interfaceDeclaration ← Static.declaration interface
        let interfaceName := program.nameOf interface
        for member in (state.members[interfaceDeclaration.inner.getD 0]?).getD #[] do
          let memberDeclaration ← Static.declaration member
          let memberName := program.nameOf member
          let gives := "an asset gives naturals and data"
          match memberDeclaration.node with
          | .member (.typeMember ..) =>
            logError "NL9" moduleName.span
              (.ofText s!"`{name}` is bound to an asset, and its interface `{interfaceName}` has the type member `{memberName}`: {gives}") (origin := .instances)
          | .member (.defMember _ _ _ _ params _ _) =>
            unless params.isEmpty do
              logError "NL9" moduleName.span
                (.ofText s!"`{name}` is bound to an asset, and its interface `{interfaceName}` has the function `{memberName}` with a parameter: {gives}") (origin := .instances)
          | .member (.lawMember _) =>
            logError "NL9" moduleName.span
              (.ofText s!"`{name}` is bound to an asset, and its interface `{interfaceName}` has the law `{memberName}`: {gives}") (origin := .instances)
          | _ => pure ()
    | .suite _ => pure ()
  | _ => pure ()

/-- The exponent of a power of two. -/
def powerOfTwo (value : Nat) : Option Nat := Id.run do
  if value == 0 then return none
  let mut current := value
  let mut exponent := 0
  while current % 2 == 0 do
    current := current / 2
    exponent := exponent + 1
  return if current == 1 then some exponent else none

mutual
  /-- What a reference stands for, step by step. -/
  partial def evalReference (env : Env) (reference : Lowered.Reference) : CompileM Thing := do
    let .reference place segments := reference
    if segments.isEmpty then throw .abandoned
    evalSegments env segments place

  /-- What the steps of a path stand for; `place` is the place of the path. A local name is a
  static natural when the environment has it as a static name. -/
  partial def evalSegments (env : Env) (segments : Array Lowered.Segment) (place : Span) :
      CompileM Thing := do
    let mut thing : Thing := .declarations #[] {}
    for segment in segments do
      let .segment step arguments _ := segment
      match step with
      | .«local» => return ← localThing env place
      | .parameter reference =>
        match env.values[reference]? with
        | some value => thing := .value value
        | none =>
          let state ← get
          let spec := ((state.program.scopes[reference.scope]?).bind
            (·.parameters[reference.index]?)).any (·.spec)
          throw (.waiting (if spec then "a specification-only parameter"
            else "a parameter outside the instance"))
      | .self _ =>
        match env.self? with
        | some value => thing := .value value
        | none => throw (.waiting "`Self` outside an instance")
      | .declaration id =>
        match thing with
        | .declarations previous scopes =>
          thing := .declarations (previous.push (id, arguments)) scopes
        | _ => throw (.waiting "a declaration reached through a value")
      | .member name _ => thing ← memberOfThing env thing name arguments place
      | .generated name => throw (.waiting s!"the generated member `{name}`")
      | .alternative .. => thing := .other "an alternative"
      | .fixed _ | .sizeOperator => thing := .other "a function"
      | .vocabularyModule _ | .entry .. | .role _ | .word _ | .label _ | .bareAlternative _ =>
        thing := .other "no static thing"
    return thing

  /-- A member of what a path stands for so far. -/
  partial def memberOfThing (env : Env) (thing : Thing) (name : String)
      (args : Option (Array Lowered.StaticArgument)) (place : Span) : CompileM Thing := do
    match thing with
    | .value value => memberOfValue env value name args place
    | .declarations steps _ =>
      if steps.isEmpty then throw .abandoned
      let value ← thingValue env thing none place (nameOf steps.back!.1)
      memberOfValue env value name args place
    | .runtime localName => refuse "TY2" place s!"`{localName}` is a run-time value; it has no member `{name}`"
    | .other what => refuse "GR5" place s!"`{name}` is reached through {what}"

  /-- A member of a static thing at an instance: of a type, from the vocabulary and from TY11;
  of a module instance, from its member table. -/
  partial def memberOfValue (env : Env) (value : StaticValue) (name : String)
      (args : Option (Array Lowered.StaticArgument)) (place : Span) : CompileM Thing := do
    let state ← get
    match value with
    | .«module» inst =>
      let some members ← moduleMembers inst
        | throw (.waiting "a member of a module whose members are being formed")
      let found : Option MemberValue := (members.find? (·.1 == name)).map (·.2)
      match found with
      | some (.type type) => return .value (.type type)
      | some (.natural number) => return .value (.natural number)
      | some (.«module» other) => return .value (.«module» other)
      | some (.definition id) =>
        let entry := state.table.entries[inst]!
        let owner ← declaration entry.key.declaration
        return .declarations #[(id, args)] (valuesByScope state.program owner entry.key.arguments)
      | some (.row _) => return .other "a function"
      | some (.opaqueType sorts) =>
        -- an application of a type member that is opaque (SP12): a fresh type per arguments
        let mut values := #[]
        for arg in args.getD #[] do
          if let .term _ _ term := arg then values := values.push (← evalAny env term)
        return .value (.type (.opaque inst name values sorts))
      | none =>
        -- a module bound to the vocabulary or to an asset has the members that its row or its
        -- asset gives: one that they do not give is not known here
        let entry := state.table.entries[inst]!
        if let some owner := state.program.declarations[entry.key.declaration]? then
          if Names.hasNoBody owner then
            throw (.waiting s!"the member `{name}` of a module bound to the vocabulary or to an asset")
        refuse "SP3" place s!"`{renderInstance state inst}` has no member `{name}`"
    | .type type =>
      match type with
      | .nominal row _ =>
        match (← getVocabulary).type? row with
        | some entry =>
          if let some (_, member) := entry.typeMembers.find? (·.1 == name) then
            return .value (.type member)
          if let some (_, number) := entry.naturalMembers.find? (·.1 == name) then
            return .value (.natural number)
          if ← isSortFunction entry.sorts name then return .other "a function"
          refuse "SP3" place
            s!"`{renderType state type}` has no member `{name}`; its sorts are {", ".intercalate entry.sorts.toList}"
        | none =>
          refuse "SP3" place s!"`{renderType state type}` has no member `{name}`; it has no sort"
      | .seq element (some size) =>
        if hasSort (← getVocabulary) element "Group" then
          if name == "Scalar" then return ← memberOfValue env (.type element) name args place
          if name == "Order" then
            match ← memberOfValue env (.type element) name args place with
            | .value (.natural order) =>
              -- the order of a collection of group elements is the element's order to the
              -- power of its size, within the budget of static evaluation
              return .value (.natural (← withStaticEvaluation
                (staticPower place (pure s!"{renderType state type}::Order") order size (written := false))))
            | other => return other
          if ← isSortFunction #["Group"] name then return .other "a function"
          refuse "SP3" place
            s!"`{renderType state type}` has no member `{name}`; its sorts are Group"
        refuse "SP3" place s!"`{renderType state type}` has no member `{name}`; it has no sort"
      | .«opaque» .. =>
        throw (.waiting "a type member of a type member of a module parameter, in the opaque typing (SP12)")
      | _ => refuse "SP3" place s!"`{renderType state type}` has no member `{name}`; it has no sort"
    | .natural number => refuse "SP3" place s!"`{number}` is a natural; it has no member `{name}`"

  /-- Whether a name is a function member of one of these sorts. -/
  partial def isSortFunction (sorts : Array String) (name : String) : CompileM Bool := do
    let state ← get
    for (id, sort) in state.sortNames.toList do
      unless sorts.contains sort do continue
      let some inner := (state.program.declarations[id]?).bind (·.inner) | continue
      if let some (.declaration member) := (state.program.namespaces[inner]?).bind (·.names[name]?) then
        if (state.program.declarations[member]?).any (·.kind == .functionMember) then return true
    return false

  /-- The value of what a path stands for, of the class expected when one is. `text` is what a
  message calls it. -/
  partial def thingValue (env : Env) (thing : Thing) (expected : Option Class) (place : Span)
      (text : CompileM String) : CompileM StaticValue := do
    match thing with
    | .value value => checkClass value expected place text
    | .runtime localName =>
      if expected == some .type then
        refuse "TY1" place s!"`{← text}` is a run-time value; a type contains no run-time value"
      else
        refuse "TY2" place
          s!"`{← text}` is not a size: `{localName}` is a run-time value; a size is built from static naturals"
    | .other what => refuse "GR5" place s!"`{← text}` is {what}; a static term is a type, a natural or a module"
    | .declarations steps scopes =>
      let some (id, _) := steps.back? | throw .abandoned
      let found ← declaration id
      match found.kind with
      | .alias | .vocabularyType | .specType | .record | .«variant» | .staticName | .«module» =>
        let values ← bindArguments env steps scopes place
        let inst ← instantiate id values { description := "", span := place }
        let value ← valueOfInstance id inst
        checkClass value expected place text
      | kind => refuse "GR5" place s!"`{← text}` is {kindWord kind}; a static term is a type, a natural or a module"

  partial def checkClass (value : StaticValue) (expected : Option Class) (place : Span)
      (text : CompileM String) : CompileM StaticValue := do
    match expected, value with
    | some .natural, .type _ => refuse "GR5" place s!"`{← text}` is a type; a natural is expected here"
    | some .natural, .«module» _ => refuse "GR5" place s!"`{← text}` is a module; a natural is expected here"
    | some .type, .natural _ => refuse "GR5" place s!"`{← text}` is a natural; a type is expected here"
    | some .type, .«module» _ => refuse "GR5" place s!"`{← text}` is a module; a type is expected here"
    | some .«module», .type _ => refuse "GR5" place s!"`{← text}` is a type; a module is expected here"
    | some .«module», .natural _ =>
      refuse "GR5" place s!"`{← text}` is a natural; a module is expected here"
    | _, _ => return value

  /-- The static value that an instance stands for. -/
  partial def valueOfInstance (id : DeclarationId) (inst : InstanceId) : CompileM StaticValue := do
    let found ← declaration id
    let content := (← get).table.content? inst
    match found.kind, content with
    | .alias, some (.alias type) => return .type type
    | .vocabularyType, some (.vocabularyType type) => return .type type
    | .record, _ => return .type (.record inst)
    | .«variant», _ => return .type (.«variant» inst)
    | .specType, _ => return .type (.specification inst)
    | .staticName, some (.staticName value) => return .natural value
    | .«module», _ => return .«module» inst
    | _, _ => throw (.waiting "an instance without a value")

  /-- The values that a reference gives the parameters of the declaration it names (SP2, SP5):
  the scopes that the place shares with it at the place's values, then the written arguments of
  each segment, positional then named, to the parameters of the scopes that segment covers. A
  parameter that nothing gives is refused (SP6): in a type or a static position nothing infers
  it. -/
  partial def bindArguments (env : Env)
      (steps : Array (DeclarationId × Option (Array Lowered.StaticArgument)))
      (scopes : Std.HashMap ScopeId (Array StaticValue)) (place : Span) :
      CompileM (Array StaticValue) := do
    let program ← program
    let some (id, _) := steps.back? | throw .abandoned
    let found ← declaration id
    let name := program.nameOf id
    let assigned ← assignArguments env steps scopes place
    let mut values := #[]
    for (reference, parameter) in deployedParameters program found do
      match assigned[reference]? with
      | some value => values := values.push value
      | none =>
        refuse "SP6" place
          s!"cannot infer `{parameter.name.text}` of `{name}`; write `{name}<{parameter.name.text} = …>`"
    return values

  /-- The values that a reference gives the parameters of the declaration it names, without
  the ones it leaves to inference (SP6). -/
  partial def assignArguments (env : Env)
      (steps : Array (DeclarationId × Option (Array Lowered.StaticArgument)))
      (scopes : Std.HashMap ScopeId (Array StaticValue)) (place : Span) :
      CompileM StaticEnvironment := do
    let state ← get
    let program := state.program
    let some (id, _) := steps.back? | throw .abandoned
    let found ← declaration id
    let parameters := deployedParameters program found
    let mut assigned : Std.HashMap ParameterRef StaticValue := {}
    for (scope, values) in scopes.toList do
      let ofScope := parameters.filter (·.1.scope == scope)
      for ((reference, _), value) in ofScope.zip values do
        assigned := assigned.insert reference value
    for (reference, _) in parameters do
      if !assigned.contains reference then
        if let some value := env.values[reference]? then
          assigned := assigned.insert reference value
    for (stepId, args?) in steps do
      let some args := args? | continue
      let chain := ((program.declarations[stepId]?).map (·.scopes)).getD #[]
      let candidates := parameters.filter fun (reference, _) =>
        chain.contains reference.scope && !assigned.contains reference
      let stepName := program.nameOf stepId
      let mut position := 0
      let mut numerals : Array String := #[]
      for arg in args do
        match arg with
        | .term argSpan none term =>
          let some (reference, parameter) := candidates[position]?
            | refuse "SP5" argSpan s!"`{stepName}` takes {candidates.size} static arguments here"
          position := position + 1
          let cls ← parameterClass reference
          if cls == .natural then
            if let .number .. := term then numerals := numerals.push parameter.name.text
          assigned := assigned.insert reference (← evalTerm env term cls)
        | .term argSpan (some argName) term =>
          match parameters.find? (·.2.name.text == argName) with
          | some (reference, _) =>
            let cls ← parameterClass reference
            assigned := assigned.insert reference (← evalTerm env term cls)
          | none =>
            refuse "SP5" argSpan s!"`{stepName}` has no static parameter `{argName}`"
        | .inferred _ none => position := position + 1
        | .inferred _ (some _) | .spec .. => pure ()
      if numerals.size >= 2 then
        let named := ", ".intercalate (numerals.toList.map (s!"{·} = …"))
        refuse "SP5" place
          s!"`{stepName}` takes the naturals {", ".intercalate (numerals.toList.map (s!"`{·}`"))}: write them by name, `{stepName}<{named}>`"
    return assigned

  /-- A size: a term over numerals and static naturals with `+ - * / ^`, `log2( )` and
  parentheses, evaluated in the naturals (TY2). -/
  partial def evalSize (env : Env) (expr : Lowered.Expr) : CompileM Nat := withStaticEvaluation do
    spendStatic expr.span (sourceText env expr.span)
    match expr with
    | .number _ value => return value
    | .operator _ .add #[left, right] => return (← evalSize env left) + (← evalSize env right)
    | .operator span .subtract #[left, right] =>
      let a ← evalSize env left
      let b ← evalSize env right
      if b <= a then return a - b
      refuse "TY2" span s!"the size `{← sourceText env span}` is {a} - {b} here: a size is a natural"
    | .operator span .multiply #[left, right] =>
      let a ← evalSize env left
      let b ← evalSize env right
      staticProduct span (sourceText env span) a b
    | .operator span .divide #[left, right] =>
      let a ← evalSize env left
      let b ← evalSize env right
      if 1 <= b && a % b == 0 then return a / b
      refuse "TY2" span s!"the size `{← sourceText env span}` is {a} / {b} here: division in a size is exact"
    | .operator span .power #[base, exponent] =>
      let a ← evalSize env base
      let b ← evalSize env exponent
      staticPower span (sourceText env span) a b
    | .call span (.reference _ segments) #[.positional _ argument] none =>
      if segments.isEmpty then throw .abandoned
      if segments.any fun (.segment step _ _) => step == .sizeOperator then
        let a ← evalSize env argument
        match powerOfTwo a with
        | some exponent => return exponent
        | none => refuse "TY2" span s!"the size `{← sourceText env span}` is log2({a}) here: log2 takes a power of two"
      refuse "TY2" span
        s!"`{← sourceText env span}` is a call; a size is built from static naturals and the operators of sizes"
    | .call span (.reference _ segments) .. =>
      if segments.isEmpty then throw .abandoned
      refuse "TY2" span
        s!"`{← sourceText env span}` is a call; a size is built from static naturals and the operators of sizes"
    | .reference reference@(.reference span _) =>
      let thing ← evalReference env reference
      match ← thingValue env thing (some .natural) span (sourceText env span) with
      | .natural value => return value
      | _ => refuse "GR5" span s!"`{← sourceText env span}` is not a natural; a natural is expected here"
    | .local span _ =>
      match ← thingValue env (← localThing env span) (some .natural) span (sourceText env span) with
      | .natural value => return value
      | _ => refuse "GR5" span s!"`{← sourceText env span}` is not a natural; a natural is expected here"
    | .type type =>
      let span := Lowered.Expr.span (.type type)
      refuse "GR5" span s!"`{← sourceText env span}` is a type; a natural is expected here"
    | .repetition span .. =>
      refuse "GR5" span s!"`{← sourceText env span}` is a type; a natural is expected here"
    | .error _ => throw .abandoned
    | other =>
      refuse "TY2" other.span
        s!"`{← sourceText env other.span}` is not a size: a size is built from numerals and static naturals with `+`, `-`, `*`, `/`, `^` and `log2( )`"

  /-- A closed type (TY1, TY3). -/
  partial def evalType (env : Env) (type : Lowered.TypeTerm) : CompileM ClosedType :=
      withStaticEvaluation do
    let span := Lowered.Expr.span (.type type)
    spendStatic span (sourceText env span)
    match type with
    | .bool _ => return .bool
    | .nat _ => return .nat
    | .rational _ => return .rational
    | .index _ size => return .index (← evalSize env size)
    | .nonzero _ inner => return .nonzero (← evalType env inner)
    | .sequence _ element size =>
      let elementType ← evalType env element
      match size with
      | some size => return .seq elementType (some (← evalSize env size))
      | none => return .seq elementType none
    | .tuple _ fields names =>
      let mut components := #[]
      for field in fields do components := components.push (← evalType env field)
      return .tuple components names
    | .reference reference@(.reference span _) =>
      let thing ← evalReference env reference
      match ← thingValue env thing (some .type) span (sourceText env span) with
      | .type closed => return closed
      | _ => refuse "GR5" span s!"`{← sourceText env span}` is not a type; a type is expected here"
    | .local span _ =>
      match ← thingValue env (← localThing env span) (some .type) span (sourceText env span) with
      | .type closed => return closed
      | _ => refuse "GR5" span s!"`{← sourceText env span}` is not a type; a type is expected here"
    | .error _ => throw .abandoned

  /-- A static term of a class (GR5). -/
  partial def evalTerm (env : Env) (expr : Lowered.Expr) (cls : Class) : CompileM StaticValue := do
    match cls with
    | .natural => return .natural (← evalSize env expr)
    | .type =>
      match asType expr with
      | some type => return .type (← evalType env type)
      | none => refuse "GR5" expr.span s!"`{← sourceText env expr.span}` is a natural; a type is expected here"
    | .«module» =>
      match expr with
      | .reference reference@(.reference span _) =>
        thingValue env (← evalReference env reference) (some .«module») span (sourceText env span)
      | .local span _ => thingValue env (← localThing env span) (some .«module») span (sourceText env span)
      | .error _ => throw .abandoned
      | _ => refuse "GR5" expr.span s!"`{← sourceText env expr.span}` is not a module; a module is expected here"

  /-- A static term whose class its form gives: a side of a constraint, an argument of a row. -/
  partial def evalAny (env : Env) (expr : Lowered.Expr) : CompileM StaticValue := do
    match expr with
    | .reference reference@(.reference span _) =>
      thingValue env (← evalReference env reference) none span (sourceText env span)
    | .local span _ => thingValue env (← localThing env span) none span (sourceText env span)
    | .type _ | .repetition .. | .list .. | .tuple .. =>
      match asType expr with
      | some type => return .type (← evalType env type)
      | none => return .natural (← evalSize env expr)
    | _ => return .natural (← evalSize env expr)

  /-- An interface named by a bound, at the static arguments the bound writes. -/
  partial def evalInterface (env : Env) (reference : Lowered.Reference) :
      CompileM (DeclarationId × Array StaticValue) := do
    let .reference place _ := reference
    match ← evalReference env reference with
    | .declarations steps scopes =>
      let some (id, _) := steps.back? | throw .abandoned
      let found ← declaration id
      unless found.kind == .interface do
        refuse "SP3" place s!"`{(← nameOf id)}` is not an interface"
      return (id, ← bindArguments env steps scopes place)
    | _ => refuse "SP3" place s!"`{← sourceText env place}` is not an interface"

  /-- An interface named by a bound as the syntax writes it: lowered first. -/
  partial def writtenInterface (env : Env) (path : Path) : CompileM (DeclarationId × Array StaticValue) := do
    let some reference ← lowerWritten (Names.Written.pathReference env.file path) | throw .abandoned
    evalInterface env reference

  /-- Whether a module instance names an interface at these static arguments (SP3, SP8). -/
  partial def implements (inst : InstanceId) (interface : DeclarationId)
      (args : Array StaticValue) : CompileM Bool := do
    match (← get).table.content? inst with
    | some (.«module» interfaces _) => return interfaces.any fun (id, values) => id == interface && values == args
    | _ =>
      -- a module whose members are being formed names what its declaration's bound names
      let entry := (← get).table.entries[inst]!
      let found ← declaration entry.key.declaration
      let some bound := Names.implementing? found | return false
      let moduleEnv := instanceEnv (← program) found entry.key.arguments
      for (id, path) in ← boundInterfaces moduleEnv bound do
        if id == interface then
          let (_, values) ← writtenInterface moduleEnv path
          if values == args then return true
      return false

  /-- Whether a value meets one sort of a bound; the text of the failure when it does not. -/
  partial def meetsSort (env : Env) (value : StaticValue) (sort : Lowered.SortTerm) :
      CompileM (Option String) := do
    let state ← get
    match sort with
    | .nat _ => return match value with
      | .natural _ => none
      | _ => some "a natural is expected"
    | .linear _ => return match value with
      | .type _ => none
      | _ => some "a type is expected"
    | .reference reference@(.reference place segments) =>
      if segments.isEmpty then throw .abandoned
      let some (.segment (.declaration interface) _ _) := segments.back? | return none
      match state.sortNames[interface]? with
      | some sortName =>
        match value with
        | .type type =>
          if hasSort (← getVocabulary) type sortName then return none
          return some s!"`{renderType state type}` is not of sort `{sortName}`"
        | _ => return some s!"`{renderValue state value}` is not a type of sort `{sortName}`"
      | none =>
        let (_, args) ← evalInterface env reference
        match value with
        | .«module» inst =>
          if ← implements inst interface args then return none
          return some s!"`{renderInstance state inst}` does not implement `{← sourceText env place}`"
        | _ => return some s!"`{renderValue state value}` is not a module"

  /-- The bound of every parameter of an instance, outermost scope first (SP3). -/
  partial def checkBounds (env : Env) (found : Declaration) (name : String) : CompileM Unit := do
    let state ← get
    let modules ← getModules
    for (reference, parameter) in deployedParameters state.program found do
      let some value := env.values[reference]? | continue
      let some scope := modules.loweredScope? reference.scope
        | throw (.defect "a scope without its lowered form")
      let bound : Option Lowered.Bound := (scope.bounds[reference.index]?).getD none
      match bound with
      | none =>
        if let .type type := value then
          if isLinear (← get) type then
            refuse "SP3" parameter.name.span
              s!"`{renderType (← get) type}` is linear; `{parameter.name.text}` of `{name}` takes freely copied data: bound it `linear`"
      | some bound =>
        let scopeEnv := { env with file := (state.program.scopes[reference.scope]?).map (·.file) |>.getD env.file }
        for sort in bound.sorts do
          if let some failure ← meetsSort scopeEnv value sort then
            refuse "SP3" bound.span
              s!"{failure}, which `{parameter.name.text}` of `{name}` requires"

  /-- Whether a constraint holds at an instance; the text of the failure when it does not
  (SP4). A specification conjunct is no part of the admission and is not evaluated (SP11). -/
  partial def checkConstraint (env : Env) (constraint : Lowered.Constraint) (owner : String) :
      CompileM (Option String) := do
    let state ← get
    let constraintText ← sourceText env (constraintSpan constraint)
    let failed (here : String) : String :=
      s!"`{owner}` requires `{constraintText}`, which is `{here}` here and does not hold"
    match constraint with
    | .bound _ subject sorts =>
      if ← mentionsSpecParameter subject then return none
      let value ← evalAny env subject
      for sort in sorts do
        if let some _ ← meetsSort env value sort then
          return some (failed s!"{renderValue state value}: {← sourceText env (sortSpan sort)}")
      return none
    | .compare span operator left right =>
      if (← mentionsSpecParameter left) || (← mentionsSpecParameter right) then return none
      let a ← evalAny env left
      let b ← evalAny env right
      let holds : Option Bool := match a, b with
        | .natural x, .natural y => some (match operator with
          | .equal => x == y | .notEqual => x != y | .less => x < y | .lessEqual => x <= y
          | .greater => x > y | .greaterEqual => x >= y | _ => false)
        | .type x, .type y => match operator with
          | .equal => some (x == y) | .notEqual => some (x != y) | _ => none
        | .«module» x, .«module» y => match operator with
          | .equal => some (x == y) | .notEqual => some (x != y) | _ => none
        | _, _ => none
      match holds with
      | some true => return none
      | some false =>
        return some (failed s!"{renderValue state a}{compareText operator}{renderValue state b}")
      | none =>
        refuse "GR5" span
          s!"`{constraintText}` compares {renderValue state a} and {renderValue state b}: a constraint compares two sizes or two types"

  /-- The `where` constraints of the scopes of an instance, outermost first (SP4). At a default
  instance a constraint that does not hold skips the instance (SP7). -/
  partial def checkWheres (env : Env) (found : Declaration) (owner : String) (isDefault : Bool)
      (skip : Lowered.Constraint → CompileM Bool) : CompileM Unit := do
    let modules ← getModules
    let program ← program
    for scope in found.scopes do
      let some lowered := modules.loweredScope? scope | continue
      let scopeEnv := { env with file := (program.scopes[scope]?).map (·.file) |>.getD env.file }
      for constraint in lowered.constraints do
        if ← skip constraint then continue
        -- a constraint that cannot be evaluated here (it reads a member that a later layer
        -- gives) is not taken to hold: the instance waits for it (SP4)
        let outcome ← try checkConstraint scopeEnv constraint owner
          catch failure => match failure with
            | .waiting reason => throw (.waiting s!"a constraint of its `where`: {reason}")
            | other => throw other
        if let some message := outcome then
          if isDefault then throw .skipped
          refuse "SP4" (constraintSpan constraint) message

  /-- The instance of a declaration at values, made once (SP7). -/
  partial def instantiate (id : DeclarationId) (values : Array StaticValue) (requested : Frame)
      (isDefault : Bool := false) (specification : Array Nat := #[])
      (owner : Option InstanceId := none) : CompileM InstanceId := do
    let key : InstanceKey := { declaration := id, arguments := values, specification, owner }
    let description ← describeInstance id values specification owner
    -- an instance first asked for as a default instance is one (SP7)
    if isDefault && ((← getResults).signatures.find? key).isNone then
      modifyResults fun results =>
        let next := results.signatures.entries.size
        { results with defaultInstances := results.defaultInstances.insert next }
    let frame : ChainFrame :=
      { subject := .ofText (if isDefault then s!"default instance `{description}`" else description)
        span := requested.span }
    -- the request for the signature: entered in progress when it is new, and recorded with the
    -- request that makes it
    let requester ← currentRequest?
    let (inst, isNew) ← modifyGetResults fun results =>
      let table := results.signatures
      let results := { results with signatures := {} }
      let (table, inst, isNew) := table.intern key frame requester
      let results := { results with signatures := table }
      let results := match requester with
        | some requester => results.addRequest requester ⟨.signature, inst⟩
        | none => results
      ((inst, isNew), results)
    unless isNew do
      let found : Option (QueryState Typed.Signature) :=
        ((← getResults).signatures.entries[inst]?).map (·.state)
      match found with
      | some (.done _) => return inst
      | some .inProgress => refuseRecursion description requested.span
      | some (.exhausted exhaustion) => throw (.exhausted exhaustion)
      | some .skipped =>
        -- skipped as a default instance: skipped again as one; asked for by the program, it is
        -- an instance like any other, computed now and refused where its `where` fails (SP4)
        if isDefault then throw .skipped
        modifyResults fun results =>
          { results.modifySignatures (·.reenter inst frame requester) with
            defaultInstances := results.defaultInstances.erase inst }
      | _ => throw .abandoned
    -- a request deeper than the budget of the chain is not computed: it is exhausted (SP10)
    if ← beyondDepth then
      let exhaustion ← logExhaustion .instantiationDepth frame
      modifyResults (·.modifySignatures (·.setState inst (.exhausted exhaustion)))
      throw (.exhausted exhaustion)
    try
      withRequest ⟨.signature, inst⟩ do
        let content ← instanceContent id inst values isDefault specification owner
        modifyResults (·.modifySignatures (·.setState inst (.done (.data content))))
        let found ← declaration id
        if found.kind == .«module» then
          moduleConditions inst found values isDefault
      return inst
    catch failure =>
      match failure with
      | .waiting reason =>
        modifyResults (·.modifySignatures (·.setState inst (.done (.data (.waits reason)))))
        return inst
      | .exhausted exhaustion =>
        modifyResults (·.modifySignatures (·.setState inst (.exhausted exhaustion)))
        throw (.exhausted exhaustion)
      | .skipped =>
        -- nothing is refused and nothing is logged, so the entry is not a failed one
        modifyResults (·.modifySignatures (·.setState inst .skipped))
        throw .skipped
      | other =>
        modifyResults (·.modifySignatures (·.setState inst .failed))
        throw other

  /-- What an instance holds: bounds and `where` first, then the types of its signature, read
  from its lowered declaration. -/
  partial def instanceContent (id : DeclarationId) (inst : InstanceId)
      (values : Array StaticValue) (isDefault : Bool) (specification : Array Nat := #[])
      (owner : Option InstanceId := none) : CompileM InstanceContent := do
    let program ← program
    let found ← declaration id
    let content := (((← getModules).lowered? id).map (·.content)).getD (.unlowered #[])
    let env := { instanceEnv program found values specification with
      self? := owner.map StaticValue.module }
    let name := program.nameOf id
    match found.node with
    | .typeDecl (.type _ _ _ _ (.primitive _)) | .«module» (.«module» _ _ _ _ _ _ (.primitive _))
    | .«module» (.«module» _ _ _ _ _ _ (.asset _)) => checkBindings id
    | _ => pure ()
    checkBounds env found name
    checkWheres env found name isDefault (hostDefinition env found)
    let optional (type : Lowered.TypeTerm) : CompileM (Option ClosedType) := do
      try return some (← evalType env type)
      catch failure => match failure with
        | .waiting _ => return none
        | other => throw other
    let parameters (head : Lowered.FunctionHead) : CompileM (Array (String × Option ClosedType)) :=
      head.parameters.mapM fun parameter => do return (parameter.binder.name, ← optional parameter.type)
    match found.node, content with
    | .typeDecl (.type _ _ _ _ (.type _)), .alias type => return .alias (← evalType env type)
    | .typeDecl (.type _ _ _ _ (.primitive _)), .vocabularyType row arguments =>
      let mut args := #[]
      for arg in arguments do
        match arg with
        | .term _ _ term => args := args.push (← evalAny env term)
        | _ => pure ()
      return .vocabularyType (.nominal row args)
    | .typeDecl (.specType ..), _ => return .unevaluated
    | .struct node, .record _ fields =>
      let mut evaluated := #[]
      for (fieldName, type) in fields do evaluated := evaluated.push (fieldName.text, ← evalType env type)
      return .record node.linear evaluated
    | .enum _, .«variant» alternatives =>
      let mut evaluated := #[]
      for (alternativeName, types) in alternatives do
        let mut payload := #[]
        for type in types do payload := payload.push (← evalType env type)
        evaluated := evaluated.push (alternativeName.text, payload)
      return .«variant» evaluated
    | .«def» _, .function head _ =>
      -- the parameters first, then the result, in the order of the text
      let evaluated ← parameters head
      let result ← match head.result with
        | some type => optional type
        | none => pure (some ClosedType.unit)
      return .signature evaluated result
    | .oracleDef node, _ =>
      -- an oracle function is not lowered: its parameter types are lowered as written
      let types ← lowerWritten (node.params.mapM fun param => Names.Written.typeTerm env.file param.type)
      let parameters ← (node.params.zip types).mapM fun (param, type) => do
        return (param.name.text, ← optional type)
      return .signature parameters none
    | .relation _, .function head _ | .law _, .function head _ | .member (.lawMember _), .function head _ =>
      return .signature (← parameters head) (some .bool)
    | .protocol _, .protocol head _ _ =>
      let ports ← head.ports.mapM fun port => do return (port.binder.name, ← optional port.type)
      let results ← head.results.mapM fun result => do return (result.name.text, ← optional result.type)
      return .protocol ports results
    | .staticName _, .staticName value => return .staticName (← evalSize env value)
    | .«module» node, _ => moduleContent inst found node env
    | _, _ => return .unevaluated

  /-- Whether a constraint of a module without a body defines one of its members (`Member == T`,
  SP4); it is then no condition. -/
  partial def hostDefinition (_env : Env) (found : Declaration) (constraint : Lowered.Constraint) :
      CompileM Bool := do
    unless found.kind == .«module» && Names.hasNoBody found do return false
    let .compare _ .equal (.reference (.reference _ segments)) _ := constraint | return false
    match segments.toList.map fun (.segment step _ _) => step with
    | [.declaration _, .member _ _] => return true
    | _ => return false

  /-- The member table of a module instance, with the checks of SP8 and NL9 that need no value. -/
  partial def moduleContent (_inst : InstanceId) (found : Declaration)
      (node : Module) (env : Env) : CompileM InstanceContent := do
    let state ← get
    let program := state.program
    let .«module» _ _ moduleName _ bound _ body := node
    let name := moduleName.text
    let mut interfaces : Array (DeclarationId × Array StaticValue) := #[]
    if let some bound := bound then
      for sort in bound.sorts do
        if let .path path := sort then
          let (interface, args) ← writtenInterface env path
          if state.sortNames.contains interface then
            refuse "SP3" path.span s!"`{name}` names the sort `{program.nameOf interface}`: only the vocabulary implements a sort"
          interfaces := interfaces.push (interface, args)
    let mut members : Array (String × MemberValue) := #[]
    -- the members that its `where` defines, for a module without a body
    if Names.hasNoBody found then
      if let some lowered := found.ownScope.bind ((← getModules).loweredScope? ·) then
        for constraint in lowered.constraints do
          if let .compare _ .equal (.reference (.reference _ segments)) right := constraint then
            if ← hostDefinition env found constraint then
              let memberName := match segments.back? with
                | some (.segment (.member member _) _ _) => member
                | _ => ""
              match ← evalAny env right with
              | .type type => members := members.push (memberName, .type type)
              | .natural value => members := members.push (memberName, .natural value)
              | .«module» other => members := members.push (memberName, .«module» other)
    match body with
    | .primitive primitive =>
      let row := primitive.row.content
      if let some entry := (← getVocabulary).module? row then
        if let some implemented := entry.implements then
          let named := interfaces.map fun (interface, _) => qualifiedName program interface
          unless named.contains implemented do
            refuse "SP8" moduleName.span
              s!"`{name}` is bound to the row `{row}`, which implements `{implemented}`, not `{", ".intercalate named.toList}`"
        for (memberName, type) in entry.typeMembers do
          members := members.push (memberName, .type type)
        for (memberName, value) in entry.naturalMembers do
          members := members.push (memberName, .natural value)
      for (interface, _) in interfaces do
        for member in (state.members[(← declaration interface).inner.getD 0]?).getD #[] do
          let memberDeclaration ← declaration member
          if memberDeclaration.kind == .functionMember then
            members := members.push (program.nameOf member, .row row)
      return .«module» interfaces members
    | .asset _ => return .«module» interfaces members
    | .suite _ =>
      let inner := found.inner.getD found.namespace
      let names := ((program.namespaces[inner]?).map (·.names)).getD {}
      let mut declared : Array String := #[]
      for (interface, _) in interfaces do
        let interfaceDeclaration ← declaration interface
        let interfaceName := program.nameOf interface
        for member in (state.members[interfaceDeclaration.inner.getD 0]?).getD #[] do
          let memberDeclaration ← declaration member
          let memberName := program.nameOf member
          if memberDeclaration.kind == .lawMember || declared.contains memberName then continue
          declared := declared.push memberName
          let some (Binding.declaration definition) := names[memberName]?
            | refuse "SP8" moduleName.span s!"`{name}` does not define `{memberName}` of `{interfaceName}`"
          let definitionDeclaration ← declaration definition
          let site := ((definitionDeclaration.name.map (·.span)).getD moduleName.span)
          let memberParameters := ((memberDeclaration.ownScope.bind fun scope =>
            program.scopes[scope]?).map (·.parameters.size)).getD 0
          let definitionParameters := ((definitionDeclaration.ownScope.bind fun scope =>
            program.scopes[scope]?).map (·.parameters.size)).getD 0
          let wrong (what : String) : CompileM Unit :=
            refuse "SP8" site s!"`{name}` defines `{memberName}` of `{interfaceName}`, {what}, as {kindWord definitionDeclaration.kind}"
          match memberDeclaration.kind with
          | .typeMember =>
            unless [DeclarationKind.alias, .vocabularyType, .record, .«variant», .specType].contains
                definitionDeclaration.kind do wrong "a type member"
            unless memberParameters == definitionParameters do
              refuse "SP8" site s!"`{name}::{memberName}` has {definitionParameters} static parameters; `{interfaceName}` declares {memberParameters}"
            if memberParameters == 0 then
              let value ← thingValue env (.declarations #[(definition, none)] {}) (some .type) site (pure memberName)
              match value with
              | .type type => members := members.push (memberName, .type type)
              | _ => pure ()
            else members := members.push (memberName, .definition definition)
          | .naturalMember =>
            unless definitionDeclaration.kind == .staticName do wrong "a natural member"
            match ← thingValue env (.declarations #[(definition, none)] {}) (some .natural) site (pure memberName) with
            | .natural value => members := members.push (memberName, .natural value)
            | _ => pure ()
          | .moduleMember =>
            let value ← match definitionDeclaration.node with
              | .moduleMember moduleNode =>
                let term ← lowerWritten (Names.Written.pathExpr env.file moduleNode.path.span moduleNode.path)
                evalTerm env term .«module»
              | .«module» _ => thingValue env (.declarations #[(definition, none)] {}) (some .«module») site (pure memberName)
              | _ => do wrong "a module member"; throw .abandoned
            if let .«module» other := value then
              if let .member (.moduleMember _ _ memberBound) := memberDeclaration.node then
                let memberEnv : Env := { file := memberDeclaration.file, values := (instanceEnv program interfaceDeclaration
                  ((interfaces.find? (·.1 == interface)).map (·.2) |>.getD #[])).values }
                for (required, path) in ← boundInterfaces memberEnv memberBound do
                  let (_, args) ← writtenInterface memberEnv path
                  unless ← implements other required args do
                    refuse "SP8" site s!"`{name}::{memberName}` is `{renderInstance (← get) other}`, which does not implement `{program.nameOf required}`"
              members := members.push (memberName, .«module» other)
          | .functionMember =>
            match definitionDeclaration.node, memberDeclaration.node with
            | .memberDef definitionNode, .member (.defMember _ modifier _ _ params _ _) =>
              let memberSpec := match modifier with
                | some (.spec _) => true
                | _ => false
              if memberSpec && !definitionNode.spec then
                refuse "SP8" site s!"`{interfaceName}` declares `{memberName}` as a `spec def`: write `spec def {memberName}(…)`"
              if !memberSpec && definitionNode.spec then
                refuse "SP8" site s!"`{interfaceName}` declares `{memberName}` as a `def`: `{name}` defines it as deployed code, not as a `spec def`"
              unless definitionNode.params.size == params.size do
                refuse "SP8" site s!"`{name}::{memberName}` has {definitionNode.params.size} binders; `{interfaceName}` declares {params.size} parameters"
            | _, _ =>
              refuse "SP8" site s!"`{name}` defines the function `{memberName}` of `{interfaceName}` by its binders: `def {memberName}(x…)`"
            members := members.push (memberName, .definition definition)
          | .protocolMember =>
            unless definitionDeclaration.kind == .protocol do wrong "a protocol member"
            members := members.push (memberName, .definition definition)
          | _ => pure ()
      for member in (state.members[inner]?).getD #[] do
        let memberDeclaration ← declaration member
        let memberName := program.nameOf member
        if (memberDeclaration.kind == .functionDefinition || memberDeclaration.kind == .moduleDefinition)
            && !declared.contains memberName then
          let interfaceNames := ", ".intercalate (interfaces.toList.map fun (i, _) => program.nameOf i)
          refuse "SP8" ((memberDeclaration.name.map (·.span)).getD moduleName.span)
            s!"`{name}` defines `{memberName}`, which `{interfaceNames}` does not have"
      return .«module» interfaces members

  /-- The conditions that the interfaces of a module instance put on it: the bounds of their
  parameters and their `where` (SP3, SP4). -/
  partial def moduleConditions (inst : InstanceId) (found : Declaration)
      (_values : Array StaticValue) (isDefault : Bool) : CompileM Unit := do
    let program ← program
    let some (.«module» interfaces _) := (← get).table.content? inst | return
    let moduleName := ((found.name.map (·.text)).getD "")
    for (interface, args) in interfaces do
      let interfaceDeclaration ← declaration interface
      let interfaceEnv : Env :=
        { instanceEnv program interfaceDeclaration args with self? := some (.«module» inst) }
      checkBounds interfaceEnv interfaceDeclaration (program.nameOf interface)
      let some lowered := interfaceDeclaration.ownScope.bind ((← getModules).loweredScope? ·) | continue
      for constraint in lowered.constraints do
        -- a constraint of an interface that cannot be evaluated here is not taken to hold:
        -- the module instance waits for it (SP4)
        let outcome ← try checkConstraint interfaceEnv constraint moduleName
          catch failure => match failure with
            | .waiting reason => throw (.waiting s!"a constraint of `{program.nameOf interface}`: {reason}")
            | other => throw other
        if let some message := outcome then
          if isDefault then throw .skipped
          refuse "SP4" (constraintSpan constraint) message
end

/-! ## The terms that typing reads from the syntax

Each is lowered apart from its declaration, from the tables of resolutions, and evaluated in its
lowered form. -/

def evalWrittenSize (env : Env) (expr : Expr) : CompileM Nat := do
  evalSize env (← lowerWritten (Names.Written.expr env.file expr))

def evalWrittenType (env : Env) (type : TypeExpr) : CompileM ClosedType := do
  evalType env (← lowerWritten (Names.Written.typeTerm env.file type))

def evalWrittenAny (env : Env) (expr : Expr) : CompileM StaticValue := do
  evalAny env (← lowerWritten (Names.Written.expr env.file expr))

/-- What a written path stands for. -/
def evalWrittenPath (env : Env) (path : Path) : CompileM Thing := do
  let some reference ← lowerWritten (Names.Written.pathReference env.file path) | throw .abandoned
  evalReference env reference

/-- What the steps of a written path stand for, as the table records them; `text` is the path as
written, which a local name stands for. -/
def evalWrittenSteps (env : Env) (steps : Array ResolvedSegment) (place : Span) (_text : String) :
    CompileM Thing := do
  if steps.isEmpty then return .declarations #[] {}
  let .reference _ segments := Names.Written.reference place { segments := steps }
  evalSegments env segments place

def assignWrittenArguments (env : Env) (steps : Array (DeclarationId × Option StaticArgs))
    (scopes : Std.HashMap ScopeId (Array StaticValue)) (place : Span) :
    CompileM StaticEnvironment := do
  assignArguments env (← lowerSteps env steps) scopes place

/-- Whether a constraint as written holds: lowered first. -/
def checkWrittenConstraint (env : Env) (constraint : Constraint) (owner : String) :
    CompileM (Option String) := do
  let lowered ← lowerWritten (Names.Written.constraint env.file constraint)
  checkConstraint env lowered owner

end Zkc.Frontend.Static
