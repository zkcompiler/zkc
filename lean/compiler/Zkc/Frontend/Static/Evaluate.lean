module

public import Zkc.Frontend.Static.ModuleBindings
public import Zkc.Frontend.Static.ProtocolView
public import Zkc.Frontend.Static.ProtocolHead

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
  the last names the target. `scopes` holds module member arguments and import-fixed arguments
  by parameter identity. -/
  | declarations (steps : Array (DeclarationId × Option (Array Lowered.StaticArgument)))
      (scopes : StaticEnvironment)
  /-- A local name: a run-time value. -/
  | runtime (name : String)
  /-- Something that is no static thing: a function, an alternative. -/
  | other (what : String)
  deriving Inhabited

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

/-- The specification-only parameters that a static term names. -/
def specParametersOf (term : Lowered.Expr) : CompileM (Array ParameterRef) := do
  let state ← get
  let mut found := #[]
  for (.reference _ segments) in term.references do
    for (.segment step _ _) in segments do
      if let .parameter reference := step then
        let spec := ((state.program.scopes[reference.scope]?).bind
          (·.parameters[reference.index]?)).any (·.spec)
        if spec then found := found.push reference
  return found

/-- Whether a static term names a specification-only parameter. -/
def mentionsSpecParameter (term : Lowered.Expr) : CompileM Bool :=
  return !(← specParametersOf term).isEmpty

/-- A deployed member call has no proof arguments. A bound can mention one inside
an interface application even when its subject is a concrete receiver. -/
def hasProofBoundArgument : Lowered.Constraint → CompileM Bool
  | .bound _ _ sorts => sorts.anyM fun
    | .reference reference => mentionsSpecParameter (.reference reference)
    | _ => pure false
  | .compare .. => pure false

/-- The static evaluator needs the specification argument of a deployed declaration. -/
def unboundSpecificationParameter := "a specification-only parameter"

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

/-- An inferred module argument is an optional candidate. Only a default root is
reported as such in the chains produced when its body is typed. -/
inductive InstanceDemand where
  | required | candidate (requiredInterfaces : Array AppliedInterface) | defaultRoot
  deriving BEq


/-- Read assigned arguments in declaration order, reporting any unsolved slot (SP6). -/
def requiredArguments {α : Type} (id : DeclarationId) (assigned : Std.HashMap ParameterRef α)
    (place : Span) : CompileM (Array α) := do
  let program ← program
  let name := program.nameOf id
  (deployedParameters program (← declaration id)).mapM fun (ref, param) => do
    let some value := assigned[ref]?
      | refuse "SP6" place s!"cannot infer `{param.name.text}` of `{name}`; write `{name}<{param.name.text} = …>`"
    return value

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
      let .segment step arguments fixedBy := segment
      match step with
      | .«local» => return ← localThing env place
      | .parameter reference =>
        match env.values[reference]? with
        | some value => thing := .value value
        | none =>
          let state ← get
          let spec := ((state.program.scopes[reference.scope]?).bind
            (·.parameters[reference.index]?)).any (·.spec)
          throw (.waiting (if spec then unboundSpecificationParameter
            else "a parameter outside the instance"))
      | .self _ =>
        match env.self? with
        | some value => thing := .value value
        | none => throw (.waiting "`Self` outside an instance")
      | .declaration id =>
        match thing with
        | .declarations previous scopes =>
          -- A specialization fixed by a use belongs to the import's scopes (SP2).
          -- A shared parameter at the use site cannot take its positional slot.
          if let (some importId, some args) := (fixedBy, arguments) then
            let program ← program
            let some origin := program.imports[importId]? | throw .abandoned
            let defining := {env with
              file := origin.file
              values := env.values.filter (fun ref _ => origin.scopes.contains ref.scope)}
            let assigned ← assignArguments defining (previous.push (id, some args)) scopes place
            thing := .declarations ((previous.map fun (decl, _) => (decl, none)).push (id, none)) assigned
          else thing := .declarations (previous.push (id, arguments)) scopes
        | _ => throw (.waiting "a declaration reached through a value")
      | .member name _ => thing ← memberOfThing env thing name arguments place
      | .generated name => thing ← generatedMember env thing name arguments place
      | .alternative .. => thing := .other "an alternative"
      | .fixed _ | .sizeOperator => thing := .other "a function"
      | .vocabularyModule _ | .entry .. | .role _ | .word _ | .label _ | .bareAlternative _ =>
        thing := .other "no static thing"
    return thing

  /-- A closed protocol's generated source types (§8). Run-tree multiplicities are
  checked against draws in the checked program, in source order. -/
  partial def generatedMember (env : Env) (prefix_ : Thing) (name : String)
      (args : Option (Array Lowered.StaticArgument)) (place : Span) : CompileM Thing := do
    let .declarations steps scopes := prefix_ | throw (.waiting s!"the generated member `{name}`")
    let some (id, _) := steps.back? | throw .abandoned
    unless (← declaration id).kind == .protocol && ["Run","Runs","Inputs","Coins","Received"].contains name do
      throw (.waiting s!"the generated member `{name}`")
    let arguments ← bindArguments env steps scopes place
    let inst ← instantiate id arguments ⟨"", place⟩
    let view ← match name with
      | "Run" =>
        if args.isSome then refuse "SX9" place "Run takes no static arguments"
        pure ProtocolView.run
      | "Runs" => pure ProtocolView.run
      | _ =>
        let some #[.term _ none (.reference (.reference _ #[.segment (.role role) none _]))] := args
          | refuse "SX9" place s!"`{name}` takes one role of this protocol"
        pure (if name == "Inputs" then .inputs role else if name == "Coins" then .coins role else .received role)
    if name != "Runs" then return .value (.type (.record (← protocolViewRecord inst view place)))
    let code ← checkedViewProtocol inst place
    let results ← getResults
    if let some blocked := code.nestedDraw then
      refuse "SX9" place s!"Runs is undefined for a draw in a choice, loop or application (line {blocked.startLine})"
    let leaf ← protocolViewRecord inst .run place
    let laws := code.flows.filterMap fun
      | .draw _ _ law _ => some law
      | _ => none
    let counts := args.getD #[]
    unless counts.size == laws.size do
      refuse "SX9" place s!"Runs takes one multiplicity for each of {laws.size} draws"
    let mut product := 1
    let mut single := none
    for (argument, law) in counts.zip laws do
      let .term span none count := argument | refuse "SX9" place "Runs takes positional multiplicities"
      let k ← evalSize env count
      let some row := results.rows[law]? | throw (.defect "missing draw law")
      let #[type] := row.outputs | throw (.defect "expected one draw result")
      unless k > 0 && (← viewLawCapacity type k) == k do
        refuse "SX6" span "run multiplicity is outside the draw domain"
      if let some one := single then
        unless one == (k == 1) do refuse "SX6" span "run multiplicities must all be one or all exceed one"
      single := some (k == 1)
      product ← staticProduct span (pure "the number of leaves in Runs") product k
    return .value (.type (.seq (.record leaf) (some product)))

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

  /-- Read one implementation from a complete or provisional module, including through
  the opaque parameter view used to elaborate a generic body. -/
  partial def lookupModuleMember (inst : InstanceId) (name : String) (place : Span) :
      CompileM (Option MemberValue) := do
    let result ← resolveModuleMember inst name place
    if result.isSome then observeMember inst place (receiver := true)
    return result

  partial def resolveModuleMember (inst : InstanceId) (name : String) (place : Span) :
      CompileM (Option MemberValue) := do
    let state ← get
    let members : Array (String × MemberValue) ← match state.table.content? inst with
      | some (.«module» _ members) => pure members
      | some (.checkingModule interfaces bindings) => do
        let key := (inst, name)
        if (← read).checkingMembers.contains key then
          refuseRecursion s!"{renderInstance state inst}::{name}" place
        let keyOfModule := state.table.allocatedKey! inst
        let owner ← declaration keyOfModule.declaration
        let .«module» (.«module» _ _ moduleName _ _ _ body) := owner.node
          | throw (.defect "a provisional receiver is not a module")
        let defining := instanceEnv state.program owner keyOfModule.arguments keyOfModule.specification
        withReader (fun ctx => { ctx with checkingMembers := key :: ctx.checkingMembers }) <|
          moduleMemberValues owner moduleName body defining interfaces.applications bindings (some name)
      | _ => throw (.waiting "a member of a module whose members are being formed")
    let found : Option MemberValue := (members.find? (·.1 == name)).map (·.2)
    match found with
    | some (.fromReceiver receiver) => resolveModuleMember receiver name place
    | member => return member

  /-- A member of a static thing at an instance: of a type, from the vocabulary and from TY11;
  of a module instance, from its member table. -/
  partial def memberOfValue (env : Env) (value : StaticValue) (name : String)
      (args : Option (Array Lowered.StaticArgument)) (place : Span) : CompileM Thing := do
    let state ← get
    match value with
    | .«module» inst =>
      let found ← lookupModuleMember inst name place
      match found with
      | some (.type type) => return .value (.type type)
      | some (.natural number) => return .value (.natural number)
      | some (.«module» other) => return .value (.«module» other)
      | some (.definition id) =>
        let instanceKey := state.table.allocatedKey! inst
        let owner ← declaration instanceKey.declaration
        return .declarations #[(id, args)] (instanceEnv state.program owner instanceKey.arguments).values
      | some (.row _) => return .other "a function"
      | some (.fromReceiver _) => throw (.defect "an unresolved module member projection")
      | some (.opaqueType sorts) =>
        -- an application of a type member that is opaque (SP12): a fresh type per arguments
        let mut values := #[]
        for arg in args.getD #[] do
          if let .term _ _ term := arg then values := values.push (← evalAny env term)
        return .value (.type (.opaque inst name values sorts))
      | none =>
        -- a module bound to the vocabulary or to an asset has the members that its row or its
        -- asset gives: one that they do not give is not known here
        let instanceKey := state.table.allocatedKey! inst
        if let some owner := state.program.declarations[instanceKey.declaration]? then
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
      (text : CompileM String) (selected : Bool := true) : CompileM StaticValue := do
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
        let inst ← formInstance id values { description := "", span := place }
        if selected then observeApplication inst place
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
      (scopes : StaticEnvironment) (place : Span) :
      CompileM (Array StaticValue) := do
    let some (id, _) := steps.back? | throw .abandoned
    requiredArguments id (← assignArguments env steps scopes place) place

  /-- The values that a reference gives the parameters of the declaration it names, without
  the ones it leaves to inference (SP6). -/
  partial def assignArguments (env : Env)
      (steps : Array (DeclarationId × Option (Array Lowered.StaticArgument)))
      (scopes : StaticEnvironment) (place : Span) :
      CompileM StaticEnvironment := do
    let state ← get
    let program := state.program
    let some (id, _) := steps.back? | throw .abandoned
    let found ← declaration id
    let parameters := deployedParameters program found
    let mut assigned := scopes
    for (reference, _) in parameters do
      if !assigned.contains reference then
        if let some value := env.values[reference]? then
          assigned := assigned.insert reference value
    for (stepId, args?) in steps do
      let some args := args? | continue
      let chain := ((program.declarations[stepId]?).map (·.scopes)).getD #[]
      let visible := parameters.filter fun (ref, _) => chain.contains ref.scope
      assigned ← assignWritten env stepId visible assigned args place
    return assigned

  /-- Bind a written argument list to the deployed parameters visible at this segment.
  A member exposes only its own parameters: its interface arguments are already fixed. -/
  partial def assignWritten (env : Env) (step : DeclarationId)
      (parameters : Array (ParameterRef × StaticParam)) (initial : StaticEnvironment)
      (args : Array Lowered.StaticArgument) (place : Span) : CompileM StaticEnvironment := do
    assignWrittenWith (evalTerm env) step parameters initial args place

  /-- The same slot assignment for closed values and for classed terms of an open head. -/
  partial def assignWrittenWith {α : Type} (evaluate : Lowered.Expr → Class → CompileM α)
      (step : DeclarationId) (parameters : Array (ParameterRef × StaticParam))
      (initial : Std.HashMap ParameterRef α) (args : Array Lowered.StaticArgument) (place : Span) :
      CompileM (Std.HashMap ParameterRef α) := do
    let program ← program
    let found ← declaration step
    let name := program.nameOf step
    let candidates := parameters.filter fun (reference, _) => !initial.contains reference
    let mut assigned := initial
    let mut position := 0
    let mut numerals := #[]
    let mut used := #[]
    for arg in args do
      let (span, label, term?) ← match arg with
        | .term span label term => pure (span, label, some term)
        | .inferred span label => pure (span, label, none)
        | .spec .. => continue
      let (reference, parameter) ← match label with
        | none =>
          let some next := candidates[position]?
            | refuse "SP5" span s!"`{name}` takes {candidates.size} static arguments here"
          pure next
        | some label =>
          match parameters.find? (·.2.name.text == label) with
          | some next => pure next
          | none =>
            if (specificationParameters program found).any (·.2.name.text == label) then
              refuse "SP11" span s!"`{label}` is a specification-only parameter and cannot be supplied as a deployed argument"
            refuse "SP5" span s!"`{name}` has no static parameter `{label}`"
      if used.contains reference then
        refuse "SP5" span s!"the static argument `{parameter.name.text}` of `{name}` is given twice"
      used := used.push reference
      if label.isNone then position := position + 1
      if let some term := term? then
        let cls ← parameterClass reference
        if label.isNone && cls == .natural && (term matches .number ..) then
          numerals := numerals.push parameter.name.text
        assigned := assigned.insert reference (← evaluate term cls)
    if numerals.size >= 2 then
      let named := ", ".intercalate (numerals.toList.map (s!"{·} = …"))
      refuse "SP5" place
        s!"`{name}` takes the naturals {", ".intercalate (numerals.toList.map (s!"`{·}`"))}: write them by name, `{name}<{named}>`"
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
      let args ← bindArguments env steps scopes place
      observeDeclarationApplication id args place
      return (id, args)
    | _ => refuse "SP3" place s!"`{← sourceText env place}` is not an interface"

  /-- An interface named by a bound as the syntax writes it: lowered first. -/
  partial def writtenInterface (env : Env) (path : Path) : CompileM (DeclarationId × Array StaticValue) := do
    let some reference ← lowerWritten (Names.Written.pathReference env.file path) | throw .abandoned
    evalInterface env reference

  /-- Whether a module instance names an interface at these static arguments (SP3, SP8). -/
  partial def implements (inst : InstanceId) (interface : DeclarationId)
      (args : Array StaticValue) : CompileM Bool := do
    match (← get).table.content? inst with
    | some (.«module» interfaces _) => return interfaces.applications.any fun (id, values) => id == interface && values == args
    | some (.checkingModule interfaces _) => return interfaces.applications.contains (interface, args)
    | _ =>
      -- a module whose members are being formed names what its declaration's bound names
      let instanceKey := (← get).table.allocatedKey! inst
      let found ← declaration instanceKey.declaration
      let some bound := Names.implementing? found | return false
      let moduleEnv := instanceEnv (← program) found instanceKey.arguments
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

  /-- The bounds of an instance, outermost scope first (SP3). A member call can check just
  the parameters introduced by the member. -/
  partial def checkBounds (env : Env) (found : Declaration) (name : String)
      (ownOnly : Bool := false) (skipMismatch : Bool := false) : CompileM Unit := do
    let state ← get
    let modules ← getModules
    for (reference, parameter) in deployedParameters state.program found do
      if ownOnly && some reference.scope != found.ownScope then continue
      let some value := env.values[reference]? | continue
      let some scope := modules.loweredScope? reference.scope
        | throw (.defect "a scope without its lowered form")
      let bound : Option Lowered.Bound := (scope.bounds[reference.index]?).getD none
      match bound with
      | none =>
        if let .type type := value then
          if isLinear (← get) type then
            if skipMismatch then throw .skipped
            refuse "SP3" parameter.name.span
              s!"`{renderType (← get) type}` is linear; `{parameter.name.text}` of `{name}` takes freely copied data: bound it `linear`"
      | some bound =>
        let scopeEnv := { env with file := (state.program.scopes[reference.scope]?).map (·.file) |>.getD env.file }
        for sort in bound.sorts do
          if let some failure ← meetsSort scopeEnv value sort then
            if skipMismatch then throw .skipped
            refuse "SP3" bound.span
              s!"{failure}, which `{parameter.name.text}` of `{name}` requires"

  /-- Whether a constraint holds at an instance; the text of the failure when it does not
  (SP4). Check specification conjuncts only when closing proof arguments (SP11). -/
  partial def checkConstraint (env : Env) (constraint : Lowered.Constraint) (owner : String)
      (specification : Bool := false) (deferProofArguments : Bool := false) : CompileM (Option String) := do
    let state ← get
    let constraintText ← sourceText env (constraintSpan constraint)
    let failed (here : String) : String :=
      s!"`{owner}` requires `{constraintText}`, which is `{here}` here and does not hold"
    match constraint with
    | .bound _ subject sorts =>
      if (← mentionsSpecParameter subject) != specification then return none
      let value ← evalAny env subject
      for sort in sorts do
        -- A deployed member has no proof arguments. Still check the interface application
        -- itself and every other sort in the bound before deciding applicability.
        let mismatch ← try meetsSort env value sort catch
          | .waiting why => do
            let .reference ref := sort | throw (.waiting why)
            unless deferProofArguments && why == unboundSpecificationParameter &&
                (← mentionsSpecParameter (.reference ref)) do throw (.waiting why)
            pure none
          | other => throw other
        if mismatch.isSome then
          return some (failed s!"{renderValue state value}: {← sourceText env (sortSpan sort)}")
      return none
    | .compare span operator left right =>
      if ((← mentionsSpecParameter left) || (← mentionsSpecParameter right)) != specification then return none
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
      (skip : Lowered.Constraint → CompileM Bool) (specification : Bool := false)
      (ownOnly : Bool := false) (deferProofArguments : Bool := false) : CompileM Unit := do
    let modules ← getModules
    let program ← program
    let scopes := if ownOnly then found.ownScope.toArray else found.scopes
    for scope in scopes do
      let some lowered := modules.loweredScope? scope | continue
      let scopeEnv := { env with file := (program.scopes[scope]?).map (·.file) |>.getD env.file }
      for constraint in lowered.constraints do
        if ← skip constraint then continue
        -- a constraint that cannot be evaluated here (it reads a member that a later layer
        -- gives) is not taken to hold: the instance waits for it (SP4)
        let outcome ← try checkConstraint scopeEnv constraint owner specification deferProofArguments
          catch failure => match failure with
            | .waiting reason => throw (.waiting s!"a constraint of its `where`: {reason}")
            | other => throw other
        if let some message := outcome then
          if isDefault then throw .skipped
          refuse "SP4" (constraintSpan constraint) message

  /-- The instance of a declaration at values, made once (SP7). -/
  partial def instantiate (id : DeclarationId) (values : Array StaticValue) (requested : Frame)
      (demand : InstanceDemand := .required) (specification : Array Nat := #[])
      (owner : Option InstanceId := none) : CompileM InstanceId := do
    let inst ← formInstance id values requested demand specification owner
    if demand == .required then observeApplication inst requested.span
    return inst

  /-- Form a signature without making the scheduler's enumeration an external member use. -/
  partial def formInstance (id : DeclarationId) (values : Array StaticValue) (requested : Frame)
      (demand : InstanceDemand := .required) (specification : Array Nat := #[])
      (owner : Option InstanceId := none) : CompileM InstanceId := do
    let isDefault := demand != .required
    let key : InstanceKey := { declaration := id, arguments := values, specification, owner }
    let description ← describeInstance id values specification owner
    let frame : ChainFrame :=
      { subject := .ofText (if demand == .defaultRoot then s!"default instance `{description}`" else description)
        span := requested.span }
    -- the request for the signature: entered in progress when it is new, and recorded with the
    -- request that makes it
    let requester ← currentRequest?
    let (inst, isNew) ← modifyGetResults fun results =>
      let table := results.signatures
      let results := { results with signatures := default }
      let (table, inst, isNew) := table.intern key frame requester
      let results := { results with signatures := table }
      let results := if isNew && demand == .defaultRoot then
        { results with defaultInstances := results.defaultInstances.insert inst } else results
      let results := match requester with
        | some requester => results.addRequest requester ⟨.signature, inst⟩
        | none => results
      ((inst, isNew), results)
    unless isNew do
      let found : Option (QueryState Typed.Signature) :=
        ((← getResults).signatures.entryAt? inst).map (·.state)
      let demand := modifyResults fun results =>
        { results.modifySignatures (·.reenter inst frame requester) with
          defaultInstances := results.defaultInstances.erase inst }
      match found with
      | some (.done (.data (.waits _ true))) => if isDefault then return inst else demand
      | some (.done _) => useQueryReads ⟨.signature, inst⟩; return inst
      | some .inProgress => refuseRecursion description requested.span
      | some (.exhausted exhaustion) => throw (.exhausted exhaustion)
      | some .skipped =>
        if isDefault then
          useQueryReads ⟨.signature, inst⟩
          throw .skipped
        demand
      | _ => throw .abandoned
    -- a request deeper than the budget of the chain is not computed: it is exhausted (SP10)
    if ← beyondDepth then
      let exhaustion ← logExhaustion .instantiationDepth frame
      modifyResults (·.modifySignatures (·.setState inst (.exhausted exhaustion)))
      throw (.exhausted exhaustion)
    try
      withRequest ⟨.signature, inst⟩ do
        let content ← instanceContent id inst values demand specification owner
        modifyResults (·.modifySignatures (·.setState inst (.done (.data content))))
        checkAppliedMember id inst values specification content
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
      (values : Array StaticValue) (demand : InstanceDemand) (specification : Array Nat := #[])
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
    checkBounds env found name (skipMismatch := demand matches .candidate _)
    checkWheres env found name (demand != .required) (hostDefinition env found)
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
    | .«module» node, _ =>
      let content ← moduleContent inst found node env demand
      if let .«module» (.concrete apps bindings) members := content then
        checkFormedMembers inst found env apps bindings members
      return content
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

  /-- Build the module's values and discharge the interface conditions that can read
  them through `Self`. An ineligible SP7 default skips before committing an SP8 owner. -/
  partial def moduleContent (inst : InstanceId) (found : Declaration)
      (node : Module) (env : Env) (demand : InstanceDemand) : CompileM InstanceContent := do
    let isDefault := demand != .required
    let state ← get
    let .«module» _ _ moduleName _ bound _ body := node
    let concrete : Bool := (realInstance state inst).run' {}
    let mut written : Array (AppliedInterface × Path) := #[]
    let mut seen : Std.HashSet AppliedInterface := {}
    if let some bound := bound then
      for sort in bound.sorts do
        if let .path path := sort then
          let app ← writtenInterface env path
          if state.sortNames.contains app.1 then
            refuse "SP3" path.span s!"`{moduleName.text}` names the sort `{state.program.nameOf app.1}`: only the vocabulary implements a sort"
          if concrete then
            if seen.contains app then continue
            seen := seen.insert app
          written := written.push (app, path)
    let applications := written.map Prod.fst
    let (bindings, conflict) ← bindModuleMembers written
    let conflict := if concrete then conflict else none
    let reject (c : MemberConflict) : CompileM Unit := do
      refuse "SP8" moduleName.span (c.message (← get) moduleName.text)
    let constrained := applications.any fun app => !(interfaceConstraints state app.1).isEmpty
    let interfaces := if concrete then ModuleInterfaces.concrete applications bindings else .ordered applications
    let complete := do
      let members ← moduleMemberValues found moduleName body env applications bindings
      return InstanceContent.«module» interfaces members
    let check (receiver : InstanceContent) (mode : InstanceDemand) := do
      modifyResults (·.modifySignatures (·.setState inst (.done (.data receiver))))
      moduleConditions inst moduleName.text applications mode
    if let .candidate required := demand then
      unless required.all applications.contains do
        -- Formation historically allocated the keys of members and interface conditions
        -- before testing the requested bound. Preserve those numbers for later packages.
        discard <| prepareModuleMembers do
          check (← complete) .required
          return none
        throw .skipped
    let decideEligibility := isDefault && (constrained || demand matches .candidate _)
    if let some c := conflict then
      unless decideEligibility do reject c
    if decideEligibility then
      try
        return ← withModuleConditions do
          -- A predicate can instantiate a member family at values that violate its
          -- contract. If the predicate excludes this default, only its truth is needed.
          let checkInTrial := constrained && bindings.entries.any fun binding =>
            let member := state.program.declarations[binding.declaration]!
            member.node matches .member (.typeMember _ _ (some _) (some _)) |
              .member (.protocolMember { staticParams := some _, .. })
          let prepared ← prepareModuleMembers do
            let content ← complete
            if checkInTrial then check content demand
            return some content
          if let some content := prepared then
            unless checkInTrial do check content demand
            if let some c := conflict then reject c
            return content
          -- A dependency computed with a provisional Self may have crossed this very
          -- instance. It cannot satisfy the actual formation or discharge its conditions.
          checkIsolatedConditions (reserveKeys := true) do
            check (.checkingModule interfaces bindings) demand
            if let some c := conflict then reject c
          let content ← complete
          check content demand
          return content
      catch
        | .waiting reason => return .waits reason true
        | failure => throw failure
    let content ← complete
    unless applications.isEmpty do
      if constrained then withModuleConditions (check content demand) else check content demand
    return content

  /-- The values defined by a suite or supplied by its binding. During default eligibility
  only the member requested through Self is read. Completed modules materialize every member. -/
  partial def moduleMemberValues (found : Declaration) (moduleName : Syntax.Name)
      (body : ModuleBody) (env : Env) (interfaces : Array AppliedInterface)
      (bindings : ModuleMemberBindings) (onlyMember : Option String := none) :
      CompileM (Array (String × MemberValue)) := do
    let state ← get
    let program := state.program
    let name := moduleName.text
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
              if onlyMember.any (· != memberName) then continue
              match ← evalAny env right with
              | .type type => members := members.push (memberName, .type type)
              | .natural value => members := members.push (memberName, .natural value)
              | .«module» other => members := members.push (memberName, .«module» other)
    if onlyMember.any (fun sought => members.any (·.1 == sought)) then return members
    let selected := match onlyMember with
      | some sought => (bindings.find? sought).toList.toArray
      | none => bindings.entries
    match body with
    | .primitive primitive =>
      let row := primitive.row.content
      let catalogue := (← getVocabulary).module? row
      if let some entry := catalogue then
        if let some implemented := entry.implements then
          let named := interfaces.map fun (interface, _) => qualifiedName program interface
          unless named.contains implemented do
            refuse "SP8" moduleName.span
              s!"`{name}` is bound to the row `{row}`, which implements `{implemented}`, not `{", ".intercalate named.toList}`"
        for (memberName, type) in entry.typeMembers do
          if onlyMember.all (· == memberName) then members := members.push (memberName, .type type)
        for (memberName, value) in entry.naturalMembers do
          if onlyMember.all (· == memberName) then members := members.push (memberName, .natural value)
      for binding in selected do
        unless (← declaration binding.declaration).kind == .functionMember do continue
        let name := program.nameOf binding.declaration
        let primitive := match catalogue with
          | some entry => (entry.standardFunctions.lookup name).getD s!"{row}.{name}"
          | none => if bindings.functionCounts[binding.application]! == 1 then row else s!"{row}.{name}"
        members := members.push (name, .row primitive)
      return members
    | .asset _ => return members
    | .suite _ =>
      let inner := found.inner.getD found.namespace
      let names := ((program.namespaces[inner]?).map (·.names)).getD {}
      for binding in selected do
        let (interface, args) := interfaces[binding.application]!
        let memberDeclaration ← declaration binding.declaration
        if memberDeclaration.kind == .lawMember then continue
        let memberName := program.nameOf binding.declaration
        let interfaceDeclaration ← declaration interface
        let interfaceName := program.nameOf interface
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
            let value ← thingValue env (.declarations #[(definition, none)] {}) (some .type) site (pure memberName) (selected := false)
            match value with
            | .type type => members := members.push (memberName, .type type)
            | _ => pure ()
          else members := members.push (memberName, .definition definition)
        | .naturalMember =>
          unless definitionDeclaration.kind == .staticName do wrong "a natural member"
          match ← thingValue env (.declarations #[(definition, none)] {}) (some .natural) site (pure memberName) (selected := false) with
          | .natural value => members := members.push (memberName, .natural value)
          | _ => pure ()
        | .moduleMember =>
          let value ← match definitionDeclaration.node with
            | .moduleMember moduleNode =>
              let term ← lowerWritten (Names.Written.pathExpr env.file moduleNode.path.span moduleNode.path)
              evalTerm env term .«module»
            | .«module» _ => thingValue env (.declarations #[(definition, none)] {}) (some .«module») site (pure memberName) (selected := false)
            | _ => do wrong "a module member"; throw .abandoned
          if let .«module» other := value then
            if let .member (.moduleMember _ _ memberBound) := memberDeclaration.node then
              let memberEnv : Env := { file := memberDeclaration.file, values := (instanceEnv program interfaceDeclaration args).values }
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
      if onlyMember.isSome then return members
      for member in (state.members[inner]?).getD #[] do
        let memberDeclaration ← declaration member
        let memberName := program.nameOf member
        if (memberDeclaration.kind == .functionDefinition || memberDeclaration.kind == .moduleDefinition)
            && !((bindings.find? memberName).any fun b =>
              (program.declarations[b.declaration]?).any (·.kind != .lawMember)) then
          let interfaceNames := ", ".intercalate (interfaces.toList.map fun (i, _) => program.nameOf i)
          refuse "SP8" ((memberDeclaration.name.map (·.span)).getD moduleName.span)
            (if interfaces.isEmpty then s!"`{name}` defines `{memberName}` as a member, and implements no interface"
            else s!"`{name}` defines `{memberName}`, which `{interfaceNames}` does not have")
      return members

  /-- A realized type member owes each written bound. Sort identity comes from name
  resolution and the vocabulary, including the derived Group sort of sized collections. -/
  partial def checkMemberType (member : Declaration) (type : ClosedType)
      (site : Span) (label : String) : CompileM Unit := do
    let .member (.typeMember _ _ _ (some bound)) := member.node | return
    let state ← get
    for sort in bound.sorts do
      match sort with
      | .linear _ => pure ()
      | .nat _ => refuse "SP8" site s!"{label}: a type cannot satisfy the bound `nat`"
      | .path path =>
        let steps ← stepsOf { file := member.file } path
        let some { step := .declaration id, .. } := steps.back?
          | refuse "SP8" site s!"{label}: the bound of a type must name a sort"
        let some sortName := state.sortNames[id]?
          | refuse "SP8" site s!"{label}: `{state.program.nameOf id}` is not a type sort"
        -- The vocabulary sorts are parameterless declarations in zkc::algebra.
        if steps.any (·.staticArgs.isSome) then
          refuse "SP8" path.span s!"{label}: the sort `{sortName}` takes no static arguments"
        unless hasSort (← getVocabulary) type sortName do
          refuse "SP8" site s!"{label}: `{renderType state type}` is not of sort `{sortName}`"

  /-- Compare the two source heads in their respective scopes. In particular types
  of both inputs and outputs must be equal; widening belongs to an application. -/
  partial def checkProtocolHead (member definition : DeclarationId)
      (expectedEnv actualEnv : Env) (site : Span) (label : String) : CompileM Unit := ProtocolHead.check do
    let modules ← getModules
    let program := modules.program
    let require := ProtocolHead.requireEqual site label
    let head (id : DeclarationId) : CompileM Lowered.ProtocolHead := do
      let some (Lowered.Content.protocol head ..) := (modules.lowered? id).map (·.content)
        | throw (.defect "missing lowered protocol head")
      pure head
    let expected ← head member
    let actual ← head definition
    let wrong (part : String) : CompileM Unit := refuse "SP8" site s!"{label}: the {part} differs"
    unless expected.roster == actual.roster do wrong "role roster"
    unless expected.specification == actual.specification do wrong "specification modifier"
    let scope (id : DeclarationId) := program.declarations[id]!.ownScope
    let evaluation : ProtocolHead.Evaluation := {
      asType, interface := evalInterface, text := sourceText
      arguments := fun id args span => do
        let params := deployedParameters program (← declaration id)
        let assigned ← assignWrittenWith (fun e cls => pure (e, cls)) id params {} args span
        requiredArguments id assigned span
      value := fun env expr cls => match cls with
        | some cls => evalTerm env expr cls
        | none => evalAny env expr }
    let left : ProtocolHead.Side := ⟨expectedEnv, scope member⟩
    let right : ProtocolHead.Side := ⟨actualEnv, scope definition⟩
    let sameSorts := ProtocolHead.sameSorts evaluation left right
    let sameTerm := ProtocolHead.sameTerm evaluation left right
    let params (id : DeclarationId) :=
      ((scope id >>= (program.scopes[·]?)).map (·.parameters)).getD #[]
    let lowered (id : DeclarationId) := scope id >>= modules.loweredScope?
    let expectedParams := params member
    let actualParams := params definition
    unless expectedParams.size == actualParams.size do wrong "static parameter count"
    let bounds (id : DeclarationId) := ((lowered id).map (·.bounds)).getD #[]
    for i in [:expectedParams.size] do
      let a := expectedParams[i]!
      let b := actualParams[i]!
      unless a.name.text == b.name.text && a.spec == b.spec do wrong "static parameter"
      let sorts (id : DeclarationId) := (((bounds id)[i]?.join).map (·.sorts)).getD #[]
      require s!"bound of `{a.name.text}`" (sameSorts (sorts member) (sorts definition))
    let sameType (a b : Lowered.TypeTerm) :=
      sameTerm (.type a) (.type b) (some .type)
    unless expected.ports.size == actual.ports.size do wrong "port count"
    for (a, b) in expected.ports.zip actual.ports do
      unless a.binder.name == b.binder.name && a.specification == b.specification &&
          a.isPrivate == b.isPrivate && a.holders == b.holders && a.readers == b.readers do
        wrong s!"port `{a.binder.name}`"
      require s!"port `{a.binder.name}`" (sameType a.type b.type)
    unless expected.results.size == actual.results.size do wrong "result count"
    for (a, b) in expected.results.zip actual.results do
      unless a.name.text == b.name.text && a.holders == b.holders && a.readers == b.readers do
        wrong s!"result `{a.name.text}`"
      require s!"result `{a.name.text}`" (sameType a.type b.type)
    let constraints (id : DeclarationId) := ((lowered id).map (·.constraints)).getD #[]
    let expectedWhere := constraints member
    let actualWhere := constraints definition
    unless expectedWhere.size == actualWhere.size do wrong "where clause"
    for (a, b) in expectedWhere.zip actualWhere do
      match a, b with
      | .compare _ op x y, .compare _ op' x' y' =>
        unless op == op' do wrong "where clause"
        require "where clause" (sameTerm x x' none)
        require "where clause" (sameTerm y y' none)
      | .bound _ x sorts, .bound _ y sorts' =>
        require "where clause" (sameTerm x y none)
        require "where clause" (sameSorts sorts sorts')
      | _, _ => wrong "where clause"

  /-- The completed table supplies Self, including members declared after the protocol.
  Optional defaults get here only after passing their eligibility and ownership checks. -/
  partial def checkFormedMembers (inst : InstanceId) (owner : Declaration) (env : Env)
      (apps : Array AppliedInterface) (bindings : ModuleMemberBindings)
      (members : Array (String × MemberValue)) : CompileM Unit := do
    let program ← program
    let definitions := program.namespaces[owner.inner.getD owner.namespace]!.names
    for (name, value) in members do
      let some binding := bindings.find? name | continue
      let member ← declaration binding.declaration
      unless (member.node matches .member (.typeMember _ _ _ (some _)) | .member (.protocolMember _)) do
        continue
      let (interface, args) := apps[binding.application]!
      let label := s!"`{owner.name.get!.text}::{name}` for `{program.nameOf interface}::{name}`"
      let site := ((do
        let .declaration id ← definitions[name]? | none
        program.declarations[id]?.bind (·.name)) <|> owner.name).get!.span
      match member.node, value with
      | .member (.typeMember _ _ _ (some _)), .type type => checkMemberType member type site label
      | .member (.protocolMember _), .definition id =>
        let expected := instanceEnv program member args
        checkIsolatedConditions do
          checkProtocolHead binding.declaration id { expected with self? := some (.«module» inst) }
            { env with self? := some (.«module» inst) } site label
      | _, _ => pure ()

  /-- A parameterized associated type or protocol has no single closed value at module
  formation. Check each realized signature, including a path directly to its definition. -/
  partial def checkAppliedMember (id : DeclarationId) (inst : InstanceId)
      (values : Array StaticValue) (specification : Array Nat) (content : InstanceContent) :
      CompileM Unit := do
    let state ← get
    let program := state.program
    let found := program.declarations[id]!
    unless found.kind == .protocol ||
        [.alias, .vocabularyType, .record, .«variant», .specType].contains found.kind do return
    let some own := found.ownScope >>= (program.scopes[·]?) | return
    if own.parameters.isEmpty then return
    if content matches .waits .. then return
    let ns := program.namespaces[found.namespace]!
    let owner := program.declarations[ns.owner]!
    let some bound := Names.implementing? owner | return
    let name := program.nameOf id
    let env := instanceEnv program found values specification
    for (interface, _) in ← boundInterfaces { file := owner.file } bound do
      let inner := program.declarations[interface]!.inner.getD 0
      let some (.declaration memberId) := program.namespaces[inner]!.names[name]? | continue
      let member := program.declarations[memberId]!
      unless (member.node matches .member (.typeMember _ _ _ (some _)) | .member (.protocolMember _)) do
        continue
      let ownerArgs := values.extract 0 (deployedParameters program owner).size
      if let some receiver := state.table.find? { declaration := ns.owner, arguments := ownerArgs } then
        if state.table.content? receiver matches some (.checkingModule ..) then
          -- This signature is discarded with the isolated eligibility trial. A selected
          -- module evaluates the predicate again with the completed receiver.
          return
      let concrete : Bool := (realInstance state inst).run' {}
      unless concrete do return
      let label := s!"`{program.nameOf ns.owner}::{name}` for `{program.nameOf interface}::{name}`"
      let site := found.name.get!.span
      match member.node with
      | .member (.typeMember _ _ _ (some _)) =>
        if found.kind == .protocol then return -- formation diagnoses the member kind
        let .type type ← valueOfInstance id inst | throw (.defect "expected a realized type member")
        checkMemberType member type site label
      | .member (.protocolMember _) =>
        unless found.kind == .protocol do return
        checkIsolatedConditions do
          let receiver ← formInstance ns.owner ownerArgs ⟨"", site⟩
          if let some (.waits why _) := (← get).table.content? receiver then throw (.waiting why)
          let some (.«module» interfaces _) := (← get).table.content? receiver
            | throw (.waiting "the implementing module of a protocol member")
          let some (_, required, decl, args) := declaredMember? program interfaces name
            | throw (.defect "missing protocol member of a formed module")
          let mut expected := instanceEnv program decl args
          -- Only corresponding member binders travel between the two scopes. A
          -- specification parameter of the module has no positional slot in the interface.
          if let (some left, some right) := (decl.ownScope, found.ownScope) then
            for i in [:own.parameters.size] do
              if let some value := env.values[(⟨right, i⟩ : ParameterRef)]? then
                expected := { expected with values := expected.values.insert ⟨left, i⟩ value }
          checkProtocolHead required id { expected with self? := some (.«module» receiver) }
            { env with self? := some (.«module» receiver) } site label
          return
      | _ => pure ()

  /-- The conditions that the interfaces of a module instance put on it: the bounds of their
  parameters and their `where` (SP3, SP4). -/
  partial def moduleConditions (inst : InstanceId) (moduleName : String)
      (interfaces : Array AppliedInterface) (demand : InstanceDemand) : CompileM Unit := do
    let state ← get
    let program := state.program
    for (interface, args) in interfaces do
      let interfaceDeclaration ← declaration interface
      let interfaceEnv : Env :=
        { instanceEnv program interfaceDeclaration args with self? := some (.«module» inst) }
      checkBounds interfaceEnv interfaceDeclaration (program.nameOf interface)
        (skipMismatch := demand matches .candidate _)
      for constraint in interfaceConstraints state interface do
        -- a constraint of an interface that cannot be evaluated here is not taken to hold:
        -- the module instance waits for it (SP4)
        let outcome ← try checkConstraint interfaceEnv constraint moduleName
          catch failure => match failure with
            | .waiting reason => throw (.waiting s!"a constraint of `{program.nameOf interface}`: {reason}")
            | other => throw other
        if let some message := outcome then
          if demand != .required then throw .skipped
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
    (scopes : StaticEnvironment) (place : Span) :
    CompileM StaticEnvironment := do
  assignArguments env (← lowerSteps env steps) scopes place

/-- Whether a constraint as written holds: lowered first. -/
def checkWrittenConstraint (env : Env) (constraint : Constraint) (owner : String) :
    CompileM (Option String) := do
  let lowered ← lowerWritten (Names.Written.constraint env.file constraint)
  checkConstraint env lowered owner

end Zkc.Frontend.Static
