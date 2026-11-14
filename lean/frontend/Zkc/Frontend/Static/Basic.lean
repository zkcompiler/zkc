module

public import Zkc.Frontend.Names.Written
public import Zkc.Frontend.Semantics.Instance
public import Zkc.Frontend.Semantics.VocabularyTable
public import Zkc.Frontend.Syntax.Printer
public import Zkc.Frontend.Syntax.Parser
public import Zkc.Frontend.Basic.CompileM

@[expose] public section

set_option autoImplicit false

/-!
# The static layer

The evaluation of static terms, the binding and inference of static arguments, and the closed
signature of a declaration at static values (SP3 to SP7). It sits below elaboration: a body
evaluates the types and static terms it meets in the static environment of its instance.

Static values and instances are computed in the bottom layer, `CompileM`: its state holds the
store of files (the program, its resolutions and its indexes), the store of results (the table
of signatures, which numbers the instances, and the tables of typing), the log of diagnostics,
and the stack of what is being computed, from which the chain of a diagnostic is read (SP7). A
refusal is logged when it is made, with the chain, and the item it ends is `abandoned`; what this
layer does not evaluate (a generated member, a specification-only parameter) `waits` and refuses
nothing.

The entry points:

- in `Zkc.Frontend.Static.Evaluate`: `instantiate` (a declaration at values, from a place: a
  request for its signature), `bindArguments` (the values that a reference gives a
  declaration), `evalType`, `evalTerm` and `evalSize` (a type or a static term in an
  environment), `memberOfValue` (a member of a static thing at an instance), `instanceEnv` (the
  environment of an instance);
- in `Zkc.Frontend.Static.Infer`: the inference of SP6, `startProblem`, `matchType` per
  argument and for the result, `retry`, `finish`.
-/

namespace Zkc.Frontend.Compile.State

/-- The table of signatures, whose entries are the instances. -/
def table (state : Compile.State) : QueryTable InstanceKey Typed.Signature := state.env.results.signatures

def resolutions (state : Compile.State) : Resolutions := state.env.modules.resolutions

def sortNames (state : Compile.State) : Std.HashMap DeclarationId String := state.env.modules.indexes.sortNames

def members (state : Compile.State) : Std.HashMap NamespaceId (Array DeclarationId) :=
  state.env.modules.indexes.members

def rowNames (state : Compile.State) : Std.HashMap String String := state.env.modules.indexes.rowNames

def scopeOwners (state : Compile.State) : Std.HashMap ScopeId DeclarationId :=
  state.env.modules.indexes.scopeOwners

def implementers (state : Compile.State) : Std.HashMap DeclarationId (Array DeclarationId) :=
  state.env.modules.indexes.implementers

/-- The instances asked for by the roots, the comments `// instantiate:` and the default
instances (SP7), in the order they were asked for. -/
def roots (state : Compile.State) : Array InstanceId := state.env.results.roots.map (·.1)

def schemes (state : Compile.State) : Array SchemeEntry := state.env.results.schemes

def reports (state : Compile.State) : Array String := state.env.results.reports

def defaults (state : Compile.State) : Array DefaultReport := state.env.results.defaults

end Zkc.Frontend.Compile.State

namespace Zkc.Frontend.QueryTable

/-- The content of an instance whose signature is done. -/
def content? (table : QueryTable InstanceKey Typed.Signature) (id : InstanceId) :
    Option InstanceContent :=
  match table.entries[id]? with
  | some { state := .done (.data content), .. } => some content
  | _ => none

end Zkc.Frontend.QueryTable

namespace Zkc.Frontend.Static

open Syntax
open Names (segmentsOf segmentArgs segmentName)

/-- What a static term is classified as, by the parameter it is bound to (GR5). -/
inductive Class where
  | type
  | natural
  | «module»
  deriving Inhabited, BEq

/-- A static environment: the values of the parameters in scope, `Self` in an interface, and
the file whose table of resolutions the syntax being evaluated is read with. In a body, the
static names in scope and the indices of loops over static ranges that are typed as run-time
naturals (TY2, TY10). -/
structure Env where
  file : FileId
  values : StaticEnvironment := {}
  self? : Option StaticValue := none
  /-- The static names in scope, by name, with their values. -/
  locals : Std.HashMap String Nat := {}
  /-- The indices of loops typed per iteration that are in scope, by name. -/
  indices : Std.HashSet String := {}
  deriving Inhabited




def program : CompileM Program := return (← get).program

def declaration (id : DeclarationId) : CompileM Declaration := do
  match (← get).program.declarations[id]? with
  | some value => return value
  | none => throw (.waiting "an unknown declaration")

def nameOf (id : DeclarationId) : CompileM String := return (← get).program.nameOf id

/-- Records a refusal at the current chain, once per place and rule, and abandons the item. -/
def refuse {α : Type} (rule : String) (span : Span) (message : String) : CompileM α :=
  throwError rule span (.ofText message) (origin := .instances)

/-- Adds a root of a kind. -/
def addRoot (inst : InstanceId) (kind : Emit.EntryKind := .root) : CompileM Unit :=
  modifyResults (·.addRoot inst kind)

/-- The number of a row of the table, entered when new. -/
def internRow (row : Typing.Row) : CompileM Typing.RowId :=
  modifyGetResults fun results =>
    let (results, id) := results.internRow row
    (id, results)

/-- Reports a text once. -/
def report (text : String) : CompileM Unit :=
  modifyResults fun results =>
    if results.reports.contains text then results
    else { results with reports := results.reports.push text }

/-- Whether a file is one of the package: given, not read from the library. -/
def inPackage (program : Program) (file : FileId) : Bool :=
  (program.files[file]?).any (!·.fromLibrary)

/-! ## Text -/

def exprText (expr : Expr) : String :=
  Layout.flatten (Printer.atoms (Printer.expr expr))

def typeText (type : TypeExpr) : String :=
  Layout.flatten (Printer.atoms (Printer.typeExpr type))

/-- An expression without the parentheses around it. -/
partial def withoutParentheses : Expr → Expr
  | .paren _ inner => withoutParentheses inner
  | other => other

/-- The bytes of the source at a place, from the record of the file the place names. -/
def sourceBytes (place : Span) : CompileM (Option ByteArray) := do
  let some record := (← getModules).records.find? (·.source.name == place.file) | return none
  let bytes := record.source.tree.source
  if place.stopByte.toNat ≤ bytes.size && place.startByte ≤ place.stopByte then
    return some (bytes.extract place.startByte.toNat place.stopByte.toNat)
  return none

/-- The expression written at a place as a message quotes it: the canonical text of the
expression that the source holds there, or the source as written when it holds none. -/
def textAt (place : Span) : CompileM String := do
  let some bytes ← sourceBytes place | return "?"
  match parseExprBytes place.file bytes with
  | .ok expr => return exprText (withoutParentheses expr)
  | .error _ => return (String.fromUTF8? bytes).getD "?"

mutual
  /-- A closed type as a message writes it. -/
  partial def renderType (state : Compile.State) : ClosedType → String
    | .bool => "bool"
    | .nat => "nat"
    | .rational => "rational"
    | .index bound => s!"index<{bound}>"
    | .nonzero field => s!"nonzero<{renderType state field}>"
    | .seq element (some size) => s!"[{renderType state element}; {size}]"
    | .seq element none => s!"[{renderType state element}]"
    | .tuple components names =>
      let parts := (components.zip names).map fun (component, name) =>
        match name with
        | some name => s!"{name}: {renderType state component}"
        | none => renderType state component
      s!"({", ".intercalate parts.toList})"
    | .nominal row arguments =>
      let name := (state.rowNames[row]?).getD row
      if arguments.isEmpty then name
      else s!"{name}<{", ".intercalate (arguments.toList.map (renderValue state))}>"
    | .record id | .variant id | .specification id => renderInstance state id
    | .opaque «module» member arguments _ =>
      -- `X::T`: the parameter that the module stands for, and the member
      let parameter := ((state.table.entries[«module»]?).bind (·.key.opaqueFor)).bind fun (reference, _) =>
        ((state.program.scopes[reference.scope]?).bind (·.parameters[reference.index]?)).map (·.name.text)
      let base := s!"{parameter.getD "?"}::{member}"
      if arguments.isEmpty then base
      else s!"{base}<{", ".intercalate (arguments.toList.map (renderValue state))}>"

  partial def renderValue (state : Compile.State) : StaticValue → String
    | .type type => renderType state type
    | .natural value => toString value
    | .module id => renderInstance state id

  /-- An instance as `name<values>`, positionally, then its specification-only values by name. -/
  partial def renderInstance (state : Compile.State) (id : InstanceId) : String :=
    match state.table.entries[id]? with
    | some entry =>
      let name := state.program.nameOf entry.key.declaration
      let specNames := ((state.program.declarations[entry.key.declaration]?).map fun found =>
        ((state.program.parameters found).filter (·.2.spec)).map (·.2.name.text)).getD #[]
      let parts := entry.key.arguments.toList.map (renderValue state) ++
        (specNames.zip entry.key.specification).toList.map fun (parameter, value) =>
          s!"spec {parameter} = {value}"
      let base := if parts.isEmpty then name else s!"{name}<{", ".intercalate parts}>"
      match entry.key.owner with
      | some owner => s!"{base} at {renderInstance state owner}"
      | none => base
    | none => "?"
end

def renderTypeM (type : ClosedType) : CompileM String := return renderType (← get) type

/-! ## The budget of static evaluation -/

/-- Spends steps of the evaluation of a static term: one per node, and for a product and a
power as many as the size of their result asks (a step for every 1,024 bits), so that the
budget bounds the size of a static natural as it bounds the steps. Past the budget of static evaluation the evaluation stops, and the check is
incomplete (TY2). `subject` is the term as a message names it. -/
def spendStatic (place : Span) (subject : CompileM String) (cost : Nat := 1) : CompileM Unit := do
  let spent := (← get).staticSteps + cost
  modify fun state => { state with staticSteps := spent }
  if (← read).options.budgets.staticEvaluation < spent then
    let text ← subject
    let exhaustion ← logExhaustion .staticEvaluation { subject := .ofText text, span := place }
    throw (.exhausted exhaustion)

/-- Runs an evaluation of a static term: the outermost one starts the count of its steps, and
the evaluations it makes on the way count towards it. -/
def withStaticEvaluation {α : Type} (action : CompileM α) : CompileM α := do
  let depth := (← get).staticDepth
  modify fun state => { state with
    staticDepth := depth + 1
    staticSteps := if depth == 0 then 0 else state.staticSteps }
  tryFinally action (modify fun state => { state with staticDepth := depth })

/-- What the size of a static natural costs: a step for every 1,024 bits. The budget of static
evaluation then bounds a natural at 2^30 bits. -/
def sizeCost (value : Nat) : Nat := value.log2 / 1024 + 1

/-- The product of two static naturals. It costs the size of its result, and is not computed
when the budget does not allow it. -/
def staticProduct (place : Span) (subject : CompileM String) (a b : Nat) : CompileM Nat := do
  spendStatic place subject (cost := sizeCost a + sizeCost b)
  return a * b

/-- The power of two static naturals. A power that the source writes costs its exponent, and
every power costs the size of its result; it is not computed when the budget does not allow
them: a power whose result no machine holds leaves the check incomplete. -/
def staticPower (place : Span) (subject : CompileM String) (a b : Nat) (written : Bool := true) :
    CompileM Nat := do
  let size := if a ≤ 1 then 1 else b * (a.log2 + 1) / 1024 + 1
  spendStatic place subject (cost := if written then b + size else size)
  return a ^ b

def renderValueM (value : StaticValue) : CompileM String := return renderValue (← get) value

/-! ## Declarations and parameters -/

/-- The static parameters of a declaration's chain that are not specification-only, outermost
first: the parameters of its instances (SP7, SP11). -/
def deployedParameters (program : Program) (declaration : Declaration) :
    Array (ParameterRef × StaticParam) :=
  (program.parameters declaration).filter fun (_, parameter) => !parameter.spec

/-- The specification-only static parameters of a declaration's chain, outermost first (SP11). -/
def specificationParameters (program : Program) (declaration : Declaration) :
    Array (ParameterRef × StaticParam) :=
  (program.parameters declaration).filter fun (_, parameter) => parameter.spec

/-- The static parameters of a declaration's own scope: those of an interface member, which its
definitions in implementing modules read under the interface's names (SP8). -/
def ownParameters (program : Program) (declaration : Declaration) : Array ParameterRef :=
  match declaration.ownScope with
  | some scope =>
    let parameters := ((program.scopes[scope]?).map (·.parameters)).getD #[]
    ((List.range parameters.size).toArray.filter fun index => !parameters[index]!.spec).map
      fun index => ⟨scope, index⟩
  | none => #[]

/-- An instance as a frame writes it: `name<p = v, …, spec e = v>`. -/
def describeInstance (declarationId : DeclarationId) (values : Array StaticValue)
    (specification : Array Nat := #[]) (owner : Option InstanceId := none) : CompileM String := do
  let state ← get
  let program := state.program
  let some found := program.declarations[declarationId]? | return "?"
  let parameters := deployedParameters program found
  let name := program.nameOf declarationId
  let parts := (parameters.zip values).map fun ((_, parameter), value) =>
    s!"{parameter.name.text} = {renderValue state value}"
  let specParts := ((specificationParameters program found).zip specification).map
    fun ((_, parameter), value) => s!"spec {parameter.name.text} = {value}"
  let base := if values.isEmpty && specification.isEmpty then name
    else s!"{name}<{", ".intercalate (parts ++ specParts).toList}>"
  match owner with
  | some inst => return s!"{base} at {renderInstance state inst}"
  | none => return base

/-- The kind and the qualified path of an interface, `zkc::hash::Hash`. -/
def qualifiedName (program : Program) (id : DeclarationId) : String := Id.run do
  let mut names : Array String := #[program.nameOf id]
  let mut current := (program.declarations[id]?).map (·.namespace)
  for _ in [0:program.namespaces.size] do
    let some ns := current | break
    let some entry := program.namespaces[ns]? | break
    let some owner := program.declarations[entry.owner]? | break
    if owner.kind == .fileModule then
      names := names.push (program.nameOf entry.owner)
      break
    names := names.push (program.nameOf entry.owner)
    current := entry.parent
  return "::".intercalate names.reverse.toList

/-- The resolution of a path, read from the table of the file of the environment. -/
def stepsOf (env : Env) (path : Path) : CompileM (Array ResolvedSegment) := do
  match (← get).resolutions.find? env.file path with
  | some resolution => return resolution.segments
  | none => throw .abandoned

/-- The interfaces that a bound names, read from the resolutions; `nat` and `linear` are not. -/
def boundInterfaces (env : Env) (bound : Bound) : CompileM (Array (DeclarationId × Path)) := do
  let mut result := #[]
  for sort in bound.sorts do
    if let .path path := sort then
      let steps ← stepsOf env path
      if let some { step := .declaration id, .. } := steps.back? then
        result := result.push (id, path)
  return result

/-- What a static parameter is: a type, a natural or a module (SP3). -/
def parameterClass (reference : ParameterRef) : CompileM Class := do
  let state ← get
  let some scope := state.program.scopes[reference.scope]? | return .type
  let some parameter := scope.parameters[reference.index]? | return .type
  if parameter.spec then return .natural
  let some bound := parameter.bound | return .type
  if bound.sorts.any (fun | .nat _ => true | _ => false) then return .natural
  let interfaces ← recover (boundInterfaces { file := scope.file } bound) (pure #[])
  if interfaces.any (fun (id, _) => !state.sortNames.contains id) then return .«module»
  return .type

/-- The paths of a static term or an expression, static arguments included. -/
partial def exprPaths : Expr → Array Path
  | .path _ path => pathPaths path
  | .call _ callee args => pathPaths callee ++ callArgsPaths args
  | .record _ type fields => pathPaths type ++ fields.foldl (init := #[]) fun acc field =>
      match field with
      | .fieldInit _ _ (some value) => acc ++ exprPaths value
      | _ => acc
  | .ifExpr _ a b c => exprPaths a ++ exprPaths b ++ exprPaths c
  | .orExpr _ a b | .andExpr _ a b | .compare _ _ a b | .sum _ _ a b | .product _ _ a b
  | .power _ a b | .innerProduct _ _ a b | .index _ a b | .repetition _ a b =>
    exprPaths a ++ exprPaths b
  | .notExpr _ a | .unary _ a | .paren _ a | .field _ a _ | .position _ a _ => exprPaths a
  | .method _ target _ staticArgs args =>
    exprPaths target ++ ((staticArgs.map staticArgsPaths).getD #[]) ++ callArgsPaths args
  | .slice _ a lower upper =>
    exprPaths a ++ ((lower.map exprPaths).getD #[]) ++ ((upper.map exprPaths).getD #[])
  | .tuple _ components => components.foldl (init := #[]) fun acc (.component _ _ value) =>
      acc ++ exprPaths value
  | .list _ elements => elements.foldl (init := #[]) fun acc element => acc ++ exprPaths element
  | .comprehension _ element _ (.domain _ start stop) filter =>
    exprPaths element ++ exprPaths start ++ ((stop.map exprPaths).getD #[]) ++
      ((filter.map exprPaths).getD #[])
  | .recordUpdate _ value fields => fields.foldl (init := exprPaths value) fun acc
      (.fieldUpdate _ _ value) => acc ++ exprPaths value
  | .binderForm _ _ _ _ (.domain _ start stop) body =>
    exprPaths start ++ ((stop.map exprPaths).getD #[]) ++ exprPaths body
  | .indexType _ size => exprPaths size
  | .nonzeroType _ type => typePaths type
  | .number _ | .byteString _ | .trueLiteral _ | .falseLiteral _ | .unit _ | .boolType _
  | .natType _ | .rationalType _ => #[]
where
  pathPaths (path : Path) : Array Path :=
    (segmentsOf path).foldl (init := #[path]) fun acc segment =>
      match segmentArgs segment with
      | some args => acc ++ staticArgsPaths args
      | none => acc
  staticArgsPaths : StaticArgs → Array Path
    | .staticArgs _ args => args.foldl (init := #[]) fun acc arg =>
        match arg with
        | .term _ _ term | .spec _ _ term => acc ++ exprPaths term
        | .inferred _ _ => acc
  callArgsPaths : CallArgs → Array Path
    | .callArgs _ arguments witnesses =>
      (arguments ++ witnesses.getD #[]).foldl (init := #[]) fun acc argument =>
        match argument with
        | .positional _ value | .named _ _ value | .spec _ _ value => acc ++ exprPaths value
  typePaths : TypeExpr → Array Path
    | .path _ path => pathPaths path
    | .index _ size => exprPaths size
    | .nonzero _ type => typePaths type
    | .sequence _ element size => typePaths element ++ ((size.map exprPaths).getD #[])
    | .tuple _ fields => fields.foldl (init := #[]) fun acc (.tupleField _ _ type) =>
        acc ++ typePaths type
    | .bool _ | .nat _ | .rational _ => #[]

/-- Whether a type is one of a sort, by the vocabulary; a sized collection of elements of a
`Group` is a `Group` (TY11). -/
partial def hasSort (vocabulary : Vocabulary) (type : ClosedType) (sort : String) : Bool :=
  match type with
  | .nominal row _ => (vocabulary.type? row).any (·.sorts.contains sort)
  | .opaque _ _ _ sorts => sorts.contains sort
  | .seq element (some _) => sort == "Group" && hasSort vocabulary element "Group"
  | _ => false

/-- The sorts of a type, for messages. -/
def sortsOf (vocabulary : Vocabulary) (type : ClosedType) : Array String :=
  match type with
  | .nominal row _ => ((vocabulary.type? row).map (·.sorts)).getD #[]
  | .opaque _ _ _ sorts => sorts
  | .seq element (some _) => if hasSort vocabulary element "Group" then #["Group"] else #[]
  | _ => #[]

end Zkc.Frontend.Static
