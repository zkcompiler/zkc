module

public import Zkc.Frontend.Names.Lookup
public import Zkc.Frontend.Names.Forms

@[expose] public section

set_option autoImplicit false

/-!
# Resolution and lowering of paths, types, expressions, patterns and statements

Every `Path` of a production is resolved and lowered in one act: its steps, with the static
arguments written on them lowered in turn, become a reference of the lowered form, or a refusal
and an error node. A use of a local name becomes the number of its binder. A single name that is
not bound where a value stands, and that some variant of the program has as an alternative, is a
bare alternative: typing completes it with the type expected there, and refuses it by NL3 when
that type has no such alternative. A dot call, an operator and a mathematical form need the type
of an expression and stay unresolved nodes. A record constructed or matched by a record pattern
outside the module that declares it is refused when one of its fields is not `pub` (NL7).

Local names are bound in suites (NL2): a binding is refused when the name is already bound in an
enclosing suite or is a static parameter in scope. A suite that ends takes its names with it, so
two sibling suites may bind one name.

The derived forms that need no type are written in their kernel forms: `else if` is an `if` in
the `else`, `and` and `or` are conditionals that remember how they were written, a pattern is one
`unpack` per level with binders that lowering makes, both spellings of a mathematical form are
one node, `T{f}` is `T{f = f}`, a role is its place in the roster. The events of a protocol are
numbered in the order of the text, depth first (EV3). Three marks say where a term is static by
its form: a binding of one name to a size is a static name (TY2), a condition built from
comparisons of sizes is static (TY9), and the index of a range that stands in a size, a static
argument or a bound of a slice in the body is typed per iteration (TY10). A statement of a later
layer waits, and keeps its names resolved.
-/

namespace Zkc.Frontend.Names

open Syntax
open Lowered (Binder)

/-- The written static arguments on the last of the steps of a segment. Arguments that an
import fixed and arguments written again are refused (SP2). -/
def attachArgs (segments : Array WrittenSegment) (args : Option StaticArgs) (name : Name) :
    Except Diagnostic (Array WrittenSegment) :=
  match args, segments.back? with
  | none, _ | _, none => .ok segments
  | some written, some last =>
    if last.staticArgs.isSome then
      .error (refusal "SP2" name.span
        s!"`{name.text}` stands for a path whose static arguments its `use` fixes; it takes no more")
    else
      .ok (segments.modify (segments.size - 1) fun last =>
        { last with staticArgs := some written, fixedBy := none })

def staticArgList : StaticArgs → Array StaticArg
  | .staticArgs _ args => args

/-- The module that a declaration is declared in, as a message names it. -/
def homeName (program : Program) (declaration : Declaration) : String :=
  match program.namespaces[declaration.namespace]? with
  | some ns => program.nameOf ns.owner
  | none => ""

/-- Whether a record has a field that is not `pub`. -/
def hasPrivateField (declaration : Declaration) : Bool :=
  match declaration.node with
  | .struct node => node.fields.any (!·.pub)
  | _ => false

def goalWords : Array String :=
  #["written", "committed", "constructed", "serialized", "fixed", "adaptive", "hidden", "observed",
    "residual"]

/-- A reference of one step, without arguments. -/
def oneStep (span : Span) (step : Step) : Lowered.Reference :=
  .reference span #[.segment step none none]

/-- The lowered node of a name or a path that resolved to steps: a local name as its binder, a
path as its reference. -/
def localOrReference (span : Span) (reference : Lowered.Reference) (name : Option String) :
    ResolveM Lowered.Expr := do
  match reference with
  | .reference _ #[.segment .«local» _ _] =>
    match name.bind ((← get).locals[·]?) with
    | some binding => return .local span binding.binder
    | none => return .error span
  | _ => return .reference reference

/-- Numbers an event in the order of the text. -/
def numberEvent (span : Span) (name : Option String) (parts : Array String) : ResolveM EventId := do
  let state ← get
  set { state with events := state.events.push { span, name, parts } }
  return state.events.size

/-- The shape of a pattern, with its binders made in the order of the text. -/
inductive PatternTree where
  /-- A name, or `_` as a binder that lowering makes, at its place. -/
  | binder (binder : Option Binder)
  | tuple (span : Span) (items : Array PatternTree)
  | record (span : Span) (type : Lowered.Reference) (declaration : DeclarationId)
      (fields : Array (Span × String)) (items : Array PatternTree)
  deriving Inhabited

/-- The levels that take a value apart along a pattern, outermost first: one `unpack` per level,
a nested pattern taking apart a value that lowering makes. -/
partial def unpackTree (tree : PatternTree) (value : Lowered.Expr) (roles : Option RoleSet) :
    ResolveM (Array Lowered.Stmt) := do
  let level (items : Array PatternTree) : ResolveM (Array (Option Binder) × Array (PatternTree × Binder)) := do
    let mut binders := #[]
    let mut inner := #[]
    for item in items do
      match item with
      | .binder binder => binders := binders.push binder
      | nested =>
        let span := match nested with
          | .tuple span _ | .record span .. => span
          | .binder _ => default
        let made ← madeBinder span .patternValue
        binders := binders.push (some made)
        inner := inner.push (nested, made)
    return (binders, inner)
  match tree with
  | .binder _ => return #[]
  | .tuple span items =>
    let (binders, inner) ← level items
    let mut statements := #[Lowered.Stmt.unpack span (.tuple items.size) binders roles value]
    for (nested, made) in inner do
      statements := statements ++ (← unpackTree nested (.local span made.id) roles)
    return statements
  | .record span type declaration fields items =>
    let (binders, inner) ← level items
    let mut statements :=
      #[Lowered.Stmt.unpack span (.record type declaration fields) binders roles value]
    for (nested, made) in inner do
      statements := statements ++ (← unpackTree nested (.local span made.id) roles)
    return statements

mutual
  /-- Resolves a path: what it stands for, and the reference of the lowered form when it
  resolved. -/
  partial def resolvePath (env : Env) (path : Path) (position : Position) :
      ResolveM (Target × Option Lowered.Reference) := do
    let segments := segmentsOf path
    let some first := segments[0]? | return (.poisoned, none)
    let firstName := segmentName first
    match ← lookupFirst env firstName .full with
    | none =>
      let mut firstArgs : Option (Array Lowered.StaticArgument) := none
      for index in [0:segments.size] do
        if let some args := segmentArgs segments[index]! then
          let lowered ← resolveStaticArgs env args
          if index == 0 then firstArgs := some lowered
      if position == .value && segments.size == 1 &&
          (← get).alternatives.contains firstName.text then
        return (.value, some (.reference path.span #[.segment (.bareAlternative firstName.text) firstArgs none]))
      refuseAt env.owner "NL3" firstName.span
        s!"`{firstName.text}` is not bound: it is no local name, static parameter, declaration or import of this module"
      return (.poisoned, none)
    | some found =>
      let mut target := found.target
      let mut resolved := found.segments
      -- the lowered arguments written on this path, by the place in `resolved` they stand at
      let mut written : Std.HashMap Nat (Array Lowered.StaticArgument) := {}
      let mut failed := false
      match attachArgs resolved (segmentArgs first) firstName with
      | .ok next => resolved := next
      | .error refused => refuse env.owner refused; failed := true
      if let some args := segmentArgs first then
        let lowered ← resolveStaticArgs env args
        unless failed do written := written.insert (resolved.size - 1) lowered
      for index in [1:segments.size] do
        let current := segments[index]!
        let name := segmentName current
        if failed then
          if let some args := segmentArgs current then discard <| resolveStaticArgs env args
          continue
        let before := target
        match ← step env target name (pathPrefixText path (index - 1)) with
        | .error refused =>
          refuse env.owner refused
          failed := true
          if let some args := segmentArgs current then discard <| resolveStaticArgs env args
        | .ok next =>
          match attachArgs next.segments (segmentArgs current) name with
          | .error refused => refuse env.owner refused; failed := true
          | .ok attached => resolved := resolved ++ attached
          target := next.target
          if let some args := segmentArgs current then
            let roles ← rolesOf before next.segments
            let lowered ← if roles.isEmpty then resolveStaticArgs env args
              else resolveRoleArgs env roles args
            unless failed do written := written.insert (resolved.size - 1) lowered
      if failed then return (.poisoned, none)
      match target with
      | .poisoned => return (.poisoned, none)
      | _ => return (target, some (← lowerSegments env path.span resolved written))

  /-- The reference of found steps, with the arguments written on the path lowered, and those
  that an import fixes lowered once in the import's environment. -/
  partial def lowerSegments (env : Env) (span : Span) (resolved : Array WrittenSegment)
      (written : Std.HashMap Nat (Array Lowered.StaticArgument)) : ResolveM Lowered.Reference := do
    let mut lowered := #[]
    for index in [0:resolved.size] do
      let segment := resolved[index]!
      let arguments ← match written[index]?, segment.staticArgs, segment.fixedBy with
        | some args, _, _ => pure (some args)
        | none, some args, some importId => pure (some (← importArguments importId args))
        | none, some args, none => pure (some (← resolveStaticArgs env args))
        | none, none, _ => pure none
      lowered := lowered.push (Lowered.Segment.segment segment.step arguments segment.fixedBy)
    return .reference span lowered

  /-- The static arguments of the path of a `use`, lowered once in the environment of the
  import. -/
  partial def importArguments (importId : ImportId) (args : StaticArgs) :
      ResolveM (Array Lowered.StaticArgument) := do
    let state ← get
    let some entry := state.program.imports[importId]? | return #[]
    let .staticArgs span _ := args
    if let some lowered := state.importArguments[(entry.file, span.startByte)]? then return lowered
    -- not lowered yet: the import is reached before its own `use` is resolved
    let lowered ← resolveStaticArgs (importEnv state.program importId) args
    modify fun state => { state with
      importArguments := state.importArguments.insert (entry.file, span.startByte) lowered }
    return lowered

  /-- The roster whose roles the arguments of `Inputs`, `Coins` and `Received` name (§8). -/
  partial def rolesOf (before : Target) (segments : Array WrittenSegment) :
      ResolveM (Array String) := do
    let program := (← get).program
    let some last := segments.back? | return #[]
    let .generated name := last.step | return #[]
    unless name == "Inputs" || name == "Coins" || name == "Received" do return #[]
    match before with
    | .declaration id | .member id =>
      return ((program.declarations[id]?).map roster).getD #[]
    | _ => return #[]

  /-- Static arguments that name roles, and the others. -/
  partial def resolveRoleArgs (env : Env) (roles : Array String) (args : StaticArgs) :
      ResolveM (Array Lowered.StaticArgument) := do
    let mut lowered := #[]
    for arg in staticArgList args do
      match arg with
      | .term span none (.path _ rolePath) =>
        match rolePath.plainName? with
        | some name =>
          if roles.contains name.text then
            lowered := lowered.push (.term span none (.reference (oneStep rolePath.span (.role name.text))))
          else lowered := lowered.push (← resolveStaticArg env arg)
        | none => lowered := lowered.push (← resolveStaticArg env arg)
      | _ => lowered := lowered.push (← resolveStaticArg env arg)
    return lowered

  partial def resolveStaticArgs (env : Env) (args : StaticArgs) :
      ResolveM (Array Lowered.StaticArgument) :=
    (staticArgList args).mapM (resolveStaticArg env)

  partial def resolveStaticArg (env : Env) : StaticArg → ResolveM Lowered.StaticArgument
    | .term span name term => do return .term span (name.map (·.text)) (← resolveExprAt env .plain term)
    | .inferred span name => return .inferred span (name.map (·.text))
    | .spec span name term => do return .spec span name.text (← resolveExprAt env .plain term)

  /-- A path where a value, a static term or a type stands: a local name, a reference, or an
  error when it does not resolve. -/
  partial def resolvePathNode (env : Env) (span : Span) (path : Path) (position : Position) :
      ResolveM Lowered.Expr := do
    match (← resolvePath env path position).2 with
    | some reference => localOrReference span reference (path.plainName?.map (·.text))
    | none => return .error span

  partial def resolveType (env : Env) : TypeExpr → ResolveM Lowered.TypeTerm
    | .bool span => return .bool span
    | .nat span => return .nat span
    | .rational span => return .rational span
    | .index span size => do return .index span (← resolveExprAt env .plain size)
    | .nonzero span type => do return .nonzero span (← resolveType env type)
    | .sequence span element size => do
      let element ← resolveType env element
      return .sequence span element (← size.mapM (resolveExprAt env .plain))
    | .tuple span fields => do
      let types ← fields.mapM fun (.tupleField _ _ type) => resolveType env type
      return .tuple span types (fields.map fun (.tupleField _ name _) => name.map (·.text))
    | .path span path => do
      match ← resolvePathNode env span path .plain with
      | .local span binder => return .local span binder
      | .reference reference => return .reference reference
      | _ => return .error span

  /-- A path that names the type of a record construction or a record pattern; a record with a
  field that is not `pub` is built and matched only in its module (NL7). -/
  partial def resolveRecordType (env : Env) (path : Path) : ResolveM (Option Lowered.Reference) := do
    let (target, reference) ← resolvePath env path .plain
    let program := (← get).program
    if let .declaration id := target then
      if let some declaration := program.declarations[id]? then
        if declaration.kind == .record && hasPrivateField declaration &&
            !program.within env.namespace declaration.namespace then
          refuseAt env.owner "NL7" path.span
            s!"`{program.nameOf id}` has a field that is not `pub`; it is built only in `{homeName program declaration}`"
    return reference

  partial def resolveExpr (env : Env) (expr : Expr) : ResolveM Lowered.Expr :=
    resolveExprAt env .value expr

  partial def resolveExprAt (env : Env) (position : Position) : Expr → ResolveM Lowered.Expr
    | .ifExpr span condition thenBranch elseBranch => do
      let condition ← resolveExprAt env position condition
      let onTrue ← resolveExprAt env position thenBranch
      return .conditional span .ifThenElse condition onTrue (← resolveExprAt env position elseBranch)
    | .orExpr span left right => do
      let left ← resolveExprAt env position left
      return .conditional span .or left (.bool span true) (← resolveExprAt env position right)
    | .andExpr span left right => do
      let left ← resolveExprAt env position left
      return .conditional span .and left (← resolveExprAt env position right) (.bool span false)
    | .compare span operator left right => do
      let left ← resolveExprAt env position left
      return .operator span (operatorOfCompare operator) #[left, ← resolveExprAt env position right]
    | .sum span operator left right => do
      let left ← resolveExprAt env position left
      return .operator span (operatorOfSum operator) #[left, ← resolveExprAt env position right]
    | .product span operator left right => do
      let left ← resolveExprAt env position left
      return .operator span (operatorOfProduct operator) #[left, ← resolveExprAt env position right]
    | .power span left right => do
      let left ← resolveExprAt env position left
      return .operator span .power #[left, ← resolveExprAt env position right]
    | .innerProduct span _ left right => do
      let left ← resolveExprAt env position left
      return .inner span left (← resolveExprAt env position right)
    | .notExpr span operand => do return .operator span .not #[← resolveExprAt env position operand]
    | .unary span operand => do return .operator span .negate #[← resolveExprAt env position operand]
    | .paren _ operand => resolveExprAt env position operand
    | .field span target name => do return .field span (← resolveExprAt env position target) name
    | .position span target number => do
      return .position span (← resolveExprAt env position target) number.value
    | .method span target name staticArgs args => do
      let target ← resolveExprAt env position target
      let staticArgs ← staticArgs.mapM (resolveStaticArgs env)
      let (arguments, _) ← resolveCallArgs env position args
      return .method span target name staticArgs arguments
    | .index span target index => do
      let target ← resolveExprAt env position target
      return .operator span .index #[target, ← resolveExprAt env position index]
    | .slice span target lower upper => do
      let target ← resolveExprAt env position target
      let lower ← lower.mapM (resolveExprAt env position)
      return .slice span target lower (← upper.mapM (resolveExprAt env position))
    | .number number => return .number number.span number.value
    | .byteString literal => return .bytes literal.span literal.values
    | .trueLiteral span => return .bool span true
    | .falseLiteral span => return .bool span false
    | .unit span => return .tuple span #[] #[]
    | .boolType span => return .type (.bool span)
    | .natType span => return .type (.nat span)
    | .rationalType span => return .type (.rational span)
    | .path span path => resolvePathNode env span path position
    | .call span callee args => do
      let (_, reference) ← resolvePath env callee position
      let (arguments, witnesses) ← resolveCallArgs env position args
      match reference with
      | some reference => return .call span reference arguments witnesses
      | none => return .error span
    | .record span type fields => do
      let reference ← resolveRecordType env type
      let mut values := #[]
      for field in fields do
        let .fieldInit fieldSpan name value := field
        match value with
        | some value => values := values.push (.field fieldSpan name (← resolveExprAt env position value))
        | none => values := values.push (.field fieldSpan name (← resolveName env name position))
      match reference with
      | some reference => return .record span reference values
      | none => return .error span
    | .tuple span components => do
      let values ← components.mapM fun (.component _ _ value) => resolveExprAt env position value
      return .tuple span values (components.map fun (.component _ name _) => name.map (·.text))
    | .list span elements => do return .list span (← elements.mapM (resolveExprAt env position))
    | .repetition span element count => do
      let element ← resolveExprAt env position element
      return .repetition span element (← resolveExprAt env .plain count)
    | .comprehension span element pattern domain filter => do
      let (generator, levels) ← resolveGenerator env position pattern domain (bodyExpr := some element)
      let element ← resolveExprAt env position element
      let filter ← filter.mapM (resolveExprAt env position)
      popSuite
      let element := if levels.isEmpty then element else .block span levels element
      return .comprehension span element generator filter
    | .recordUpdate span value fields => do
      let value ← resolveExprAt env position value
      let fields ← fields.mapM fun (.fieldUpdate fieldSpan name update) => do
        return Lowered.FieldValue.field fieldSpan name (← resolveExprAt env position update)
      return .recordUpdate span value fields
    | .binderForm span operator _ pattern domain body => do
      let (generator, levels) ← resolveGenerator env position pattern domain (bodyExpr := some body)
      let body ← resolveExprAt env position body
      popSuite
      let body := if levels.isEmpty then body else .block span levels body
      return .fold span (foldOf operator) generator body
    | .indexType span size => do return .type (.index span (← resolveExprAt env .plain size))
    | .nonzeroType span type => do return .type (.nonzero span (← resolveType env type))

  /-- A name that stands for a value without being a path: the short form `{x}` of a field, the
  name that `:=` updates. -/
  partial def resolveName (env : Env) (name : Name) (position : Position) : ResolveM Lowered.Expr := do
    match ← lookupFirst env name .full with
    | some found =>
      match found.target with
      | .poisoned => return .error name.span
      | _ => localOrReference name.span (← lowerSegments env name.span found.segments {}) (some name.text)
    | none =>
      if position == .value && (← get).alternatives.contains name.text then
        return .reference (oneStep name.span (.bareAlternative name.text))
      refuseAt env.owner "NL3" name.span
        s!"`{name.text}` is not bound: it is no local name, static parameter, declaration or import of this module"
      return .error name.span

  /-- What a loop, a comprehension or a fold ranges over: the domain, then the binder of each item
  in a new suite, which the caller closes, with the levels of a pattern that takes an item
  apart. The index of a range is typed per iteration when it stands in a static position of the
  body (TY10). -/
  partial def resolveGenerator (env : Env) (position : Position) (pattern : Pattern) (domain : Domain)
      (body : Option (Array Stmt) := none) (bodyExpr : Option Expr := none) :
      ResolveM (Lowered.Generator × Array Lowered.Stmt) := do
    let .domain span start stop := domain
    let start ← resolveExprAt env position start
    let stop ← stop.mapM (resolveExprAt env position)
    pushSuite
    match stop with
    | some stop =>
      let staticIndex := match pattern with
        | .name name =>
          (body.getD #[]).any (stmtStaticUse name.text) || bodyExpr.any (staticUseIn name.text false)
        | _ => false
      let (index, levels) ← itemBinder env pattern span (static := staticIndex)
      return (.range index start stop staticIndex, levels)
    | none =>
      let (item, levels) ← itemBinder env pattern span
      let iteration ← madeBinder span .iteration
      return (.collection item iteration start, levels)

  /-- The binder of an item: the name of the pattern, or a binder that lowering makes, with the
  levels that take it apart. -/
  partial def itemBinder (env : Env) (pattern : Pattern) (span : Span) (static : Bool := false) :
      ResolveM (Binder × Array Lowered.Stmt) := do
    match pattern with
    | .name name => return (← bindLocal env name (static := static), #[])
    | .wildcard span => return (← madeBinder span .patternValue, #[])
    | _ =>
      let tree ← bindPattern env pattern
      let made ← madeBinder span .patternValue
      return (made, ← unpackTree tree (.local span made.id) none)

  partial def resolveCallArgs (env : Env) (position : Position) :
      CallArgs → ResolveM (Array Lowered.Argument × Option (Array Lowered.Argument))
    | .callArgs _ arguments witnesses => do
      let argument (argument : Argument) : ResolveM Lowered.Argument :=
        match argument with
        | .positional span value => do return .positional span (← resolveExprAt env position value)
        | .named span name value => do return .named span name (← resolveExprAt env position value)
        | .spec span name value => do return .spec span name (← resolveExprAt env position value)
      let lowered ← arguments.mapM argument
      return (lowered, ← witnesses.mapM (·.mapM argument))

  /-- Resolves the type of a record pattern and binds the names of a pattern, in the order of the
  text. -/
  partial def bindPattern (env : Env) : Pattern → ResolveM PatternTree
    | .name name => do return .binder (some (← bindLocal env name))
    | .wildcard span => return .binder (some (← madeBinder span .discarded))
    | .tuple span items => do return .tuple span (← items.mapM (bindPattern env))
    | .record span type fields => do
      let reference ← resolveRecordType env type
      let declaration := match reference with
        | some (.reference _ segments) => segments.back?.bind fun
          | .segment (.declaration id) _ _ => some id
          | _ => none
        | none => none
      let mut written := #[]
      let mut items := #[]
      for field in fields do
        let .fieldPattern fieldSpan name pattern := field
        written := written.push (fieldSpan, name.text)
        match pattern with
        | some pattern => items := items.push (← bindPattern env pattern)
        | none => items := items.push (.binder (some (← bindLocal env name)))
      return .record span ((reference.getD (.reference type.span #[]))) (declaration.getD 0) written items

  /-- A pattern after `case`. A single name is bound: whether it is an alternative of the
  matched variant, and then the case of that alternative, or a name for the matched value that
  covers the alternatives without a case, is decided where the type of the matched value is
  known (TY13). It does not depend on the other variants of the program. -/
  partial def resolveCasePattern (env : Env) : CasePattern → ResolveM Lowered.CasePattern
    | .pattern (.name name) => do
      return .any name.span (some (← bindLocal env name))
    | .pattern pattern => casePatternOf env pattern
    | .number number => return .literal number.span (.number number.span number.value)
    | .trueLiteral span => return .literal span (.bool span true)
    | .falseLiteral span => return .literal span (.bool span false)
    | .variant span path payload => do
      let (_, reference) ← resolvePath env path .value
      let items ← (payload.getD #[]).mapM (resolveCasePattern env)
      return .alternative span (reference.getD (.reference path.span #[])) items
    | .tuple span items => do return .tuple span (← items.mapM (resolveCasePattern env))

  /-- A pattern inside a case pattern: it binds, as the pattern of a binding does. -/
  partial def casePatternOf (env : Env) : Pattern → ResolveM Lowered.CasePattern
    | .name name => do return .any name.span (some (← bindLocal env name))
    | .wildcard span => return .any span none
    | .tuple span items => do return .tuple span (← items.mapM (casePatternOf env))
    | .record span type fields => do
      let reference := (← resolveRecordType env type).getD (.reference type.span #[])
      let fields ← fields.mapM fun (.fieldPattern _ name pattern) => do
        match pattern with
        | some pattern => return (name, ← casePatternOf env pattern)
        | none => return (name, ← casePatternOf env (.name name))
      return .record span reference fields

  partial def resolveStmts (env : Env) (statements : Array Stmt) : ResolveM (Array Lowered.Stmt) := do
    let mut lowered := #[]
    for statement in statements do lowered := lowered ++ (← resolveStmt env statement)
    return lowered

  partial def resolveSuite (env : Env) (statements : Array Stmt) : ResolveM (Array Lowered.Stmt) := do
    pushSuite
    let lowered ← resolveStmts env statements
    popSuite
    return lowered

  partial def resolveStmt (env : Env) : Stmt → ResolveM (Array Lowered.Stmt)
    | .binding span pattern type holders value => do
      let value ← resolveExpr env value
      let type ← type.mapM (resolveType env)
      let roles ← holders.mapM holdersOf
      match pattern with
      | .name name =>
        let isStatic := type.isNone && sizeForm (← get).statics value
        let binder ← bindLocal env name (static := isStatic)
        if isStatic then return #[.staticName span binder value]
        return #[.bind span binder type roles value]
      | .wildcard wildcard => return #[.bind span (← madeBinder wildcard .discarded) type roles value]
      | _ =>
        let tree ← bindPattern env pattern
        let made ← madeBinder span .patternValue
        return #[Lowered.Stmt.bind span made type roles value] ++
          (← unpackTree tree (.local span made.id) roles)
    | .mutDecl span name type placement value => do
      let value ← resolveExpr env value
      let type ← type.mapM (resolveType env)
      let roles ← placement.mapM fun placement => holdersOf placement.holders
      return #[.bind span (← bindLocal env name (mutable := true)) type roles value]
    | .update span name value => do
      let value ← resolveExpr env value
      return #[.update span (← resolveName env name .plain) value]
    | .eventStmt (.bound span site pattern type holders event) => do
      let number ← numberEvent span (siteName site (some pattern)) (eventParts event)
      let what ← resolveEvent env event
      let type ← type.mapM (resolveType env)
      let roles ← holders.mapM holdersOf
      match what with
      | .error names =>
        match pattern with
        | .name name => discard <| bindLocal env name (site := true)
        | _ => discard <| bindPattern env pattern
        let names := names ++ (type.map (#[Lowered.Expr.type ·])).getD #[]
        return #[.waiting span (waitReason event) names]
      | .ok what =>
        match pattern with
        | .name name => return #[.event span number (some (← bindLocal env name (site := true))) type roles what]
        | .wildcard wildcard =>
          return #[.event span number (some (← madeBinder wildcard .discarded)) type roles what]
        | _ =>
          let tree ← bindPattern env pattern
          let made ← madeBinder span .patternValue
          return #[Lowered.Stmt.event span number (some made) type roles what] ++
            (← unpackTree tree (.local span made.id) roles)
    | .eventStmt (.application span site application) => do
      let number ← numberEvent span (siteName site none) #["value"]
      match ← resolveApplication env application with
      | .ok what => return #[.event span number none none none what]
      | .error names => return #[.waiting span "an application of a protocol that is not resolved" names]
    | .«open» span _ claims => do
      let mut names := #[]
      for claim in claims do
        names := names.push (← resolveExpr env claim.handle)
        if let some opening := claim.opening then
          names := names.push (← resolveExpr env opening.position)
          names := names.push (← resolveExpr env opening.value)
      return #[.waiting span "an `open` (layer D)" names]
    | .guard span holders condition reason => do
      let condition ← resolveExpr env condition
      let roles ← holders.mapM holdersOf
      return #[.guard span roles condition (reasonOf reason)]
    | .«if» span condition thenSuite elseBranch => do
      let condition ← resolveExpr env condition
      let isStatic := staticCondition (← get).statics condition
      let onTrue ← resolveSuite env thenSuite
      let onFalse ← match elseBranch with
        | some (.suite _ statements) => resolveSuite env statements
        | some (.elseIf statement) => resolveStmt env statement
        | none => pure #[]
      return #[.«if» span isStatic condition onTrue onFalse]
    | .«match» span scrutinee cases => do
      let scrutinee ← resolveExpr env scrutinee
      let cases ← cases.mapM fun (.«case» caseSpan pattern body) => do
        pushSuite
        let pattern ← resolveCasePattern env pattern
        let body ← resolveStmts env body
        popSuite
        return Lowered.Case.«case» caseSpan pattern body
      return #[.«match» span scrutinee cases]
    | .«for» span pattern domain collected body => do
      let (generator, levels) ← resolveGenerator env .value pattern domain (body := some body)
      let lowered ← resolveStmts env body
      let values ← (collected.getD #[]).mapM fun entry => resolveExpr env entry.value
      popSuite
      let mut collectedBinders := #[]
      for (entry, value) in (collected.getD #[]).zip values do
        collectedBinders := collectedBinders.push
          (Lowered.Collected.collected entry.span (← bindLocal env entry.name) value)
      return #[.«for» span generator collectedBinders (levels ++ lowered)]
    | .empty _ => return #[]

  /-- An event, or the names of one that waits for a later layer. -/
  partial def resolveEvent (env : Env) : Event → ResolveM (Except (Array Lowered.Expr) Lowered.Event)
    | .send _ payload sender receivers oracle => do
      let payload ← resolveExpr env payload
      if let some kind := oracle then
        return .error #[payload, ← resolveExprAt env .plain kind]
      let sender ← sender.mapM roleOf
      return .ok (.send payload sender (← receivers.mapM roleOf))
    | .draw _ type sender receivers => do
      let law ← resolveType env type
      return .ok (.draw law (← roleOf sender) (← receivers.mapM roleOf))
    | .sample _ type => do return .ok (.sample (← resolveType env type))
    | .query _ handle _ positions _ => do
      let handle ← resolveExpr env handle
      return .error #[handle, ← resolveExpr env positions]
    | .attempt _ => return .ok .attempt
    | .application application => resolveApplication env application

  partial def resolveApplication (env : Env) (application : Application) :
      ResolveM (Except (Array Lowered.Expr) Lowered.Event) := do
    let (_, callee) ← resolvePath env application.callee .plain
    let (arguments, _) ← resolveCallArgs env .value application.args
    let mut roleMap := #[]
    for entry in (application.roleMap.map (·.entries)).getD #[] do
      roleMap := roleMap.push (entry.callee, ← roleOf entry.caller)
    match callee with
    | some callee => return .ok (.apply callee arguments roleMap)
    | none => return .error (arguments.map fun
        | .positional _ value | .named _ _ value | .spec _ _ value => value)

  /-- Why an event statement waits. -/
  partial def waitReason : Event → String
    | .send .. => "an oracle send (layer D)"
    | .query .. => "a `query` (layer D)"
    | _ => "an application of a protocol that is not resolved"

  partial def resolveBody (env : Env) : Body → ResolveM Lowered.Expr
    | .expression _ value | .suiteExpression _ value => resolveExpr env value
    | .statements span statements result => do
      let lowered ← resolveStmts env statements
      return .block span lowered (← resolveExpr env result)
end

end Zkc.Frontend.Names
