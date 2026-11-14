module

public import Zkc.Frontend.Names.Basic

@[expose] public section

set_option autoImplicit false

/-!
# Lookup

What a name stands for, without recording anything: the first segment of a path, found
lexically, and each later segment, a step from what came before.

The first segment is found innermost first: a local name; a static parameter; `Self` in an
interface; a member of the interface the name stands in, or of an interface that its `where`
requires of `Self`; a declaration or an import of the namespaces around; a name of the prelude;
a function of the fixed table; `log2`.

A step through a static parameter, `Self`, or a type or module member of one is checked against
the interfaces that the text declares for it: the bound of the parameter, the bound an interface
writes on a member, the `where` constraints in scope and those of the interfaces it has,
closed under what each interface requires of `Self`. A member that none of them declares is
refused here, whatever the instances are (SP3). A step through a declared type is left to the
instance.

Imports are resolved on demand and remembered; the chain of imports being resolved is kept, so
that a cycle is refused and does not loop.
-/

namespace Zkc.Frontend.Names

open Syntax

/-- The scopes from the outermost to `scope`. -/
def chainOf (program : Program) (scope : ScopeId) : Array ScopeId := Id.run do
  let mut chain := #[]
  let mut current := some scope
  for _ in [0:program.scopes.size + 1] do
    match current with
    | none => break
    | some id =>
      chain := chain.push id
      current := (program.scopes[id]?).bind (·.parent)
  return chain.reverse

/-- The static parameters of a chain of scopes by name; an inner scope hides an outer one. -/
def parametersOf (program : Program) (scopes : Array ScopeId) : Std.HashMap String ParameterRef :=
  scopes.foldl (init := {}) fun map scope =>
    let parameters := ((program.scopes[scope]?).map (·.parameters)).getD #[]
    (List.range parameters.size).foldl (init := map) fun map index =>
      map.insert parameters[index]!.name.text ⟨scope, index⟩

/-- The interface whose namespace this is. -/
def interfaceOfNamespace (program : Program) (ns : NamespaceId) : Option DeclarationId := do
  let n ← program.namespaces[ns]?
  let owner ← program.declarations[n.owner]?
  if owner.kind == .interface then some n.owner else none

/-- An environment without facts. -/
def plainEnv (program : Program) (owner : Owner) (file : FileId) (ns : NamespaceId)
    (scopes : Array ScopeId) : Env :=
  { owner, file, «namespace» := ns, scopes, parameters := parametersOf program scopes
    interface? := interfaceOfNamespace program ns }

/-- The environment of an import: the namespace and the scopes where the `use` stands. -/
def importEnv (program : Program) (id : ImportId) : Env :=
  let entry := program.imports[id]!
  plainEnv program (.import id) entry.file entry.namespace entry.scopes

/-- The environment in which the bounds and the `where` of a scope are read. -/
def scopeEnv (program : Program) (scope : ScopeId) : Env :=
  let entry := program.scopes[scope]!
  plainEnv program (.scope scope) entry.file entry.namespace (chainOf program scope)

/-- The environment of the head of an interface. -/
def interfaceEnv (program : Program) (id : DeclarationId) : Env :=
  let declaration := program.declarations[id]!
  plainEnv program (.declaration id) declaration.file (declaration.inner.getD declaration.namespace)
    declaration.scopes

/-- What a declaration found in a namespace stands for. -/
def kindOf (program : Program) (id : DeclarationId) : Option DeclarationKind :=
  (program.declarations[id]?).map (·.kind)

def nodeOf (program : Program) (id : DeclarationId) : Option DeclarationSyntax :=
  (program.declarations[id]?).map (·.node)

def targetOf (program : Program) (id : DeclarationId) : Target :=
  match kindOf program id with
  | some .fileModule | some .«module» => .«module» id
  | _ => .declaration id

def generatedOfProtocol : Array String := #["Run", "Runs", "Inputs", "Coins", "Received"]

def generatedOfScheme : Array String :=
  #["Statement", "Witness", "Keys", "Proof", "Results", "prove", "verify", "run"]

def generatedOfLayout : Array String := #["write", "read"]

def fixedFunction? : String → Option FixedFunction
  | "sum" => some .sum
  | "product" => some .product
  | "all" => some .all
  | "any" => some .any
  | "inner" => some .inner
  | _ => none

def segment (step : Step) : WrittenSegment := { step, staticArgs := none }

/-- The target that the member `id` of a static thing gives the path `path`. -/
def memberTarget (program : Program) (id : DeclarationId) (path : StaticPath) : Target :=
  match kindOf program id with
  | some .typeMember | some .moduleMember | some .naturalMember => .static path
  | _ => .member id

/-- How a lookup reads names. -/
inductive Mode where
  /-- Every lexical name. -/
  | full
  /-- Only declarations and imports of namespaces and the prelude: how a bound is read when
  what a static thing has is being worked out. -/
  | namespaces
  deriving BEq

/-- `Self` and a member of interface `interface`, for a bare name inside it. -/
def selfMember (program : Program) (interface : DeclarationId) (member : DeclarationId)
    (name : String) : Found :=
  let path : StaticPath := { root := .self interface, members := #[name] }
  { segments := #[segment (.self interface), segment (.member name (some member))]
    target := memberTarget program member path }

/-- A fact of `interface`, with its `Self` read as `path`. -/
def substitute (fact : Fact) (interface : DeclarationId) (path : StaticPath) : Fact :=
  let replace (subject : StaticPath) : StaticPath :=
    match subject.root with
    | .self id => if id == interface then { path with members := path.members ++ subject.members } else subject
    | .parameter _ => subject
  match fact with
  | .bound subject knownOf => .bound (replace subject) knownOf
  | .equal left right =>
    let side : FactSubject → FactSubject
      | .path p => .path (replace p)
      | .other => .other
    .equal (side left) (side right)

def refusal (rule : String) (span : Span) (message : String) : Diagnostic :=
  { origin := .names, rule, span, message := .ofText message }

mutual
  /-- The steps of an import's path and what it stands for, or nothing when it is refused (the
  refusal is the import's) or names an unreadable module. -/
  partial def importFound (id : ImportId) : ResolveM (Option Found) := do
    let state ← get
    match state.imports[id]? with
    | some (.done found) => return some found
    | some .failed => return none
    | some .inProgress =>
      let program := state.program
      let names := (state.importStack.toList.dropWhile (· != id)).map fun other =>
        (program.imports[other]?).map (·.name.text) |>.getD ""
      let entry := program.imports[id]!
      let cycle := " → ".intercalate (names ++ [entry.name.text])
      refuseAt (.import id) "NL3" entry.name.span
        s!"`{entry.name.text}` is not bound: its imports form a cycle through {cycle}"
      modify fun state => { state with imports := state.imports.insert id .failed }
      return none
    | none =>
      modify fun state => { state with
        imports := state.imports.insert id .inProgress
        importStack := state.importStack.push id }
      let result ← usePath id
      modify fun state => { state with importStack := state.importStack.pop }
      match result with
      | .ok found =>
        modify fun state => { state with imports := state.imports.insert id (.done found) }
        return some found
      | .error refused =>
        -- a cycle refused this import already; keep that refusal
        if let some .failed := (← get).imports[id]? then return none
        refuse (.import id) refused
        modify fun state => { state with imports := state.imports.insert id .failed }
        return none

  /-- The path of a `use`: the longest prefix that is a module, then a step per name. -/
  partial def usePath (id : ImportId) : ResolveM (Except Diagnostic Found) := do
    let state ← get
    let program := state.program
    let entry := program.imports[id]!
    let env := importEnv program id
    let segments := segmentsOf entry.path
    let names := segments.map fun s => (segmentName s).text
    let mut start : Option (Nat × Found) := none
    for shorter in [0:names.size] do
      let count := names.size - shorter
      let key := pathText (names.extract 0 count)
      if state.unreadable.contains key then return .ok { segments := #[], target := .poisoned }
      let args := segmentArgs segments[count - 1]!
      if let some moduleId := program.modules[key]? then
        let first : WrittenSegment :=
          { step := .declaration moduleId, staticArgs := args, fixedBy := some id }
        start := some (count, { segments := #[first], target := .«module» moduleId })
        break
      if isVocabularyModule key then
        let first : WrittenSegment :=
          { step := .vocabularyModule key, staticArgs := args, fixedBy := some id }
        start := some (count, { segments := #[first], target := .vocabularyModule key })
        break
    let some (count, initial) := start
      | return .error (refusal "NL3" (segmentName segments[0]!).span
          s!"`{pathText names}` names no module: no file given and no file of the library has its path or a prefix of it")
    let mut found := initial
    for index in [count:segments.size] do
      let name := segmentName segments[index]!
      match ← step env found.target name (pathPrefixText entry.path (index - 1)) with
      | .error refused => return .error refused
      | .ok next =>
        found := { segments := found.segments ++ withArgs next.segments
                     (segmentArgs segments[index]!) (some id)
                   target := next.target }
    let pathSegments := found.segments
    modify fun state => { state with importPaths := state.importPaths.insert id pathSegments }
    if let some selected := entry.selected then
      match ← step env found.target selected (pathText names) with
      | .error refused => return .error refused
      | .ok next =>
        found := { segments := found.segments ++ withArgs next.segments none (some id)
                   target := next.target }
    return .ok found

  /-- The written arguments on the last of the steps of one segment. -/
  partial def withArgs (segments : Array WrittenSegment) (args : Option StaticArgs)
      (fixedBy : Option ImportId) : Array WrittenSegment :=
    if segments.isEmpty then segments else
    segments.modify (segments.size - 1) fun last =>
      if last.fixedBy.isSome && last.staticArgs.isSome then last
      else { last with staticArgs := args.orElse fun _ => last.staticArgs
                       fixedBy := if args.isSome then fixedBy else last.fixedBy.orElse fun _ => fixedBy }

  /-- What a binding of a namespace stands for. -/
  partial def bindingFound (binding : Binding) : ResolveM Found := do
    let program := (← get).program
    match binding with
    | .declaration id =>
      return { segments := #[segment (.declaration id)], target := targetOf program id }
    | .import id =>
      match ← importFound id with
      | some found => return found
      | none => return { segments := #[], target := .poisoned }

  /-- The first segment of a path. -/
  partial def lookupFirst (env : Env) (name : Name) (mode : Mode) : ResolveM (Option Found) := do
    let state ← get
    let program := state.program
    let text := name.text
    if mode == .full then
      if state.locals.contains text then
        return some { segments := #[segment .«local»], target := .value }
      if let some reference := env.parameters[text]? then
        return some { segments := #[segment (.parameter reference)]
                      target := .static { root := .parameter reference, members := #[] } }
      if let some interface := env.interface? then
        if text == "Self" then
          return some { segments := #[segment (.self interface)]
                        target := .static { root := .self interface, members := #[] } }
    let mut current := some env.namespace
    for _ in [0:program.namespaces.size + 1] do
      let some ns := current | break
      let some entry := program.namespaces[ns]? | break
      if interfaceOfNamespace program ns |>.isSome then
        if mode == .full then
          let all ← closure #[entry.owner]
          if let some member ← findMember all text then
            return some (selfMember program entry.owner member text)
      else
        match entry.names[text]? with
        | some (.declaration id) =>
          if env.excluded? != some id then return some (← bindingFound (.declaration id))
        | some binding => return some (← bindingFound binding)
        | none =>
          -- `Self` in a module that implements an interface is the module (SP8): a member
          -- repeats the head that the interface writes with `Self`
          if text == "Self" && mode == .full then
            if let some owner := program.declarations[entry.owner]? then
              if (implementing? owner).isSome then
                return some { segments := #[segment (.declaration entry.owner)]
                              target := .«module» entry.owner }
        if mode == .full then
          if let some host := env.host? then
            if (program.declarations[host]?).bind (·.inner) == some ns then
              let known ← moduleKnown host
              if let some member ← findMember (← closure known.interfaces) text then
                return some { segments := #[segment (.declaration host),
                                            segment (.member text (some member))]
                              target := .«open» }
      current := entry.parent
    if let some prelude := state.prelude? then
      match (program.namespaces[prelude]?).bind (·.names[text]?) with
      | some (.declaration id) =>
        if (program.declarations[id]?).any (·.pub) then
          return some (← bindingFound (.declaration id))
      | some (.import id) =>
        if (program.imports[id]?).any (·.pub) then return some (← bindingFound (.import id))
      | none => pure ()
    if mode == .full then
      if let some function := fixedFunction? text then
        return some { segments := #[segment (.fixed function)], target := .value }
      if text == "log2" then return some { segments := #[segment .sizeOperator], target := .value }
    return none

  /-- One step from `target` by the name of the next segment. `before` is the text of the path
  so far, for messages. -/
  partial def step (env : Env) (target : Target) (name : Name) (before : String) :
      ResolveM (Except Diagnostic Found) := do
    let state ← get
    let program := state.program
    let text := name.text
    let noMember (what : String) : Except Diagnostic Found :=
      .error (refusal "NL3" name.span s!"{what} has no member `{text}`")
    let open_ : Except Diagnostic Found :=
      .ok { segments := #[segment (.member text none)], target := .«open» }
    match target with
    | .poisoned => return .ok { segments := #[], target := .poisoned }
    | .«module» id =>
      let some declaration := program.declarations[id]? | return open_
      let some inner := declaration.inner | return open_
      let entry := program.namespaces[inner]!
      let within := program.within env.namespace inner
      let interfaces ← match implementing? declaration with
        | some _ => do pure (some (← closure (← moduleKnown id).interfaces))
        | none => pure none
      match entry.names[text]? with
      | some (.declaration found) =>
        let other := program.declarations[found]!
        let isMember ← match interfaces with
          | some all => do pure (other.kind == .functionDefinition || other.kind == .moduleDefinition
              || (← findMember all text).isSome)
          | none => pure false
        if other.pub || within || isMember then
          return .ok { segments := #[segment (.declaration found)], target := targetOf program found }
        return .error (refusal "NL7" name.span
          s!"`{text}` is not `pub` in `{before}`; a declaration without `pub` is visible in its module only")
      | some (.import found) =>
        if (program.imports[found]?).any (·.pub) || within then
          return .ok (← bindingFound (.import found))
        return .error (refusal "NL3" name.span
          s!"module `{before}` has no `{text}`: its `use` of `{text}` is not `pub`")
      | none =>
        if let some all := interfaces then
          if let some member ← findMember all text then
            return .ok { segments := #[segment (.member text (some member))]
                         target := match kindOf program member with
                           | some .typeMember | some .moduleMember | some .naturalMember => .«open»
                           | _ => .member member }
          if state.layout?.any all.contains && generatedOfLayout.contains text then
            return .ok { segments := #[segment (.generated text)], target := .generated }
          if (← moduleKnown id).open then return open_
        return .error (refusal "NL3" name.span s!"module `{before}` has no `{text}`")
    | .vocabularyModule path =>
      if (vocabularyEntry? path text).isSome then
        return .ok { segments := #[segment (.entry path text)], target := .value }
      return .error (refusal "NL3" name.span s!"module `{path}` has no `{text}`")
    | .declaration id =>
      let some declaration := program.declarations[id]? | return open_
      match declaration.kind with
      | .«variant» =>
        let alternatives := match declaration.node with
          | .enum node => node.alternatives
          | _ => #[]
        match alternatives.findIdx? (·.name.text == text) with
        | some index =>
          return .ok { segments := #[segment (.alternative id index)], target := .alternative }
        | none =>
          return .error (refusal "NL3" name.span s!"the variant `{before}` has no alternative `{text}`")
      | .protocol =>
        if generatedOfProtocol.contains text then
          return .ok { segments := #[segment (.generated text)], target := .generated }
        return .error (refusal "NL3" name.span
          s!"the protocol `{before}` has no member `{text}`: its members are Run, Runs, Inputs, Coins and Received (§8)")
      | .scheme =>
        if generatedOfScheme.contains text then
          return .ok { segments := #[segment (.generated text)], target := .generated }
        return .error (refusal "NL3" name.span
          s!"the scheme `{before}` has no member `{text}`: its members are Statement, Witness, Keys, Proof, Results, prove, verify and run (§8)")
      | .alias | .vocabularyType | .specType | .record | .moduleDefinition => return open_
      | .interface =>
        return .error (refusal "NL3" name.span
          s!"`{before}` is an interface; a member is reached through a module that implements it or a static parameter bounded by it")
      | kind => return noMember s!"`{before}` is {kindWord kind}; it"
    | .static path =>
      -- what is known of a path is looked up once per path: the table is of this lookup alone
      modify fun state => { state with knownPaths := {}, knownCut := false }
      let known ← known env path #[]
      if let some member ← findMember known.interfaces text then
        return .ok { segments := #[segment (.member text (some member))]
                     target := memberTarget program member (path.push text) }
      if state.layout?.any known.interfaces.contains && generatedOfLayout.contains text then
        return .ok { segments := #[segment (.generated text)], target := .generated }
      if known.open then
        return .ok { segments := #[segment (.member text none)], target := .static (path.push text) }
      -- in the order of their declarations: the sorts in the order of their hierarchy
      let names := (known.interfaces.qsort (· < ·)).map (declarationName program)
      let allSorts ← known.interfaces.allM isSort
      let tail :=
        if names.isEmpty then "it has no sort and no interface"
        else if allSorts then s!"its sorts are {", ".intercalate names.toList}"
        else s!"its interfaces are {", ".intercalate names.toList}"
      return .error (refusal "SP3" name.span s!"`{before}` has no member `{text}`; {tail}")
    | .member id =>
      if (program.declarations[id]?).any (·.kind == .protocolMember) &&
          generatedOfProtocol.contains text then
        return .ok { segments := #[segment (.generated text)], target := .generated }
      return noMember s!"`{before}`"
    | .«open» | .generated => return open_
    | .alternative | .value => return noMember s!"`{before}`"

  /-- The first member of these interfaces with the name. -/
  partial def findMember (interfaces : Array DeclarationId) (name : String) :
      ResolveM (Option DeclarationId) := do
    let program := (← get).program
    for interface in interfaces do
      let some inner := (program.declarations[interface]?).bind (·.inner) | continue
      if let some (.declaration member) := (program.namespaces[inner]?).bind (·.names[name]?) then
        return some member
    return none

  /-- Whether an interface is a sort: `Group` of `zkc::algebra`, or an interface whose `where`
  requires `Self` to be of a sort (SP3). -/
  partial def isSort (interface : DeclarationId) : ResolveM Bool := do
    let program := (← get).program
    let some algebra := program.modules["zkc::algebra"]? | return false
    let group := ((program.declarations[algebra]?).bind (·.inner)).bind fun inner =>
      (program.namespaces[inner]?).bind (·.names["Group"]?)
    let some (.declaration group) := group | return false
    return (← closure #[interface]).contains group

  /-- The interfaces with every interface that one of them requires of `Self`, in the order
  reached. -/
  partial def closure (interfaces : Array DeclarationId) : ResolveM (Array DeclarationId) := do
    let mut result : Array DeclarationId := #[]
    let mut queue := interfaces
    let mut index := 0
    while index < queue.size do
      let interface := queue[index]!
      index := index + 1
      if result.contains interface then continue
      result := result.push interface
      queue := queue ++ (← requirements interface)
    return result

  /-- What the `where` of an interface requires of `Self` (`Self: Group`). -/
  partial def requirements (interface : DeclarationId) : ResolveM (Array DeclarationId) := do
    let state ← get
    if let some cached := state.requirements[interface]? then return cached
    if state.requirementsInProgress.contains interface then return #[]
    modify fun state => { state with
      requirementsInProgress := state.requirementsInProgress.insert interface }
    let program := state.program
    let env := interfaceEnv program interface
    let constraints : Array Constraint := match nodeOf program interface with
      | some (.interface node) => (node.whereClause.map (·.constraints)).getD #[]
      | _ => #[]
    let mut result : Array DeclarationId := #[]
    for constraint in constraints do
      if let Constraint.bound _ (.path _ path) bound := constraint then
        if path.plainName?.map (·.text) == some "Self" then
          result := (Known.union { interfaces := result } (← boundKnown env bound)).interfaces
    modify fun state => { state with
      requirements := state.requirements.insert interface result
      requirementsInProgress := state.requirementsInProgress.erase interface }
    return result

  /-- The interfaces that a bound names. A bound that names something else is left open. -/
  partial def boundKnown (env : Env) (bound : Bound) : ResolveM Known := do
    let mut known : Known := {}
    for sort in bound.sorts do
      if let .path path := sort then
        known := known.union (← interfaceOf env path)
    return known

  /-- The interface that a path of a bound names, read through namespaces only. -/
  partial def interfaceOf (env : Env) (path : Path) : ResolveM Known := do
    let program := (← get).program
    let segments := segmentsOf path
    let some first := segments[0]? | return { «open» := true }
    let some found ← lookupFirst env (segmentName first) .namespaces | return { «open» := true }
    let mut target := found.target
    for index in [1:segments.size] do
      match target with
      | .«module» _ | .vocabularyModule _ | .declaration _ =>
        match ← step env target (segmentName segments[index]!) (pathPrefixText path (index - 1)) with
        | .ok next => target := next.target
        | .error _ => return { «open» := true }
      | _ => return { «open» := true }
    match target with
    | .declaration id =>
      if (program.declarations[id]?).any (·.kind == .interface) then
        return { interfaces := #[id] }
      return { «open» := true }
    | _ => return { «open» := true }

  /-- The interfaces that an implementing module names in its bound. -/
  partial def moduleKnown (id : DeclarationId) : ResolveM Known := do
    let state ← get
    if let some cached := state.moduleKnown[id]? then return cached
    if state.moduleKnownInProgress.contains id then return { «open» := true }
    let program := state.program
    let some declaration := program.declarations[id]? | return {}
    let some bound := implementing? declaration | return {}
    modify fun state => { state with moduleKnownInProgress := state.moduleKnownInProgress.insert id }
    let env := plainEnv program (.declaration id) declaration.file
      (declaration.inner.getD declaration.namespace) declaration.scopes
    let known ← boundKnown env bound
    modify fun state => { state with
      moduleKnown := state.moduleKnown.insert id known
      moduleKnownInProgress := state.moduleKnownInProgress.erase id }
    return known

  /-- The bound written on a static parameter. -/
  partial def parameterKnown (reference : ParameterRef) : ResolveM Known := do
    let state ← get
    if let some cached := state.parameterKnown[reference]? then return cached
    let program := state.program
    let some scope := program.scopes[reference.scope]? | return {}
    let some parameter := scope.parameters[reference.index]? | return {}
    let known ← match parameter.bound with
      | some bound => boundKnown (scopeEnv program reference.scope) bound
      | none => pure {}
    modify fun state => { state with parameterKnown := state.parameterKnown.insert reference known }
    return known

  /-- The bound an interface writes on a type or module member. -/
  partial def memberKnown (member : DeclarationId) : ResolveM Known := do
    let state ← get
    if let some cached := state.memberKnown[member]? then return cached
    let program := state.program
    let some declaration := program.declarations[member]? | return {}
    let bound := match declaration.node with
      | .member (.typeMember _ _ _ bound) => bound
      | .member (.moduleMember _ _ bound) => some bound
      | _ => none
    let env := plainEnv program (.declaration member) declaration.file declaration.namespace
      declaration.scopes
    let known ← match bound with
      | some bound => boundKnown env bound
      | none => pure {}
    modify fun state => { state with memberKnown := state.memberKnown.insert member known }
    return known

  /-- The static path that a subject of a constraint names, when it is one: a static parameter
  or `Self`, or a member of the interface, followed by member names. -/
  partial def subjectPath (env : Env) (subject : Expr) : ResolveM (Option StaticPath) := do
    match subject with
    | .paren _ inner => subjectPath env inner
    | .path _ (.path _ segments) =>
      let names := segments.map fun s => (segmentName s).text
      let some first := names[0]? | return none
      if let some reference := env.parameters[first]? then
        return some { root := .parameter reference, members := names.extract 1 names.size }
      if let some interface := env.interface? then
        if first == "Self" then
          return some { root := .self interface, members := names.extract 1 names.size }
        if (← findMember (← closure #[interface]) first).isSome then
          return some { root := .self interface, members := names }
      return none
    | _ => return none

  /-- What the constraints of a `where` state about static things. -/
  partial def factsOf (env : Env) (whereClause : Where) : ResolveM (Array Fact) := do
    let mut facts := #[]
    for constraint in whereClause.constraints do
      match constraint with
      | .bound _ subject bound =>
        if let some path ← subjectPath env subject then
          facts := facts.push (.bound path (← boundKnown env bound))
      | .compare _ .equal left right =>
        let side (expression : Expr) : ResolveM FactSubject := do
          match ← subjectPath env expression with
          | some path => pure (.path path)
          | none => pure .other
        facts := facts.push (.equal (← side left) (← side right))
      | .compare .. => pure ()
    return facts

  /-- The facts that the `where` of an interface states, relative to its `Self`. -/
  partial def interfaceFacts (interface : DeclarationId) : ResolveM (Array Fact) := do
    let state ← get
    if let some cached := state.interfaceFacts[interface]? then return cached
    modify fun state => { state with interfaceFacts := state.interfaceFacts.insert interface #[] }
    let program := state.program
    let facts ← match nodeOf program interface with
      | some (.interface node) => match node.whereClause with
        | some whereClause => factsOf (interfaceEnv program interface) whereClause
        | none => pure #[]
      | _ => pure #[]
    modify fun state => { state with interfaceFacts := state.interfaceFacts.insert interface facts }
    return facts

  /-- The interfaces that a static path is known to have, closed under requirements. -/
  partial def known (env : Env) (path : StaticPath) (visited : Array StaticPath) :
      ResolveM Known := do
    -- a path that is being computed gives nothing here; what met it is not kept
    if visited.contains path then
      modify fun state => { state with knownCut := true }
      return {}
    if let some found := (← get).knownPaths[path]? then return found
    let outerCut := (← get).knownCut
    modify fun state => { state with knownCut := false }
    let visited := visited.push path
    let program := (← get).program
    let mut result : Known := {}
    match path.parent? with
    | none =>
      match path.root with
      | .parameter reference => result := ← parameterKnown reference
      | .self interface => result := { interfaces := #[interface] }
    | some (parent, last) =>
      let above ← known env parent visited
      match ← findMember above.interfaces last with
      | some member =>
        if (program.declarations[member]?).any fun d =>
            d.kind == .typeMember || d.kind == .moduleMember then
          result := result.union (← memberKnown member)
      | none => if above.open then result := { result with «open» := true }
    for fact in env.facts do
      result := result.union (← applyFact env fact path visited)
    for drop in [1:path.members.size + 1] do
      let prefixPath : StaticPath :=
        { path with members := path.members.extract 0 (path.members.size - drop) }
      let prefixKnown ← known env prefixPath visited
      for interface in prefixKnown.interfaces do
        for fact in ← interfaceFacts interface do
          result := result.union
            (← applyFact env (substitute fact interface prefixPath) path visited)
    let found : Known := { result with interfaces := ← closure result.interfaces }
    let cut := (← get).knownCut
    modify fun state => { state with
      knownPaths := if cut then state.knownPaths else state.knownPaths.insert path found
      knownCut := outerCut || cut }
    return found

  /-- What a fact says of `path`. -/
  partial def applyFact (env : Env) (fact : Fact) (path : StaticPath) (visited : Array StaticPath) :
      ResolveM Known := do
    match fact with
    | .bound subject knownOf => return if subject == path then knownOf else {}
    | .equal left right =>
      let other : Option FactSubject := match left, right with
        | .path l, _ => if l == path then some right else
            match right with
            | .path r => if r == path then some left else none
            | .other => none
        | .other, .path r => if r == path then some left else none
        | .other, .other => none
      match other with
      | some (.path q) => known env q visited
      | some .other => return { «open» := true }
      | none => return {}
end

end Zkc.Frontend.Names
