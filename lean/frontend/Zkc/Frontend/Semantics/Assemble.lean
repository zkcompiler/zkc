module

public import Std.Data.HashSet
public import Zkc.Frontend.Syntax.Error
public import Zkc.Frontend.Syntax.Spans
public import Zkc.Frontend.Semantics.Program
public import Zkc.Frontend.Basic.Log
public import Zkc.Frontend.Semantics.Vocabulary

@[expose] public section

set_option autoImplicit false

/-!
# Assembly of a program

From parsed files to a `Program`. The given files come first, in their order; then
`zkc::prelude`, which is always loaded; then every module that a `use` names, in the order in
which the paths are reached. A path of a `use` is a module path followed by names: `zkc::a::b`
is the module of the given file with that header, or else the library file `zkc/a/b.zkc`, read
through the loader when the path first names it. The longest prefix of the path that names a
module is the module; the names after it are steps from it. A given file whose header is a
library path stands in place of the library module. `zkc::security` has no source file: its
names are entries of the vocabulary.

Every item becomes a declaration with its namespace and its chain of parameter scopes, every
name bound by a `use` an import. Checked here: no two files have one path (NL4); a namespace
binds a name once (NL2); a module outside the core library declares no name of the prelude, and
each language item is declared in its module, public and with its kind (NL10).
-/

namespace Zkc.Frontend

open Syntax

/-- A source as the assembler receives it: the name under which it was read, which its spans
carry, and its tree or the refusal of the parser. -/
structure SourceInput where
  name : String
  parsed : Except SyntaxError SourceFile
  deriving Inhabited

/-- The modules of the core library (§2.5). -/
def coreModules : Array String :=
  #["zkc::prelude", "zkc::option", "zkc::algebra", "zkc::oracle", "zkc::commitment",
    "zkc::hash", "zkc::layout", "zkc::construction", "zkc::security"]

def preludePath : Array String := #["zkc", "prelude"]

/-- A language item (§2.4): its name, the module that declares it, its kind, and how a message
names the kind. -/
structure LanguageItem where
  name : String
  «module» : String
  kind : DeclarationKind
  description : String
  deriving Inhabited

/-- The language items of §2.4. -/
def languageItems : Array LanguageItem :=
  let sort (name : String) : LanguageItem := ⟨name, "zkc::algebra", .interface, "interface"⟩
  #[⟨"length", "zkc::prelude", .function, "function"⟩,
    ⟨"Option", "zkc::option", .variant, "variant"⟩,
    sort "Group", sort "Ring", sort "PrimeOrderGroup", sort "Field", sort "PrimeField",
    sort "ExtensionField", sort "TwoAdicField",
    ⟨"Kind", "zkc::oracle", .interface, "interface"⟩,
    ⟨"Rows", "zkc::oracle", .interface, "interface"⟩,
    ⟨"Linear", "zkc::oracle", .interface, "interface"⟩,
    ⟨"Derived", "zkc::oracle", .interface, "interface"⟩,
    ⟨"Oracle", "zkc::oracle", .vocabularyType, "sealed type"⟩,
    ⟨"Pending", "zkc::oracle", .vocabularyType, "sealed type"⟩,
    ⟨"data", "zkc::oracle", .function, "function"⟩,
    ⟨"pending", "zkc::oracle", .function, "function"⟩,
    ⟨"lower", "zkc::oracle", .function, "function"⟩,
    ⟨"Commitment", "zkc::commitment", .interface, "interface"⟩,
    ⟨"Hash", "zkc::hash", .interface, "interface"⟩,
    ⟨"Layout", "zkc::layout", .interface, "interface"⟩,
    ⟨"canonical", "zkc::layout", .module, "module"⟩,
    ⟨"Suite", "zkc::construction", .interface, "interface"⟩]

/-- A program as assembled, with the diagnostics of assembly. -/
structure Assembly where
  program : Program
  log : Log
  /-- Module paths whose file the parser refused or whose header names another path: a path
  to one of them stands for nothing, and is not refused again. -/
  unreadable : Std.HashSet String
  deriving Inhabited

namespace Assemble

structure State where
  files : Array SourceUnit := #[]
  namespaces : Array Namespace := #[]
  scopes : Array ParameterScope := #[]
  declarations : Array Declaration := #[]
  imports : Array Import := #[]
  modules : Std.HashMap String DeclarationId := {}
  log : Log := {}
  /-- Module paths that no file has. -/
  missing : Std.HashSet String := {}
  unreadable : Std.HashSet String := {}
  deriving Inhabited

abbrev AssembleM := StateM State

def refuse (rule : String) (span : Span) (message : String) : AssembleM Unit :=
  modify fun state =>
    { state with log := state.log.add { origin := .names, rule, span, message := .ofText message } }

def bindingSpan (state : State) : Binding → Option Span
  | .declaration id => ((state.declarations[id]?).bind (·.name)).map (·.span)
  | .import id => (state.imports[id]?).map (·.name.span)

/-- Binds a name in a namespace. A second binding of a name is refused (NL2). -/
def bind (ns : NamespaceId) (name : Name) (binding : Binding) : AssembleM Unit := do
  let state ← get
  let some current := state.namespaces[ns]? | return
  match current.names[name.text]? with
  | some earlier =>
    let line := ((bindingSpan state earlier).map (·.startLine)).getD 0
    let what := match earlier with
      | .declaration _ => "declared"
      | .import _ => "imported"
    refuse "NL2" name.span
      s!"`{name.text}` is already {what} at line {line}: two declarations of a module, or a declaration and an import, do not share a name"
  | none =>
    modify fun state => { state with
      namespaces := state.namespaces.modify ns fun n => { n with names := n.names.insert name.text binding } }

def newNamespace (parent : Option NamespaceId) (owner : DeclarationId) (file : FileId) :
    AssembleM NamespaceId :=
  modifyGet fun state =>
    let entry : Namespace := { parent, owner, file, names := {} }
    (state.namespaces.size, { state with namespaces := state.namespaces.push entry })

def newScope (origin : ScopeOrigin) (file : FileId) (ns : NamespaceId) (parent : Option ScopeId)
    (parameters : Option StaticParams) (whereClause : Option Where) : AssembleM ScopeId :=
  modifyGet fun state =>
    let entry : ParameterScope :=
      { origin, file, «namespace» := ns, parent
        parameters := (parameters.map (·.params)).getD #[], whereClause }
    (state.scopes.size, { state with scopes := state.scopes.push entry })

/-- A scope of a declaration's own, when it has static parameters or a `where`. -/
def ownScope (file : FileId) (ns : NamespaceId) (scopes : Array ScopeId)
    (parameters : Option StaticParams) (whereClause : Option Where) : AssembleM (Option ScopeId) :=
  if parameters.isSome || whereClause.isSome then
    some <$> newScope .declaration file ns scopes.back? parameters whereClause
  else pure none

/-- Enters a declaration and binds its name in its namespace. -/
def declare (kind : DeclarationKind) (name : Option Name) (pub : Bool) (file : FileId)
    (ns : NamespaceId) (scopes : Array ScopeId) (own : Option ScopeId)
    (inner : Option NamespaceId) (node : DeclarationSyntax) : AssembleM DeclarationId := do
  let chain := match own with
    | some scope => scopes.push scope
    | none => scopes
  let entry : Declaration :=
    { kind, name, pub, file, «namespace» := ns, scopes := chain, ownScope := own, inner, node }
  let id ← modifyGet fun state =>
    (state.declarations.size, { state with declarations := state.declarations.push entry })
  if let some name := name then bind ns name (.declaration id)
  return id

/-- The declaration of an item with an optional scope of its own. -/
def declareItem (kind : DeclarationKind) (name : Name) (pub : Bool) (file : FileId)
    (ns : NamespaceId) (scopes : Array ScopeId) (parameters : Option StaticParams)
    (whereClause : Option Where) (node : DeclarationSyntax) : AssembleM Unit := do
  let own ← ownScope file ns scopes parameters whereClause
  discard <| declare kind (some name) pub file ns scopes own none node

def addUse (file : FileId) (ns : NamespaceId) (scopes : Array ScopeId) (declaration : Use) :
    AssembleM Unit := do
  let entries : Array (Option Name × Name) := match declaration.tail with
    | .whole =>
      match declaration.path with
      | .path _ segments => match segments.back? with
        | some (.segment _ name _) => #[(none, name)]
        | none => #[]
    | .alias name => #[(none, name)]
    | .names _ names => names.map fun name => (some name, name)
  for (selected, name) in entries do
    let entry : Import :=
      { file, «namespace» := ns, scopes, pub := declaration.pub, path := declaration.path
        selected, name }
    let id ← modifyGet fun state =>
      (state.imports.size, { state with imports := state.imports.push entry })
    bind ns name (.import id)

def addMember (file : FileId) (ns : NamespaceId) (scopes : Array ScopeId) (member : Member) :
    AssembleM Unit := do
  match member with
  | .typeMember _ name parameters _ =>
    let own ← ownScope file ns scopes parameters none
    discard <| declare .typeMember (some name) true file ns scopes own none (.member member)
  | .natMember _ name =>
    discard <| declare .naturalMember (some name) true file ns scopes none none (.member member)
  | .moduleMember _ name _ =>
    discard <| declare .moduleMember (some name) true file ns scopes none none (.member member)
  | .defMember _ _ name parameters _ _ whereClause =>
    let own ← ownScope file ns scopes parameters whereClause
    discard <| declare .functionMember (some name) true file ns scopes own none (.member member)
  | .protocolMember head =>
    let own ← ownScope file ns scopes head.staticParams head.whereClause
    discard <| declare .protocolMember (some head.name) true file ns scopes own none (.member member)
  | .lawMember law =>
    let own ← ownScope file ns scopes law.staticParams law.whereClause
    discard <| declare .lawMember (some law.name) true file ns scopes own none (.member member)

mutual
  partial def addItems (file : FileId) (ns : NamespaceId) (scopes : Array ScopeId)
      (items : Array Item) : AssembleM Unit := do
    for item in items do addItem file ns scopes item

  partial def addItem (file : FileId) (ns : NamespaceId) (scopes : Array ScopeId) :
      Item → AssembleM Unit
    | .use declaration => addUse file ns scopes declaration
    | .«section» (.«section» _ parameters whereClause items) => do
      let scope ← newScope .«section» file ns scopes.back? parameters whereClause
      addItems file ns (scopes.push scope) items
    | .«module» declaration => addModule file ns scopes declaration
    | .interface declaration => do
      let id := (← get).declarations.size
      let inner ← newNamespace (some ns) id file
      let own ←
        if declaration.staticParams.isSome || declaration.whereClause.isSome then
          some <$> newScope .interface file inner scopes.back? declaration.staticParams
            declaration.whereClause
        else pure none
      discard <| declare .interface (some declaration.name) declaration.pub file ns scopes own
        (some inner) (.interface declaration)
      let chain := match own with
        | some scope => scopes.push scope
        | none => scopes
      for member in declaration.members.getD #[] do addMember file inner chain member
    | .typeDecl declaration => match declaration with
      | .type _ pub name parameters value =>
        let kind := match value with
          | .primitive _ => DeclarationKind.vocabularyType
          | .type _ => .alias
        declareItem kind name pub file ns scopes parameters none (.typeDecl declaration)
      | .specType _ pub name parameters _ =>
        declareItem .specType name pub file ns scopes parameters none (.typeDecl declaration)
    | .struct declaration =>
      declareItem .record declaration.name declaration.pub file ns scopes declaration.staticParams
        none (.struct declaration)
    | .enum declaration =>
      declareItem .variant declaration.name declaration.pub file ns scopes declaration.staticParams
        none (.enum declaration)
    | .«def» declaration =>
      declareItem .function declaration.name declaration.pub file ns scopes declaration.staticParams
        declaration.whereClause (.«def» declaration)
    | .oracleDef declaration =>
      declareItem .oracleFunction declaration.name declaration.pub file ns scopes
        declaration.staticParams declaration.whereClause (.oracleDef declaration)
    | .protocol declaration =>
      declareItem .protocol declaration.head.name declaration.pub file ns scopes
        declaration.head.staticParams declaration.head.whereClause (.protocol declaration)
    | .relation declaration =>
      declareItem .relation declaration.name declaration.pub file ns scopes
        declaration.staticParams declaration.whereClause (.relation declaration)
    | .contract declaration =>
      discard <| declare .contract none false file ns scopes none none (.contract declaration)
    | .scheme declaration =>
      discard <| declare .scheme (some declaration.name) declaration.pub file ns scopes none none
        (.scheme declaration)
    | .goal declaration =>
      discard <| declare .goal (some declaration.name) declaration.pub file ns scopes none none
        (.goal declaration)
    | .law declaration =>
      declareItem .law declaration.name false file ns scopes declaration.staticParams
        declaration.whereClause (.law declaration)
    | .staticName declaration =>
      discard <| declare .staticName (some declaration.name) declaration.pub file ns scopes none
        none (.staticName declaration)

  partial def addModule (file : FileId) (ns : NamespaceId) (scopes : Array ScopeId)
      (declaration : Module) : AssembleM Unit := do
    let .«module» _ pub name parameters _ whereClause body := declaration
    let id := (← get).declarations.size
    let inner ← newNamespace (some ns) id file
    let own ←
      if parameters.isSome || whereClause.isSome then
        some <$> newScope .«module» file inner scopes.back? parameters whereClause
      else pure none
    discard <| declare .«module» (some name) pub file ns scopes own (some inner)
      (.«module» declaration)
    let chain := match own with
      | some scope => scopes.push scope
      | none => scopes
    match body with
    | .suite items =>
      for item in items do
        match item with
        | .item item => addItem file inner chain item
        | .moduleMember member =>
          discard <| declare .moduleDefinition (some member.name) false file inner chain none none
            (.moduleMember member)
        | .memberDef member =>
          discard <| declare .functionDefinition (some member.name) false file inner chain none
            none (.memberDef member)
    | .primitive _ | .asset _ => pure ()
end

/-- Adds a parsed file. A file whose header is the path of a file already added is refused
(NL4). `expected` is the path under which the library was asked for the file; a header that
names another path is refused. The result says whether the file was added. -/
def addFile (name : String) (tree : SourceFile) (fromLibrary : Bool) (expected : Option String) :
    AssembleM Bool := do
  let path := tree.tree.path.names.map (·.text)
  let key := pathText path
  if let some wanted := expected then
    if wanted != key then
      refuse "NL4" tree.tree.path.span
        s!"`{name}` is the file of the module `{wanted}`, and its header names `{key}`: the header of a file is the statement of its module path"
      modify fun state => { state with unreadable := state.unreadable.insert wanted }
      return false
  let state ← get
  if let some other := state.modules[key]? then
    let otherName := ((state.declarations[other]?).bind fun declaration =>
      (state.files[declaration.file]?).map (·.name)).getD ""
    refuse "NL4" tree.tree.path.span
      s!"`{key}` is already the module of the file `{otherName}`: no two files have one path"
    return false
  let file := state.files.size
  modify fun state => { state with
    files := state.files.push { name, path, tree, fromLibrary } }
  let id := (← get).declarations.size
  let ns ← newNamespace none id file
  let own ←
    if tree.tree.staticParams.isSome || tree.tree.whereClause.isSome then
      some <$> newScope .file file ns none tree.tree.staticParams tree.tree.whereClause
    else pure none
  discard <| declare .fileModule none true file ns #[] own (some ns) (.file tree.tree)
  modify fun state => { state with
    declarations := state.declarations.modify id fun declaration =>
      { declaration with name := some { span := tree.tree.path.span, text := key } }
    modules := state.modules.insert key id }
  let chain := match own with
    | some scope => #[scope]
    | none => #[]
  addItems file ns chain tree.tree.items
  return true

/-- Adds a source: its tree, or the refusal of the parser. -/
def addInput (input : SourceInput) (fromLibrary : Bool) (expected : Option String) :
    AssembleM Bool := do
  match input.parsed with
  | .ok tree => addFile input.name tree fromLibrary expected
  | .error error =>
    modify fun state => { state with log := state.log.add (Diagnostic.ofSyntax error) }
    if let some wanted := expected then
      modify fun state => { state with unreadable := state.unreadable.insert wanted }
    return false

/-- Loads the module that a path of a `use` names, when no file has it yet: the longest prefix
of the path that is a module. -/
def ensureModule {m : Type → Type} [Monad m] (load : Array String → m (Option SourceInput))
    (state : State) (names : Array String) : m State := do
  let mut state := state
  for shorter in [0:names.size] do
    let names := names.extract 0 (names.size - shorter)
    let key := pathText names
    if state.modules.contains key || state.unreadable.contains key || isVocabularyModule key then
      return state
    if state.missing.contains key then continue
    match ← load names with
    | none => state := { state with missing := state.missing.insert key }
    | some input =>
      let (_, next) := (addInput input true (some key)).run state
      return next
  return state

/-- The names that the prelude binds publicly. -/
def preludeNames (state : State) : Array String := Id.run do
  let some id := state.modules["zkc::prelude"]? | return #[]
  let some declaration := state.declarations[id]? | return #[]
  let some inner := declaration.inner | return #[]
  let some ns := state.namespaces[inner]? | return #[]
  let mut names := #[]
  for (name, binding) in ns.names.toList do
    let isPublic : Bool := match binding with
      | .declaration id => (state.declarations[id]?).any (·.pub)
      | .import id => (state.imports[id]?).any (·.pub)
    if isPublic then names := names.push name
  return names

/-- NL10: a module outside the core library declares no name that the prelude binds publicly; a
language item is declared, public and with its kind, in its module. A function of the fixed table
is no name of the prelude: a declaration with its name hides it in its module, as a local name
does. -/
def checkLanguageItems : AssembleM Unit := do
  let state ← get
  let prelude := preludeNames state
  for declaration in state.declarations do
    let some name := declaration.name | continue
    let some file := state.files[declaration.file]? | continue
    if coreModules.contains (pathText file.path) then continue
    let inModule := (state.namespaces[declaration.namespace]?).any fun ns =>
      (state.declarations[ns.owner]?).any fun owner =>
        owner.kind == .fileModule || owner.kind == .«module»
    let declares := match declaration.kind with
      | .fileModule | .contract | .functionDefinition | .moduleDefinition => false
      | _ => true
    if inModule && declares && prelude.contains name.text then
      refuse "NL10" name.span s!"`{name.text}` is a name of the prelude; a module does not declare it"
  for item in languageItems do
    let some moduleId := state.modules[item.module]? | continue
    let some moduleDeclaration := state.declarations[moduleId]? | continue
    let header := (moduleDeclaration.name.map (·.span)).getD default
    let message :=
      s!"the language item `{item.name}` is not declared as a public {item.description} of `{item.module}`"
    let binding := (moduleDeclaration.inner.bind fun inner =>
      (state.namespaces[inner]?).bind (·.names[item.name]?))
    match binding with
    | some (.declaration id) =>
      let some declaration := state.declarations[id]? | continue
      unless declaration.kind == item.kind && declaration.pub do
        refuse "NL10" ((declaration.name.map (·.span)).getD header) message
    | _ => refuse "NL10" header message

end Assemble

open Assemble in
/-- Assembles a program from the given sources and the library modules they reach. `load`
reads the library file of a module path, or answers that there is none. -/
def assemble {m : Type → Type} [Monad m] (inputs : Array SourceInput)
    (load : Array String → m (Option SourceInput)) : m Assembly := do
  let mut state : State := {}
  for input in inputs do
    state := ((addInput input false none).run state).2
  state ← ensureModule load state preludePath
  let mut cursor := 0
  while cursor < state.imports.size do
    let names := match state.imports[cursor]!.path with
      | .path _ segments => segments.map fun (.segment _ name _) => name.text
    state ← ensureModule load state names
    cursor := cursor + 1
  state := (checkLanguageItems.run state).2
  let program : Program :=
    { files := state.files, namespaces := state.namespaces, scopes := state.scopes
      declarations := state.declarations, imports := state.imports, modules := state.modules }
  return { program, log := state.log, unreadable := state.unreadable }

end Zkc.Frontend
