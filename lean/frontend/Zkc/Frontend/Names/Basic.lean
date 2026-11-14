module

public import Std.Data.HashSet
public import Zkc.Frontend.Syntax.Spans
public import Zkc.Frontend.Semantics.Assemble
public import Zkc.Frontend.Semantics.Resolution
public import Zkc.Frontend.Lowered.Declaration

@[expose] public section

set_option autoImplicit false

/-!
# The layer of names

The layer of names walks every declaration of an assembled program once, with an environment:
the namespace it is read in, the static parameters in scope, the interface whose `Self` it may
name, and the facts that the `where` clauses in scope state about static things. Resolving a
name and writing the lowered node that stands for it are one act: every function of the walk
returns the lowered form of what it resolved, and the table of resolutions is read off the
lowered form afterwards.

Local names live in the state, as a stack of suites; each binder is numbered in its declaration,
and a use of a local name names its binder. Refusals are collected per owner (a declaration, a
scope of a section, an import), and the first of each owner in source order is kept: what
follows it in the same owner may depend on it.
-/

namespace Zkc.Frontend.Names

open Syntax
open Lowered (Binder)

instance : Inhabited Segment := ⟨.segment default default none⟩

/-- What a refusal is collected under. -/
inductive Owner where
  | declaration (id : DeclarationId)
  | scope (id : ScopeId)
  | «import» (id : ImportId)
  deriving Inhabited, BEq, Hashable

/-- The root of a static path: a static parameter, or `Self` in an interface. -/
inductive StaticRoot where
  | parameter (reference : ParameterRef)
  | self (interface : DeclarationId)
  deriving Inhabited, BEq, Hashable

/-- A static parameter or `Self`, followed by the names of type and module members:
`G::Scalar`, `Self::Units`. -/
structure StaticPath where
  root : StaticRoot
  members : Array String
  deriving Inhabited, BEq, Hashable

namespace StaticPath

def push (path : StaticPath) (member : String) : StaticPath :=
  { path with members := path.members.push member }

def parent? (path : StaticPath) : Option (StaticPath × String) :=
  path.members.back?.map fun last => ({ path with members := path.members.pop }, last)

end StaticPath

/-- What the interfaces of a static thing are known to be. `open` says that a `where` equates
it with something whose members the text does not determine: a member that none of the
interfaces declares is then left to the instance. -/
structure Known where
  interfaces : Array DeclarationId := #[]
  «open» : Bool := false
  deriving Inhabited

namespace Known

def union (a b : Known) : Known :=
  { interfaces := b.interfaces.foldl (init := a.interfaces) fun acc id =>
      if acc.contains id then acc else acc.push id
    «open» := a.open || b.open }

end Known

/-- One side of an equality of a `where`. -/
inductive FactSubject where
  | path (path : StaticPath)
  | other
  deriving Inhabited

/-- What a constraint of a `where` says of static things. -/
inductive Fact where
  /-- `subject: B + C`: the subject has the interfaces of the bound. -/
  | bound (subject : StaticPath) (known : Known)
  /-- `left == right`. -/
  | equal (left right : FactSubject)
  deriving Inhabited

/-- What the steps of a path so far stand for. -/
inductive Target where
  /-- A file module or a nested module. -/
  | «module» (id : DeclarationId)
  | vocabularyModule (path : String)
  /-- Any other declaration found in a namespace. -/
  | declaration (id : DeclarationId)
  /-- A static parameter, `Self`, or a type, natural or module member of one. -/
  | static (path : StaticPath)
  /-- A function, protocol or law member reached through a static thing. -/
  | member (id : DeclarationId)
  /-- A member that the text does not determine: of a declared type, of a module bound to the
  vocabulary, of a member left to the instance. Its own members are left to the instance too. -/
  | «open»
  | alternative
  /-- A generated member (§8). -/
  | generated
  /-- A local name, a function of the fixed table, a role, a word, an entry: no member. -/
  | value
  /-- What a refused import or an unreadable module stands for: nothing more is refused. -/
  | poisoned
  deriving Inhabited

/-- A step as lookup finds it: the step, the static arguments written on its segment as the
syntax holds them, and the import that fixes them. -/
structure WrittenSegment where
  step : Step
  staticArgs : Option StaticArgs
  fixedBy : Option ImportId := none
  deriving Inhabited

/-- The steps and what they stand for. -/
structure Found where
  segments : Array WrittenSegment
  target : Target
  deriving Inhabited

/-- Where a path stands, for the lookup of a name that is not bound. -/
inductive Position where
  /-- In a type, a static term, a bound, a path that names a declaration. -/
  | plain
  /-- In an expression or a `case`, where a bare alternative of a variant may stand. -/
  | value
  deriving Inhabited, BEq

/-- The environment of a declaration. -/
structure Env where
  owner : Owner
  file : FileId
  «namespace» : NamespaceId
  /-- The parameter scopes in scope, outermost first. -/
  scopes : Array ScopeId
  /-- The static parameters in scope by name; an inner scope hides an outer one. -/
  parameters : Std.HashMap String ParameterRef
  /-- The interface whose `Self` and members are in scope. -/
  interface? : Option DeclarationId := none
  /-- A member definition: its own name is not in scope in it (SP8). -/
  excluded? : Option DeclarationId := none
  /-- A module without a body: the members of its interfaces are named bare in its `where`
  (SP4). -/
  host? : Option DeclarationId := none
  /-- What the `where` clauses in scope state. -/
  facts : Array Fact := #[]
  deriving Inhabited

inductive ImportState where
  | inProgress
  | done (found : Found)
  | failed
  deriving Inhabited

/-- A local name in scope: the place of its binding, whether the binding names the site of an
event, and its binder. -/
structure Local where
  span : Span
  site : Bool
  binder : LocalId
  deriving Inhabited

structure State where
  program : Program
  unreadable : Std.HashSet String
  /-- The first refusal of each owner in source order. -/
  refusals : Std.HashMap Owner Diagnostic := {}
  imports : Std.HashMap ImportId ImportState := {}
  /-- The imports being resolved, innermost last. -/
  importStack : Array ImportId := #[]
  /-- The steps of the path of an import, without the listed name: they stand even when the
  name is refused. -/
  importPaths : Std.HashMap ImportId (Array WrittenSegment) := {}
  /-- The static arguments of the path of a `use`, lowered once, by their file and first byte. -/
  importArguments : Std.HashMap (FileId × UInt32) (Array Lowered.StaticArgument) := {}
  /-- The local names in scope. -/
  locals : Std.HashMap String Local := {}
  /-- The names that each open suite binds, innermost last. -/
  suites : Array (Array String) := #[]
  /-- The binders in scope that stand for a static natural: static names and indices of ranges
  typed per iteration. -/
  statics : Std.HashSet LocalId := {}
  /-- The binders of the declaration being lowered, by number. -/
  binders : Array Binder := #[]
  /-- The events of the protocol being lowered, in the order of the text (EV3). -/
  events : Array SourceEvent := #[]
  /-- The roster of the protocol being lowered. -/
  roster : Array String := #[]
  /-- The roles written that the roster does not have (HO3). -/
  unknownRoles : Array Name := #[]
  /-- The names of the alternatives of every variant of the program. -/
  alternatives : Std.HashSet String := {}
  prelude? : Option NamespaceId := none
  /-- `Layout` of `zkc::layout`, whose implementing modules have generated members. -/
  layout? : Option DeclarationId := none
  parameterKnown : Std.HashMap ParameterRef Known := {}
  requirements : Std.HashMap DeclarationId (Array DeclarationId) := {}
  requirementsInProgress : Std.HashSet DeclarationId := {}
  interfaceFacts : Std.HashMap DeclarationId (Array Fact) := {}
  /-- What is known of the static paths asked about while one path is looked up, each computed
  once. A result is kept only when computing it met no path that was being computed. -/
  knownPaths : Std.HashMap StaticPath Known := {}
  /-- Whether the lookup under way met a path that was being computed. -/
  knownCut : Bool := false
  memberKnown : Std.HashMap DeclarationId Known := {}
  moduleKnown : Std.HashMap DeclarationId Known := {}
  moduleKnownInProgress : Std.HashSet DeclarationId := {}
  /-- The static terms of the comments `// instantiate: m<args>`, by file, resolved in the
  scope of their file module, with their lowered form. -/
  instantiations : Array (FileId × Expr × Lowered.Expr) := #[]
  /-- For each protocol, the names in scope at each of its loops, by the loop's index. -/
  loopScopes : Std.HashMap DeclarationId (Std.HashMap String (Array String)) := {}
  deriving Inhabited

abbrev ResolveM := StateM State

def program : ResolveM Program := return (← get).program

def declaration? (id : DeclarationId) : ResolveM (Option Declaration) :=
  return (← get).program.declarations[id]?

/-- Keeps the refusal when it is the first of its owner in source order. -/
def refuse (owner : Owner) (refusal : Diagnostic) : ResolveM Unit :=
  modify fun state =>
    match state.refusals[owner]? with
    | some earlier =>
      if refusal.span.startByte < earlier.span.startByte then
        { state with refusals := state.refusals.insert owner refusal }
      else state
    | none => { state with refusals := state.refusals.insert owner refusal }

def refuseAt (owner : Owner) (rule : String) (span : Span) (message : String) : ResolveM Unit :=
  refuse owner { origin := .names, rule, span, message := .ofText message }

/-! ## Local names and binders -/

/-- Starts the lowering of a declaration: no binder, no event, no roster. -/
def startDeclaration : ResolveM Unit :=
  modify fun state => { state with
    locals := {}, suites := #[#[]], statics := {}, binders := #[], events := #[], roster := #[]
    unknownRoles := #[] }

/-- Starts the local names of a definition; the binders of the declaration stay numbered. -/
def startLocals : ResolveM Unit :=
  modify fun state => { state with locals := {}, suites := #[#[]], statics := {} }

def pushSuite : ResolveM Unit :=
  modify fun state => { state with suites := state.suites.push #[] }

def popSuite : ResolveM Unit :=
  modify fun state =>
    match state.suites.back? with
    | none => state
    | some names =>
      { state with
        locals := names.foldl (init := state.locals) fun locals name => locals.erase name
        statics := names.foldl (init := state.statics) fun statics name =>
          match state.locals[name]? with
          | some binding => statics.erase binding.binder
          | none => statics
        suites := state.suites.pop }

/-- A new binder of the declaration. -/
def newBinder (name : String) (span : Span) (origin : BinderOrigin := .written)
    (mutable : Bool := false) : ResolveM Binder := do
  let state ← get
  let binder : Binder := { id := state.binders.size, name, span, origin, mutable }
  set { state with binders := state.binders.push binder }
  return binder

/-- A binder that lowering makes: no source names it. -/
def madeBinder (span : Span) (origin : BinderOrigin) : ResolveM Binder := do
  newBinder s!"%{(← get).binders.size}" span origin

/-- Puts a binder in scope in the innermost suite under its name. -/
def enterLocal (name : Name) (binder : LocalId) (site : Bool) (static : Bool) : ResolveM Unit :=
  modify fun state => { state with
    locals := state.locals.insert name.text { span := name.span, site, binder }
    suites := state.suites.modify (state.suites.size - 1) (·.push name.text)
    statics := if static then state.statics.insert binder else state.statics }

/-- Binds a local name in the innermost suite (NL2): a name already in scope, or the name of a
static parameter in scope, is not bound again. `site` says that the name is the one-name binder
of an event, which names its site: two events of one definition that share a name are refused
by the rule of sites (EV3), which covers events in sibling suites too, and not here. A binder is
made whether or not the name is bound. -/
def bindLocal (env : Env) (name : Name) (site : Bool := false) (mutable : Bool := false)
    (static : Bool := false) : ResolveM Binder := do
  let binder ← newBinder name.text name.span (mutable := mutable)
  let state ← get
  if let some earlier := state.locals[name.text]? then
    unless site && earlier.site do
      refuseAt env.owner "NL2" name.span
        s!"`{name.text}` is already bound at line {earlier.span.startLine}; a local name is bound once"
  else if env.parameters.contains name.text then
    refuseAt env.owner "NL2" name.span
      s!"`{name.text}` is a static parameter here and occurs in types; a binder does not shadow it"
  else enterLocal name binder.id site static
  return binder

/-- Binds a local name without the checks of NL2: a name a clause reads from the protocol. -/
def addLocal (name : String) (span : Span) : ResolveM Binder := do
  let binder ← newBinder name span
  enterLocal { span, text := name } binder.id false false
  return binder

/-! ## Roles -/

/-- The place of a role in the roster; a role that the roster does not have is listed, and stands
as the place one past the roster. -/
def roleOf (name : Name) : ResolveM Nat := do
  let state ← get
  match state.roster.findIdx? (· == name.text) with
  | some place => return place
  | none =>
    set { state with unknownRoles := state.unknownRoles.push name }
    return state.roster.size

def holdersOf : Holders → ResolveM RoleSet
  | .role name => return RoleSet.single (← roleOf name)
  | .roles _ names => do
    let mut roles := RoleSet.empty
    for name in names do roles := roles.insert (← roleOf name)
    return roles

/-! ## Names of declarations -/

def declarationName (program : Program) (id : DeclarationId) : String :=
  program.nameOf id

/-- How a message names what a declaration is. -/
def kindWord : DeclarationKind → String
  | .fileModule | .«module» => "a module"
  | .interface => "an interface"
  | .alias => "an alias"
  | .vocabularyType => "a type of the vocabulary"
  | .specType => "a specification type"
  | .record => "a record"
  | .«variant» => "a variant"
  | .function | .functionMember | .functionDefinition => "a function"
  | .oracleFunction => "an oracle function"
  | .protocol | .protocolMember => "a protocol"
  | .relation => "a relation"
  | .staticName | .naturalMember => "a natural"
  | .law | .lawMember => "a law"
  | .contract => "a contract"
  | .scheme => "a scheme"
  | .goal => "a goal"
  | .typeMember => "a type member"
  | .moduleMember | .moduleDefinition => "a module member"

/-- The text of a path up to and including segment `index`. -/
def pathPrefixText (path : Path) (index : Nat) : String :=
  match path with
  | .path _ segments =>
    "::".intercalate ((segments.extract 0 (index + 1)).toList.map fun (.segment _ name _) => name.text)

def segmentsOf : Path → Array Segment
  | .path _ segments => segments

def segmentName : Segment → Name
  | .segment _ name _ => name

def segmentArgs : Segment → Option StaticArgs
  | .segment _ _ args => args

/-- Whether a declaration is a module with an interface bound. -/
def implementing? (declaration : Declaration) : Option Bound :=
  match declaration.node with
  | .«module» (.«module» _ _ _ _ bound _ _) => bound
  | _ => none

/-- Whether a module has no suite: it is bound to the vocabulary or to an asset. -/
def hasNoBody (declaration : Declaration) : Bool :=
  match declaration.node with
  | .«module» (.«module» _ _ _ _ _ _ (.suite _)) => false
  | .«module» _ => true
  | _ => false

/-- The roles of the roster of a protocol or a protocol member. -/
def roster (declaration : Declaration) : Array String :=
  match declaration.node with
  | .protocol node => node.head.roles.map (·.text)
  | .member (.protocolMember head) => head.roles.map (·.text)
  | _ => #[]

end Zkc.Frontend.Names
