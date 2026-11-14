module

public import Std.Data.HashMap
public import Zkc.Frontend.Syntax.Tree

@[expose] public section

set_option autoImplicit false

/-!
# The program: files, namespaces, parameter scopes, declarations

A program is the files given to the tool and the library modules they reach. Two structures
lie over its declarations, and they are separate because a `section` has static parameters and
no name:

- a *namespace* holds names: a file module, a nested module, an interface. The items of a
  section are in the namespace of the module around it;
- a *parameter scope* holds static parameters and a `where`: a file module, a nested module, a
  section, an interface, and a declaration with parameters of its own (SP1).

A declaration is in one namespace and under a chain of parameter scopes, outermost first.
Everything here is found without looking at a body.
-/

namespace Zkc.Frontend

open Syntax

abbrev FileId := Nat
abbrev NamespaceId := Nat
abbrev ScopeId := Nat
abbrev DeclarationId := Nat
abbrev ImportId := Nat

/-- One source file of the program. -/
structure SourceUnit where
  /-- The name under which the file was read; spans carry it. -/
  name : String
  /-- The module path of the header, one string per name. -/
  path : Array String
  tree : SourceFile
  /-- The file was found in the library directory, not given to the tool. -/
  fromLibrary : Bool
  deriving Inhabited

/-- What a declaration is. The first group are the items of the grammar; the second the members
of an interface; the third the two items that stand only in an implementing module. -/
inductive DeclarationKind where
  | fileModule | «module» | interface
  | alias | vocabularyType | specType | record | «variant»
  | function | oracleFunction | protocol | relation
  | staticName | law | contract | scheme | goal
  | typeMember | naturalMember | moduleMember | functionMember | protocolMember | lawMember
  | moduleDefinition | functionDefinition
  deriving Inhabited, BEq, Repr

/-- The syntax node of a declaration. -/
inductive DeclarationSyntax where
  | file (node : File)
  | «module» (node : Module)
  | interface (node : Interface)
  | typeDecl (node : TypeDecl)
  | struct (node : Struct)
  | enum (node : Enum)
  | «def» (node : Def)
  | oracleDef (node : OracleDef)
  | protocol (node : Protocol)
  | relation (node : Relation)
  | staticName (node : StaticName)
  | law (node : Law)
  | contract (node : Contract)
  | scheme (node : Scheme)
  | goal (node : Goal)
  /-- a member of an interface -/
  | member (node : Member)
  /-- `module Name = Path` in an implementing module -/
  | moduleMember (node : ModuleMember)
  /-- `def f(x…)` in an implementing module -/
  | memberDef (node : MemberDef)
  deriving Inhabited

/-- Where a parameter scope comes from. -/
inductive ScopeOrigin where
  | file | «module» | «section» | interface | declaration
  deriving Inhabited, BEq, Repr

/-- Static parameters and a `where`. Either may be absent, not both, except for the scope of a
file module or a module, which exists whenever the module has one of them. -/
structure ParameterScope where
  origin : ScopeOrigin
  file : FileId
  /-- The namespace in which the parameters' bounds and the `where` are read: the module's own
  for a file module and a module, the interface's own for an interface and its members, the
  namespace around for a section and a declaration. -/
  «namespace» : NamespaceId
  /-- The scope around, absent for the outermost. -/
  parent : Option ScopeId
  parameters : Array StaticParam
  whereClause : Option Where
  deriving Inhabited

/-- A static parameter: its scope and its position in the scope. -/
structure ParameterRef where
  scope : ScopeId
  index : Nat
  deriving Inhabited, BEq, Hashable, Repr

/-- What a name of a namespace is bound to. -/
inductive Binding where
  | declaration (id : DeclarationId)
  | «import» (id : ImportId)
  deriving Inhabited, BEq, Repr

/-- One name bound by a `use`. `use a::b` and `use a::b as c` bind one name to the path;
`use a::b::{X, y}` binds each listed name to the path extended by it. Static arguments on a
segment of the path are fixed for every use of the name (SP2); they are evaluated under the
scopes of the place where the `use` stands. -/
structure Import where
  file : FileId
  /-- The namespace in which the `use` stands and whose name it binds. -/
  «namespace» : NamespaceId
  /-- The parameter scopes around the `use`, outermost first. -/
  scopes : Array ScopeId
  pub : Bool
  path : Path
  /-- For `use a::b::{X, y}`, the listed name; the bound name is then this one. -/
  selected : Option Name
  /-- The name bound. -/
  name : Name
  deriving Inhabited

/-- A namespace: the names of a file module, a nested module or an interface. -/
structure Namespace where
  /-- The namespace around, absent for a file module. -/
  parent : Option NamespaceId
  /-- The module or interface whose namespace this is. -/
  owner : DeclarationId
  file : FileId
  names : Std.HashMap String Binding
  deriving Inhabited

/-- A declaration. -/
structure Declaration where
  kind : DeclarationKind
  /-- Absent for a contract, which names the definition it is for. -/
  name : Option Name
  pub : Bool
  file : FileId
  /-- The namespace that holds its name. For a file module, its own. -/
  «namespace» : NamespaceId
  /-- The parameter scopes it is under, outermost first; its own is last when it has one. -/
  scopes : Array ScopeId
  /-- Its own parameter scope, when it has static parameters or a `where` of its own. -/
  ownScope : Option ScopeId
  /-- For a module or an interface, the namespace of its items. -/
  inner : Option NamespaceId
  node : DeclarationSyntax
  deriving Inhabited

/-- The program as assembled from its files. -/
structure Program where
  files : Array SourceUnit := #[]
  namespaces : Array Namespace := #[]
  scopes : Array ParameterScope := #[]
  declarations : Array Declaration := #[]
  imports : Array Import := #[]
  /-- The file modules by their path, written `a::b::c`. -/
  modules : Std.HashMap String DeclarationId := {}
  deriving Inhabited

namespace Program

/-- The static parameters of a declaration with their references, outermost scope first. -/
def parameters (program : Program) (declaration : Declaration) :
    Array (ParameterRef × StaticParam) := Id.run do
  let mut result := #[]
  for scope in declaration.scopes do
    let parameters := (program.scopes[scope]?.map (·.parameters)).getD #[]
    for index in [0:parameters.size] do
      result := result.push (⟨scope, index⟩, parameters[index]!)
  return result

/-- Whether the namespace `inner` is `outer` or lies inside it. -/
def within (program : Program) (inner outer : NamespaceId) : Bool := Id.run do
  let mut current := some inner
  for _ in [0:program.namespaces.size + 1] do
    match current with
    | none => return false
    | some id =>
      if id == outer then return true
      current := (program.namespaces[id]?).bind (·.parent)
  return false

/-- The name a declaration is written with, or the empty text for a contract. -/
def nameOf (program : Program) (id : DeclarationId) : String :=
  ((program.declarations[id]?).bind (·.name)).map (·.text) |>.getD ""

end Program

/-- A module path as text: its names joined by `::`. -/
def pathText (names : Array String) : String := "::".intercalate names.toList

end Zkc.Frontend
