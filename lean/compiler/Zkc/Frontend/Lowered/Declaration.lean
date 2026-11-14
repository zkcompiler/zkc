module

public import Zkc.Frontend.Lowered.Tree

@[expose] public section

set_option autoImplicit false

/-!
# Lowered declarations

A declaration as every instance of it reads it: its head as written, with the types as terms,
and its body in the lowered form. This is the unit that is computed once per file and that
another file may depend on: a caller in another file instantiates the declaration from this
record and from nothing else of the file.

The derived declarations are already their kernel forms: a `relation` is a specification
function to `bool` over its statement parameters and then its witness parameters, with the
place of the split kept; a `law` is a specification function without a caller; the parameters
and the `where` of a `section` are those of the scopes of its members.
-/

namespace Zkc.Frontend.Lowered

open Syntax

/-- A sort of a bound: `nat`, `linear`, or an interface. -/
inductive SortTerm where
  | nat (span : Span)
  | linear (span : Span)
  | reference (reference : Reference)
  deriving Inhabited

/-- A constraint of a `where`, lowered. -/
inductive Constraint where
  | bound (span : Span) (subject : Expr) (sorts : Array SortTerm)
  | compare (span : Span) (operator : Operator) (left right : Expr)
  deriving Inhabited

/-- The bound of a static parameter: its sorts, and its place. -/
structure Bound where
  span : Span
  sorts : Array SortTerm
  deriving Inhabited

/-- A parameter scope, lowered: the bounds of its parameters and its `where`. -/
structure Scope where
  id : ScopeId
  /-- The bound of each parameter, in order. -/
  bounds : Array (Option Bound)
  constraints : Array Constraint
  deriving Inhabited

structure Parameter where
  binder : Binder
  type : TypeTerm
  deriving Inhabited

structure Port where
  binder : Binder
  type : TypeTerm
  /-- The holders; for a handle, the holders of its data. -/
  holders : RoleSet
  /-- For a handle placed `@H -> R`, the readers. -/
  readers : Option RoleSet := none
  isPrivate : Bool := false
  /-- A `spec` port: it has no holder and is in no emitted signature. -/
  specification : Bool := false
  deriving Inhabited

structure ResultPort where
  name : Name
  type : TypeTerm
  holders : RoleSet
  readers : Option RoleSet := none
  deriving Inhabited

/-- The head of a function, a relation, a law or a function member. -/
structure FunctionHead where
  parameters : Array Parameter
  /-- Absent for a function without a result type written: the empty tuple. -/
  result : Option TypeTerm
  /-- For a relation, the number of statement parameters: the witness parameters follow. -/
  statementParameters : Option Nat := none
  /-- A `spec def`, the formula of a relation, a law (SX1). -/
  specification : Bool := false
  /-- The name of `#[kernel("…")]` (FN5). -/
  kernel : Option String := none
  deriving Inhabited

/-- What a function is bound to. -/
inductive FunctionBody where
  /-- Statements and the returned value: a `block`, or one expression. -/
  | body (value : Expr)
  /-- `= primitive("row", args)` -/
  | primitive (span : Span) (row : String) (arguments : Array StaticArgument)
  /-- `= external("name")` -/
  | external (span : Span) (name : String)
  /-- A member of an interface: defined by the implementing modules. -/
  | absent
  deriving Inhabited

structure ProtocolHead where
  /-- The names of the roles, in the order of `roles(…)`. -/
  roster : Array String
  ports : Array Port
  results : Array ResultPort
  /-- The events of the body in the order of the text (EV3). -/
  events : Array SourceEvent
  specification : Bool := false
  deriving Inhabited

/-- What a declaration is, lowered. A kind that lowering does not rewrite yet keeps its syntax in
the record of its file and its resolved names here. -/
inductive Content where
  | function (head : FunctionHead) (body : FunctionBody)
  | protocol (head : ProtocolHead) (body : Array Stmt) (results : Array Expr)
  | alias (type : TypeTerm)
  /-- `type T = primitive("row", args)` -/
  | vocabularyType (row : String) (arguments : Array StaticArgument)
  | record (linear : Bool) (fields : Array (Name × TypeTerm))
  | «variant» (alternatives : Array (Name × Array TypeTerm))
  | staticName (value : Expr)
  /-- `def f(x, …)` in an implementing module: the parameters take the types of the member of
  the interface that it defines. -/
  | memberDefinition (parameters : Array Binder) (body : FunctionBody)
  /-- A kind that is not lowered yet (a module, an interface, a member that declares no
  definition, a contract, a scheme, a goal, an oracle function): its names, resolved, as terms. -/
  | unlowered (names : Array Expr)
  deriving Inhabited

structure Declaration where
  id : DeclarationId
  /-- The number of local binders: the binders are numbered from 0 below it. -/
  locals : Nat := 0
  /-- The local binders by number: what a message names a binder by. -/
  binders : Array Binder := #[]
  content : Content
  /-- A name of the declaration was refused: no instance of it is elaborated, and what depends
  on it reports nothing more. -/
  refused : Bool := false
  /-- The roles written that the roster does not have (HO3), in the order of the text. Such a
  role stands in the lowered form as the place one past the roster; elaboration refuses the
  first. -/
  unknownRoles : Array Name := #[]
  deriving Inhabited

end Zkc.Frontend.Lowered
