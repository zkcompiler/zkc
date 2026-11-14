module

public import Zkc.Frontend.Static.Infer
public import Zkc.Frontend.Static.Types
public import Zkc.Frontend.Typed.Tree
public import Zkc.Frontend.Semantics.Rows

@[expose] public section

set_option autoImplicit false

/-!
# The layer of elaboration

Elaboration turns the lowered body of a declaration, at an instance, into a typed tree. It runs
once per body, in a fresh state, in the static environment of the instance: a type or a static
term it meets is evaluated by the static layer below it.

Its context is the instance and how to reach the bodies of callees; its state is the local names
in scope with their types, and the binders it makes. The families of forms (terms, statements)
are files that do not import one another: each calls the others through `Recursion`, a record of
functions that travels beside the context and is tied once, where the families are put together.

Typing does not depend on facts (TY4). What a fact must justify (a conversion against the
widening, an application defined on a domain) is a node like any other; whether the role that
computes it has the fact is decided when its code is emitted. A refusal of elaboration abandons
the body, as the first refusal of a body does.
-/

namespace Zkc.Frontend.Elab

open Syntax
open Static

/-- A local name at the point reached. -/
structure Local where
  /-- The binder with the type the name has now: for a `mut` name, that of its last update. -/
  binder : Typed.Binder
  /-- A static name, or the index of an iteration typed on its own: its number. -/
  static? : Option Nat := none
  deriving Inhabited

structure Context where
  /-- The static environment of the instance. -/
  env : Env
  «instance» : InstanceId
  /-- How messages name the instance. -/
  name : String
  /-- Asks for the body of a callee from the place of a call, before its result is used. -/
  typeBody : InstanceId → Span → CompileM Unit := fun _ _ => pure ()
  /-- The body is a specification item (SX1): a `spec def`, the formula of a relation, a law. It
  may use `rational` and `spec type`s and call specification functions. -/
  specification : Bool := false
  /-- In the elaboration at the instance of a definition generic over a module parameter
  (SP12): the places that its opaque elaboration resolved to a member of the parameter's
  interface. -/
  resolutions : Std.HashMap Typing.ResolvedPlace ParameterRef := {}
  /-- The roster of the protocol whose body is elaborated; `none` in local code, where a
  statement has no role and an event does not stand (FN1). -/
  roster : Option (Array String) := none
  /-- Asks for the typed body of a protocol that the body applies, from the place of the
  application, before its results are used. -/
  protocolBody : InstanceId → Span → CompileM Unit := fun _ _ => pure ()

instance : Inhabited Context := ⟨{ env := default, «instance» := 0, name := "" }⟩

structure State where
  /-- The local names in scope, by binder. -/
  locals : Std.HashMap LocalId Local := {}
  /-- The indices of loops over static ranges that are typed as run-time naturals: where one
  stands in a static position, the body is typed per iteration (TY10). -/
  indices : Std.HashSet LocalId := {}
  /-- The indices of the iterations that are typed on their own: each stands for its number in
  a size, and is no size in a condition (TY9). -/
  iterationIndices : Std.HashSet LocalId := {}
  /-- The number of the next binder that elaboration makes. -/
  nextLocal : LocalId := 0
  /-- In the opaque elaboration, the places resolved to a member of an interface (SP12). -/
  resolved : Array (Typing.ResolvedPlace × ParameterRef) := #[]
  /-- Whether a binder of deployed code binds a linear value (LN1). -/
  linear : Bool := false
  /-- The operands bound to keep the order of evaluation, by binder: the nodes they stand for. -/
  operands : Std.HashMap LocalId Typed.Expr := {}
  /-- The names bound by a statement that was refused: a use of one makes no diagnostic. -/
  refused : Std.HashSet LocalId := {}
  /-- The names bound to the results of an application that has several: the binder of each
  result, by its name in the callee's head. `y.r` reads the result `r` (RM3). -/
  results : Std.HashMap LocalId (Array (String × Typed.Binder)) := {}
  /-- The names that only name the site of an application without results, and the names bound
  to several results (RM3): neither is a value. -/
  valueless : Std.HashMap LocalId String := {}
  /-- The `spec` ports: no role holds one, and it stands only in a specification expression
  (SX4). -/
  specificationPorts : Std.HashSet LocalId := {}
  deriving Inhabited

/-- The recursion between the families of forms, with the context and the state passed
explicitly so that the record does not mention the monad it is carried in. -/
structure Recursion where
  /-- An expression against the type expected of it, when one is. -/
  expr : Lowered.Expr → Option ClosedType → Context → State → CompileM (Typed.Expr × State)
  /-- The statements of a suite, in order, in the scope of the point reached; the names they
  bind stay for what follows. -/
  stmts : Array Lowered.Stmt → Context → State → CompileM (Array Typed.Stmt × State)

instance : Inhabited Recursion :=
  ⟨{ expr := fun _ _ _ _ => throw .abandoned, stmts := fun _ _ _ => throw .abandoned }⟩

/-- What the monad reads: the context and the recursion. -/
structure Scope where
  context : Context
  recursion : Recursion
  deriving Inhabited

abbrev ElabM := ReaderT Scope (StateT State CompileM)

instance {α : Type} : Inhabited (ElabM α) := ⟨throw .abandoned⟩

namespace ElabM

/-- Runs the elaboration of one body from a state. -/
def run {α : Type} (action : ElabM α) (scope : Scope) (state : State := {}) :
    CompileM (α × State) :=
  (ReaderT.run action scope).run state

end ElabM

def getContext : ElabM Context := return (← read).context

/-- Runs an action in a changed context. -/
def withContext {α : Type} (change : Context → Context) (action : ElabM α) : ElabM α :=
  withReader (fun scope => { scope with context := change scope.context }) action

/-- Elaborates an expression against the type expected of it, through the recursion. -/
def elabExprR (expr : Lowered.Expr) (expected : Option ClosedType := none) : ElabM Typed.Expr := do
  let scope ← read
  let (result, state) ← liftM (scope.recursion.expr expr expected scope.context (← get))
  set state
  return result

/-- Elaborates statements in the scope of the point reached, through the recursion. -/
def elabStmtsR (statements : Array Lowered.Stmt) : ElabM (Array Typed.Stmt) := do
  let scope ← read
  let (result, state) ← liftM (scope.recursion.stmts statements scope.context (← get))
  set state
  return result

/-! ## Refusals -/

/-- Refuses at a place: the refusal is logged and the statement abandoned. The statement is
then an error node, and the statements after it are elaborated (`elabStmts`). -/
def refuseHere {α : Type} (rule : String) (span : Span) (message : String) : ElabM α :=
  liftM (refuse rule span message : CompileM α)

/-- A form not typed yet: the body waits for it. -/
def waitFor {α : Type} (reason : String) : ElabM α := throw (.waiting reason)

/-- A form that lowering does not give elaboration: a defect of the frontend. -/
def unexpected {α : Type} (what : String) : ElabM α :=
  throw (.defect s!"elaboration does not expect {what}")

def renderTypeE (type : ClosedType) : ElabM String := liftM (renderTypeM type : CompileM String)

/-- The expression written at a place, as a message quotes it. -/
def textOf (span : Span) : ElabM String := liftM (textAt span : CompileM String)

/-- The sort whose rows give the function of an operator on a type of the sort (NL6). -/
def sortOfFunction : String → Option String
  | "add" | "sub" | "neg" | "equal" | "zero" => some "Group"
  | "mul" | "pow" | "one" => some "Ring"
  | "div" => some "Field"
  | _ => none

/-- The key of the place of an operator and the member it is (SP12). -/
def resolvedPlace (span : Span) (function : String) : Typing.ResolvedPlace :=
  (span.file, span.startByte, span.stopByte, function)

/-! ## Local names -/

/-- Runs an action in a suite: the names it binds do not stay. -/
def inSuite {α : Type} (action : ElabM α) : ElabM α := do
  let saved ← get
  let result ← action
  modify fun state => { state with locals := saved.locals, indices := saved.indices }
  return result

/-- Runs an action in a suite whose updates of `mut` names stay: the names it binds do not, and a
`mut` name declared before it leaves with the type its last update gave it (TY10). -/
def inSuiteKeeping {α : Type} (action : ElabM α) : ElabM α := do
  let saved ← get
  let result ← action
  let current ← get
  let mut locals := saved.locals
  for (id, entry) in saved.locals.toList do
    if entry.binder.mutable then
      if let some updated := current.locals[id]? then locals := locals.insert id updated
  modify fun state => { state with locals, indices := saved.indices }
  return result

/-- Sets the type a `mut` name has from here on. -/
def setLocalType (binder : LocalId) (type : ClosedType) : ElabM Unit :=
  modify fun state => { state with
    locals := state.locals.modify binder fun entry => { entry with binder := { entry.binder with type } } }

/-- Binds a local name of the lowered form at a type. -/
def bindLocal (binder : Lowered.Binder) (type : ClosedType) (static? : Option Nat := none)
    (mutable : Bool := false) (declared : Bool := false) : ElabM Typed.Binder := do
  let linear := !(← getContext).specification && isLinear (← getThe Compile.State) type
  let typed : Typed.Binder :=
    { id := binder.id, name := binder.name, span := binder.span, type, origin := binder.origin
      mutable := mutable || binder.mutable, declared, linear }
  modify fun state => { state with
    locals := state.locals.insert binder.id { binder := typed, static? }
    nextLocal := max state.nextLocal (binder.id + 1)
    linear := state.linear || linear }
  return typed

/-- A binder that elaboration makes. -/
def freshBinder (name : String) (span : Span) (type : ClosedType) (origin : BinderOrigin)
    (mutable : Bool := false) : ElabM Typed.Binder := do
  let state ← get
  let binder : Typed.Binder := { id := state.nextLocal, name, span, type, origin, mutable }
  set { state with nextLocal := state.nextLocal + 1
                   locals := state.locals.insert binder.id { binder } }
  return binder

/-- A binder of the lowered form that elaboration makes, for a form it writes out. -/
def madeBinder (name : String) (span : Span) (origin : BinderOrigin) : ElabM Lowered.Binder := do
  let state ← get
  set { state with nextLocal := state.nextLocal + 1 }
  return { id := state.nextLocal, name, span, origin }

/-- Stops where a stepped loop has more iterations than the budget allows (TY10): the check of
the body is incomplete. -/
def checkStepped (count : Nat) (span : Span) : ElabM Unit := do
  let limit := (← liftM (read : CompileM Compile.Context)).options.budgets.steppedIterations
  if limit < count then
    let name := (← getContext).name
    let exhaustion ← liftM (logExhaustion .steppedIterations { subject := .ofText name, span } :
      CompileM Exhaustion)
    throw (.exhausted exhaustion)

/-- The local name of a binder, in scope. -/
def localOf? (binder : LocalId) : ElabM (Option Local) := return (← get).locals[binder]?

/-- The static environment at the point reached: the instance's, with the static names and the
indices in scope, by their names. -/
def staticEnv : ElabM Env := do
  let context ← getContext
  let state ← get
  let mut locals := context.env.locals
  let mut indices := context.env.indices
  for (_, entry) in state.locals.toList do
    if let some value := entry.static? then locals := locals.insert entry.binder.name value
  for binder in state.indices.toList do
    if let some entry := state.locals[binder]? then indices := indices.insert entry.binder.name
  return { context.env with locals, indices }

/-- The requests for the typed bodies of instances. The tree of a function instance is made with
its code, when its body is asked for, and kept here; this request returns it, and waits for a
body that was not asked for yet. -/
def bodyQuery : Query InstanceId Typed.Definition where
  kind := .tree
  table := (·.trees)
  setTable := fun results table => { results with trees := table }
  instanceOf := fun _ id => id
  compute := fun _ _ => throw (.waiting "a typed body that is made when the body is asked for")

end Zkc.Frontend.Elab
