module

public import Zkc.Frontend.Typed.Basic

@[expose] public section

set_option autoImplicit false

/-!
# The typed tree

The body of a definition at an instance, in kernel forms (§4.1 of the reference) and nothing
else. Elaboration makes it from the lowered form; the passes, the emission to the core, and the
tools read it, and nothing changes it. Every node has a mark: its place, its number in the
definition, and what elaboration made it for when the source did not write it. Every expression
has its closed type.

**One tree for local code and for protocol bodies.** A function body is the body of the one
role that runs it: the same expressions, the same bindings, guards and control. A protocol body
adds events, and what the source writes of roles: the roles after `@` on a binding and on a
guard, the sender after `from`, the holders of ports and results. Elaboration needs no role.
The roles that compute a statement, the participants of a choice or a loop, the holders of a
binder and the sender of a send are computed by the placement pass (HO1, HO2, CT1, EV5) and
kept in its tables, by the number of the node. Whether a conditional is a local `if` or a
`choose`, and a loop a local loop or a `repeat`, follows from those tables, so `if`, `match`
and `for` are typed by one elaborator.

**`mut` names stay names.** A `mut` name is a binder, an update is a statement, and a read is a
`local` like any other, whose type is the type the name has at that point (TY10). A control
statement lists the `mut` names from outside that its suites update; where an arm or a body ends
with such a name at a narrower type than the name has afterwards, elaboration ends the suite
with an update that widens it. The carried values of a loop and the results of the arms of a
choice are read off these lists at emission.

**One loop.** A `for` has one typed body when every iteration types alike (a uniform loop, and
every loop with a run-time count), and one typed body per iteration, in order, when it is
stepped or its index is static in the body (TY10). A loop of no iteration has no body at the
instance; its body typed apart is kept beside it. A comprehension and a fold over naturals,
`bool` or a declared type are a `block` whose statements are that loop: a loop that collects,
or a `mut` accumulator and a loop that updates it. A fold over elements of a sort is the
application of its row to the collection.

**Errors.** A statement that could not be elaborated is `Stmt.error`, with the names it would
have bound. An expression that could not be elaborated is `error` with the type that was
expected of it, and the operands evaluated before it. A diagnostic about an expression with an
`error` among its operands is not made. A body with an `error` is no part of a package; the
check of its facts reports what stands before the first `error` in the order of the tree.

**The opaque elaboration** of a definition generic over a module parameter (SP12) is a tree of
the same type. It differs in two places: a type member of the parameter is the type `opaque`,
and an operator, a form or a dot call on a value of such a type is an application of
`Callee.member`. It is the generic definition that is kept beside the instance.

**Provenance.** What elaboration makes for a derived form says what it is for, where a rule of
the language is stated on the source form: the origin of a binder (a binder made for a pattern,
an iteration number, `_`, the result of an application bound to no name) and, for an
accumulator, what it accumulates (`Accumulation`: the fold it is of, or a comprehension).
-/

namespace Zkc.Frontend.Typed

open Syntax

mutual
  inductive Expr where
    | literal (info : Info) (value : Literal)
    /-- A static natural that stands as a value. -/
    | staticValue (info : Info) (value : Nat) (source : StaticSource)
    | «local» (info : Info) (binder : LocalId)
    | apply (info : Info) (callee : Callee) (arguments : Array Expr)
    /-- `local.make`, `local.variant`. -/
    | construct (info : Info) (what : Construction) (parts : Array Expr)
    /-- `local.get`: a component of a tuple or a field of a record, by position. `name` is what
    the source reads the part by, `r.f` or `t.1`. A part taken by indexing or by a pattern has
    none. -/
    | project (info : Info) (target : Expr) (position : Nat) (name : Option String)
    /-- A conversion of `value` to the type of the node (TY5), at the place of the node; `quote`
    is what a refusal of it at emission quotes. -/
    | convert (info : Info) (conversion : Conversion) (value : Expr) (quote : Quote)
    /-- `local.if` with one value per arm. An `and` or an `or` is this node with a literal
    arm. -/
    | conditional (info : Info) (form : ConditionalForm) (condition onTrue onFalse : Expr)
    /-- Statements, then a value. -/
    | block (info : Info) (statements : Array Stmt) (result : Expr)
    /-- What could not be elaborated, at the type expected of it, with the operands evaluated
    before it: emission evaluates them, and refuses there with the refusal elaboration held, unless
    one of them is refused first. -/
    | error (info : Info) (evaluated : Array Expr)

  inductive Stmt where
    /-- `x = e`, `mut x = e`. -/
    | bind (mark : Mark) (binder : Binder) (value : Expr) (placement : Placement)
    /-- The components of a tuple, the fields of a record in the order of its declaration, or the
    payload of a variant of one alternative: every binder at once; `none` takes nothing (a field
    the pattern does not name), and `_` is a binder whose origin is `discarded`. Taking a linear
    record apart is its one use. -/
    | unpack (mark : Mark) (binders : Array (Option Binder)) (value : Expr)
        (placement : Placement)
    | update (mark : Mark) (target : LocalId) (value : Expr) (placement : Placement)
    /-- `local.guard`. In a protocol body each role of the placement performs it on its own
    copy of the condition. -/
    | guard (mark : Mark) (condition : Expr) (reason : Zkc.Core.Reason) (placement : Placement)
    | «if» (mark : Mark) (condition : Expr) (onTrue onFalse : Array Stmt) (control : Control)
    /-- `match` on a value of a variant: every alternative is covered by one case. The matched
    value is evaluated once, before the cases. When it has a `binder`, the value is bound to
    it, and a case that names the value reads it by that binder. The binding is part of the
    statement: in a protocol body the participants of the `match` compute it, and no other
    holder of the value does. -/
    | «match» (mark : Mark) (scrutinee : Expr) (binder : Option Binder) («variant» : InstanceId)
        (cases : Array Case) (control : Control)
    | «for» (mark : Mark) (loop : Loop) (control : Control)
    /-- The arm that a static condition takes (TY9): its statements, with their own scope of
    names and of facts. It is no choice and has no participants. -/
    | scope (mark : Mark) (body : Array Stmt)
    /-- An event of a protocol body, with its number in the text. -/
    | event (mark : Mark) (event : EventId) (what : Event)
    /-- A statement that could not be elaborated. Its refusal is reported; the names it would
    have bound are bound by `binders`, and a use of one makes no further diagnostic. -/
    | error (mark : Mark) (binders : Array Binder)

  /-- One case of a `match`: the alternatives it covers (one for a case that names an
  alternative, the remaining ones for a case that covers every value), the binders of the
  payload, and the body. -/
  inductive Case where
    | «case» (span : Span) (alternatives : Array Nat) (payload : Array (Option Binder))
        (body : Array Stmt)

  /-- A loop: the index, what it ranges over, the names bound after it to what it collects
  (TY16), and its body or bodies. -/
  inductive Loop where
    | loop (index : Binder) (domain : Domain) (collected : Array Binder) (body : LoopBody)

  inductive Domain where
    /-- `a..b`. `count` is `b - a` when both bounds are static. -/
    | range (start stop : Expr) (count : Option Nat)
    /-- A collection, evaluated once; `item` is bound to its element in each iteration, and
    the index is the iteration number. `size` is that of a sized collection. -/
    | collection (source : Expr) (item : Binder) (size : Option Nat)

  inductive LoopBody where
    /-- One typing for every iteration: the statements, and the value of each collected name
    at the end of an iteration. -/
    | uniform (body : Array Stmt) (values : Array Expr)
    /-- One typing per iteration, in order. -/
    | stepped (iterations : Array Iteration)
    /-- A loop of no iteration: nothing of it exists at the instance. Its body typed apart is
    kept, with the value of each collected name, for what a collected name has after the loop:
    the element type of its value (TY16) and its holders (HO2). The body is no part of the
    program: it is not emitted and not run, and a type in it may name an instance that only the
    typing apart made. When the body does not type apart there is none, and a collected name is
    `[]`. -/
    | empty (body : Array Stmt) (values : Array Expr)

  /-- One iteration of a stepped loop: the value of the index, the statements, and the value
  of each collected name. -/
  inductive Iteration where
    | iteration (index : Nat) (body : Array Stmt) (values : Array Expr)

  inductive Event where
    /-- `sender` is the role written after `from`; when none is written the placement pass
    finds the sender (EV5). The receivers are in the order written. -/
    | send (binder : Option Binder) (payload : Expr) (sender : Option Nat)
        (receivers : Array Nat)
    /-- `law` is the sampling row of the law at its type (TY15). -/
    | draw (binder : Option Binder) (law : RowRef) (sender : Nat) (receivers : Array Nat)
    | sample (binder : Option Binder) (law : RowRef) (role : Nat)
    | attempt (binder : Option Binder) (role : Nat)
    /-- An application of a protocol instance: one binder per result of the callee, the
    arguments in the order of the ports that are not `spec`, the `spec` arguments by their
    ports, and the total role map: the caller's role for each role of the callee (RM1). `order`
    gives the arguments in the order written, by their places among the ports: a role
    evaluates the arguments it computes in that order (HO4). -/
    | apply (results : Array (Option Binder)) (callee : InstanceId) (arguments : Array Expr)
        (specification : Array (String × Expr)) (roleMap : Array Nat) (order : Array Nat)
end

instance : Inhabited Expr := ⟨.error default #[]⟩
instance : Inhabited Stmt := ⟨.scope default #[]⟩
instance : Inhabited Loop := ⟨.loop default (.range default default none) #[] (.uniform #[] #[])⟩

namespace Expr

def info : Expr → Info
  | .literal info _ | .staticValue info .. | .local info _ | .apply info .. | .construct info ..
  | .project info .. | .convert info .. | .conditional info .. | .block info .. | .error info .. =>
    info

def span (expr : Expr) : Span := expr.info.span

def type (expr : Expr) : ClosedType := expr.info.type

end Expr

mutual
  /-- Whether an expression contains an error node. -/
  partial def Expr.hasError : Expr → Bool
    | .error .. => true
    | .literal .. | .staticValue .. | .local .. => false
    | .apply _ _ arguments => arguments.any Expr.hasError
    | .construct _ _ parts => parts.any Expr.hasError
    | .project _ target _ _ => target.hasError
    | .convert _ _ value _ => value.hasError
    | .conditional _ _ condition onTrue onFalse =>
      condition.hasError || onTrue.hasError || onFalse.hasError
    | .block _ statements result => statements.any Stmt.hasError || result.hasError

  partial def Loop.hasError : Loop → Bool
    | .loop _ domain _ body =>
      (match domain with
        | .range start stop _ => start.hasError || stop.hasError
        | .collection source _ _ => source.hasError) ||
      (match body with
        | .uniform statements values => statements.any Stmt.hasError || values.any Expr.hasError
        | .stepped iterations => iterations.any fun (.iteration _ statements values) =>
            statements.any Stmt.hasError || values.any Expr.hasError
        | .empty .. => false)

  partial def Stmt.hasError : Stmt → Bool
    | .bind _ _ value _ | .unpack _ _ value _ | .update _ _ value _ => value.hasError
    | .guard _ condition _ _ => condition.hasError
    | .if _ condition onTrue onFalse _ =>
      condition.hasError || onTrue.any Stmt.hasError || onFalse.any Stmt.hasError
    | .match _ scrutinee _ _ cases _ =>
      scrutinee.hasError || cases.any fun (.case _ _ _ body) => body.any Stmt.hasError
    | .error .. => true
    | .for _ loop _ => loop.hasError
    | .scope _ body => body.any Stmt.hasError
    | .event _ _ what =>
      match what with
      | .send _ payload _ _ => payload.hasError
      | .apply _ _ arguments specification _ _ =>
        arguments.any Expr.hasError || specification.any (·.2.hasError)
      | .draw .. | .sample .. | .attempt .. => false
end

/-- The names that statements update, their nested suites included, each once in the order of
the first update. -/
partial def updatedIn (statements : Array Stmt) (found : Array LocalId := #[]) : Array LocalId :=
  statements.foldl (init := found) fun found statement =>
    match statement with
    | .update _ target _ _ => if found.contains target then found else found.push target
    | .if _ _ onTrue onFalse _ => updatedIn onFalse (updatedIn onTrue found)
    | .match _ _ _ _ cases _ => cases.foldl (init := found) fun found (.case _ _ _ body) => updatedIn body found
    | .for _ (.loop _ _ _ body) _ =>
      match body with
      | .uniform inner _ => updatedIn inner found
      | .stepped iterations => iterations.foldl (init := found) fun found (.iteration _ inner _) =>
          updatedIn inner found
      | .empty .. => found
    | .scope _ body => updatedIn body found
    | _ => found

/-- The body of a function instance. -/
structure FunctionBody where
  parameters : Array Binder
  statements : Array Stmt
  /-- The value of `return`, or of an expression body. -/
  result : Expr
  deriving Inhabited

/-- A port of a protocol at an instance: its binder and what the head says of it. A `spec`
port has no holder and is no operand of deployed code. -/
structure BodyPort where
  binder : Binder
  holders : RoleSet
  specification : Bool := false
  deriving Inhabited

/-- A result of a protocol at an instance: its value, and the roles that the head says hold
it, each of which computes its own copy. -/
structure BodyResult where
  name : String
  value : Expr
  holders : RoleSet
  deriving Inhabited

/-- The body of a protocol instance. -/
structure ProtocolBody where
  /-- The names of the roles, in roster order. -/
  roster : Array String
  /-- The ports, in the order of the head. -/
  ports : Array BodyPort
  statements : Array Stmt
  /-- The results, in the order of the head. `return` is the last line of a body (CT5), so it
  is no statement. -/
  results : Array BodyResult
  deriving Inhabited

inductive Body where
  | function (body : FunctionBody)
  | protocol (body : ProtocolBody)
  /-- Bound to a row of the vocabulary: a call applies the row. -/
  | row (row : RowRef)
  /-- Bound to the formal library: a header. -/
  | external (name : String)
  deriving Inhabited

namespace Body

def hasError : Body → Bool
  | .function body => body.statements.any Stmt.hasError || body.result.hasError
  | .protocol body => body.statements.any Stmt.hasError || body.results.any (·.value.hasError)
  | .row _ | .external _ => false

end Body

/-- What elaboration makes of the body of an instance. -/
structure Definition where
  «instance» : InstanceId
  body : Body
  /-- For a definition generic over a module parameter, its opaque elaboration: the generic
  definition, in which an operator on a type member is the member of the interface (SP12). -/
  generic : Option Body := none
  /-- One more than the largest number of a local binder. -/
  locals : Nat := 0
  /-- The count of the nodes of the body, once they are numbered. -/
  nodes : Nat := 0
  /-- A form of a later layer that the body or its signature needs: it is typed as far as it
  goes and is not emitted. -/
  waiting : Option String := none
  /-- The body applies an operation of specifications that has no form in the core. -/
  specificationOnly : Bool := false
  deriving Inhabited

namespace Definition

/-- Whether the body can be emitted as far as its own tree goes. -/
def emittable (definition : Definition) : Bool :=
  !definition.body.hasError && definition.waiting.isNone

end Definition

end Zkc.Frontend.Typed
