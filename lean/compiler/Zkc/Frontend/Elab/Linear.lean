module

public import Zkc.Frontend.Typed.Tree

@[expose] public section

set_option autoImplicit false

/-!
# The uses of linear values (LN1, LN2)

A value of a linear type is used exactly once on every path (LN1). Elaboration marks the binders
of linear values; this pass reads the checked tree of a body in the order of evaluation and counts
the uses of each: a read of a linear binder is a use. A statement computed by several roles is one
use, at all of them (LN2).

- A binder used a second time is refused; so is a body that ends, or a region that ends, while a
  binder bound in it still owes its use.
- A binder bound outside a loop is not used inside it, whether the loop is typed once or one
  iteration at a time, and the element of a repetition `[v; s]` is in a loop over its copies.
- The arms of a choice, the cases of a `match` and the right operand of `and` and `or` (which is
  evaluated only when needed) are paths: each uses the same binders bound before it, and a binder
  bound in one is used in it.
- An update `x := e` consumes the value of `x` and assigns a new one, in one statement.
-/

namespace Zkc.Frontend.Linear

open Syntax (Span)
open Typed

/-- A linear binder that is bound: its name and place, or those of the update that gave its
value, whether it was used, the depth of the loops around its binder, and the binder's own place,
which an update keeps. -/
structure Owed where
  name : String
  binder : Span
  used : Bool := false
  depth : Nat
  origin : Span
  deriving Inhabited

structure LinearState where
  /-- By name, as the source writes it: one binding of a name is in scope (NL2). -/
  owed : Std.HashMap String Owed := {}
  /-- The names of the binders bound so far. -/
  names : Std.HashMap LocalId String := {}
  /-- The loops around the point reached. -/
  depth : Nat := 0
  deriving Inhabited

abbrev LinearM := StateT LinearState (Except (Span × String))

def fail {α : Type} (span : Span) (message : String) : LinearM α := throw (span, message)

def neverUsed (entry : Owed) : String :=
  s!"`{entry.name}` (line {entry.binder.startLine}) is never opened, returned or passed on"

def sameSpan (a b : Span) : Bool := a.file == b.file && a.startByte == b.startByte

/-- A read of a binder: a use when its value is linear. -/
def use (binder : LocalId) (span : Span) : LinearM Unit := do
  let state ← get
  let some name := state.names[binder]? | return
  let some entry := state.owed[name]? | return
  if entry.depth < state.depth then
    fail span s!"`{entry.name}` (line {entry.binder.startLine}) is used inside a loop outside its scope; a linear value is used exactly once"
  if entry.used then
    fail span s!"`{entry.name}` is used twice (it was bound at line {entry.binder.startLine}); a linear value is used exactly once"
  set { state with owed := state.owed.insert name { entry with used := true } }

/-- A binder: it owes a use when its value is linear. -/
def bind (binder : Binder) : LinearM Unit := do
  let state ← get
  if let some old := state.owed[binder.name]? then
    unless old.used do fail old.binder (neverUsed old)
  let owed := if binder.linear then
      state.owed.insert binder.name
        { name := binder.name, binder := binder.span, depth := state.depth, origin := binder.span }
    else state.owed.erase binder.name
  set { state with owed, names := state.names.insert binder.id binder.name }

/-- The binders bound in a region that ends, used in it: a region of a path or a loop. A binder
bound before it and updated in it is not bound in it. -/
def closeRegion (before : LinearState) : LinearM Unit := do
  for (binder, entry) in (← get).owed.toList do
    let outer := (before.owed[binder]?).any fun earlier => sameSpan earlier.origin entry.origin
    unless outer || entry.used do fail entry.binder (neverUsed entry)

/-- A loop: the binders bound outside it are not used inside it, and those bound inside it are
used in each iteration. -/
def inLoop (action : LinearM Unit) : LinearM Unit := do
  let before ← get
  set { before with depth := before.depth + 1 }
  action
  closeRegion { before with depth := before.depth + 1 }
  set before

/-- Paths of which one is taken: each uses the same binders bound before them (LN2). -/
def paths (span : Span) (arms : Array (LinearM Unit)) : LinearM Unit := do
  let before ← get
  let mut afters : Array LinearState := #[]
  for arm in arms do
    set before
    arm
    closeRegion before
    afters := afters.push (← get)
  let mut owed := before.owed
  for (binder, entry) in before.owed.toList do
    let states := afters.map fun after => after.owed[binder]?
    let used := states.map fun state => state.any (·.used)
    if used.any id && used.any (!·) then
      fail span s!"`{entry.name}` (line {entry.binder.startLine}) is used on one path of this choice and not on another; both arms of a choice use the same linear names"
    if let some (some first) := states[0]? then owed := owed.insert binder first
  set { before with owed }

mutual
  partial def expr : Expr → LinearM Unit
    | .literal .. | .staticValue .. => pure ()
    | .local info binder => use binder info.span
    -- the element of `[v; s]` is in a loop over its copies
    | .apply _ (.operation .seqFill) #[element] => inLoop (expr element)
    | .apply _ _ arguments => arguments.forM expr
    | .construct _ _ parts => parts.forM expr
    | .project _ target _ _ => expr target
    | .convert _ _ value _ => expr value
    | .conditional info .and a b _ => do
      expr a
      paths info.span #[expr b, pure ()]
    | .conditional info .or a _ b => do
      expr a
      paths info.span #[expr b, pure ()]
    | .conditional info .ifThenElse condition onTrue onFalse => do
      expr condition
      paths info.span #[expr onTrue, expr onFalse]
    | .block _ body result => do
      statements body
      expr result
    | .error _ evaluated => evaluated.forM expr

  partial def statements (body : Array Stmt) : LinearM Unit := body.forM statement

  partial def statement : Stmt → LinearM Unit
    | .bind _ binder value _ => do
      expr value
      bind binder
    | .unpack _ binders value _ => do
      expr value
      for binder in binders do
        if let some binder := binder then bind binder
    | .update mark target value _ => do
      expr value
      let state ← get
      let some name := state.names[target]? | return
      if let some entry := state.owed[name]? then
        unless entry.used do fail mark.span (neverUsed entry)
        set { state with owed := state.owed.insert name { entry with binder := mark.span, used := false } }
    | .guard _ condition _ _ => expr condition
    | .«if» mark condition onTrue onFalse _ => do
      expr condition
      paths mark.span #[statements onTrue, statements onFalse]
    | .«match» mark scrutinee binder _ cases _ => do
      -- the matched value is bound, and the `match` reads it
      expr scrutinee
      if let some binder := binder then
        bind binder
        use binder.id scrutinee.span
      paths mark.span (cases.map fun (.case _ _ payload body) => do
        for binder in payload do
          if let some binder := binder then bind binder
        statements body)
    | .«for» _ (.loop index domain collected body) _ => do
      match domain with
      | .range start stop _ => do expr start; expr stop
      | .collection source _ _ => expr source
      let item : Option Binder := match domain with
        | .collection _ item _ => some item
        | .range .. => none
      let iteration (statementsOf : Array Stmt) (values : Array Expr) : LinearM Unit := inLoop do
        bind index
        if let some item := item then bind item
        statements statementsOf
        values.forM expr
      match body with
      | .uniform statementsOf values => iteration statementsOf values
      | .empty .. => pure ()
      | .stepped iterations =>
        for (.iteration _ statementsOf values) in iterations do iteration statementsOf values
      collected.forM bind
    | .scope _ body => statements body
    | .event _ _ what => do
      -- what an event reads is used; what it binds owes a use
      match what with
      | .send binder payload _ _ => do
        expr payload
        if let some binder := binder then bind binder
      | .draw binder .. | .sample binder .. | .attempt binder .. =>
        if let some binder := binder then bind binder
      | .apply results _ arguments _ _ order => do
        -- the arguments are used in the order written
        for position in order do
          if let some argument := arguments[position]? then expr argument
        for binder in results do
          if let some binder := binder then bind binder
    | .error _ binders => binders.forM bind
end

/-- Checks the uses of the linear binders of a function body: its parameters, its statements and
what it returns. The first fault, with its place and message. -/
def check (body : FunctionBody) : Except (Span × String) Unit := do
  let action : LinearM Unit := do
    body.parameters.forM bind
    statements body.statements
    expr body.result
    for (_, entry) in (← get).owed.toList do
      unless entry.used do fail entry.binder (neverUsed entry)
  discard <| action.run {}

/-- Checks the uses of the linear binders of a protocol body: its ports, its statements and
its results. A value with several holders is used once by one statement, at all of them (LN2).
The first fault, with its place and message. -/
def checkProtocol (body : ProtocolBody) : Except (Span × String) Unit := do
  let action : LinearM Unit := do
    for port in body.ports do
      unless port.specification do bind port.binder
    statements body.statements
    for result in body.results do expr result.value
    for (_, entry) in (← get).owed.toList do
      unless entry.used do fail entry.binder (neverUsed entry)
  discard <| action.run {}

end Zkc.Frontend.Linear
