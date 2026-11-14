module

public import Zkc.Frontend.Typed.Tree
public import Zkc.Frontend.Static.Types

@[expose] public section

set_option autoImplicit false

/-!
# The invariants of a typed tree

What every typed tree satisfies, checked on the tree alone. A violation is a defect of the
elaborator, not a refusal of the program: the passes and the emission read the tree as if these
held.

- **Scope.** A read of a name stands after its binder, on its path.
- **The type of a read.** A read has the type that the name has at that point: the binder's
  for an immutable name; for a `mut` name the type of its last binding or update, and after a
  control statement the type that the statement leaves it at.
- **Types from parts.** The condition of a conditional is a `bool` and its arms have its type;
  a block has the type of its result; a conversion converts between the two types it stands
  between.
- **Control.** A control statement lists the `mut` names declared before it that its suites
  update, each once, with the type each has after it; every arm, and a uniform body, ends with
  each of them at that type.
- **Loops.** A body gives one value per collected name; the iterations of a stepped loop are
  numbered from zero in order.
- **Matches.** No alternative is covered by two cases.
- **Local code.** The body of a function has no event and writes no role.
- **Binders.** A binder's number is below the count of the definition.
-/

namespace Zkc.Frontend.Passes

open Syntax (Span)
open Typed

structure Violation where
  span : Span
  message : String
  deriving Inhabited

namespace WellFormed

structure State where
  /-- The names in scope, each with the type it has at the point reached, and whether it is
  `mut`. -/
  scope : Std.HashMap LocalId (ClosedType × Bool) := {}
  violations : Array Violation := #[]

structure Context where
  /-- One more than the largest number of a binder of the definition. -/
  locals : Nat
  /-- The body is local code: no event, no written role. -/
  function : Bool

abbrev CheckM := ReaderT Context (StateM State)

def violate (span : Span) (message : String) : CheckM Unit :=
  modify fun state => { state with violations := state.violations.push { span, message } }

def bind (binder : Binder) : CheckM Unit := do
  unless binder.id < (← read).locals do
    violate binder.span s!"the binder `{binder.name}` has the number {binder.id}, which the definition does not count"
  modify fun state => { state with scope := state.scope.insert binder.id (binder.type, binder.mutable) }

/-- Whether a conversion stands between two types that it converts. -/
partial def converts : Conversion → ClosedType → ClosedType → Bool
  | .unsized, .seq a (some _), .seq b none => Static.typeEq a b
  | .indexToNat, .index _, .nat => true
  | .widenIndex, .index low, .index high => low ≤ high
  | .fromNonzero, .nonzero field, target => Static.typeEq field target
  | .sized, .seq a none, .seq b (some _) => Static.typeEq a b
  | .bounded, .nat, .index _ | .bounded, .index _, .index _ => true
  | .nonzero, source, .nonzero field => Static.typeEq source field
  | .elements inner, .seq a m, .seq b n => m == n && converts inner a b
  | .components inner, .tuple sources _, .tuple targets _ =>
    sources.size == targets.size && (List.range sources.size).all fun index =>
      match (inner[index]?).join with
      | some part => converts part sources[index]! targets[index]!
      | none => Static.typeEq sources[index]! targets[index]!
  | .empty, source, .seq _ size => Static.isEmptyCollection source && (size == some 0 || size == none)
  | .andThen first middle second, source, target => converts first source middle && converts second middle target
  | _, _, _ => false

/-- Runs a suite: the names it binds do not stay, and each `mut` name from before keeps the
type the suite leaves it at. -/
def inSuite (action : CheckM Unit) : CheckM Unit := do
  let before := (← get).scope
  action
  modify fun state => { state with
    scope := before.fold (init := before) fun scope binder (type, mutable) =>
      match state.scope[binder]? with
      | some (now, _) => if mutable then scope.insert binder (now, mutable) else scope.insert binder (type, mutable)
      | none => scope }

/-- The carried names of a control statement have, where a suite ends, the types that the
statement leaves them at. -/
def checkEnds (span : Span) (control : Control) (what : String) : CheckM Unit := do
  let scope := (← get).scope
  for (binder, type) in control.updates.zip control.carried do
    if let some (now, _) := scope[binder]? then
      unless Static.typeEq now type do
        violate span s!"{what} ends with the carried name #{binder} at a type other than the statement leaves it at"

/-- Sets the carried names to the types the statement leaves them at. -/
def leave (control : Control) : CheckM Unit :=
  modify fun state => { state with
    scope := (control.updates.zip control.carried).foldl (init := state.scope) fun scope (binder, type) =>
      scope.modify binder fun (_, mutable) => (type, mutable) }

mutual
  partial def expr : Expr → CheckM Unit
    | .literal .. | .staticValue .. => pure ()
    | .local info binder => do
      match (← get).scope[binder]? with
      | some (type, _) =>
        unless Static.typeEq type info.type do
          violate info.span s!"a read of #{binder} at a type other than the name has here"
      | none => violate info.span s!"a read of #{binder}, which is not bound here"
    | .apply _ _ arguments => arguments.forM expr
    | .construct _ _ parts => parts.forM expr
    | .project _ target _ _ => expr target
    | .convert info conversion value _ => do
      expr value
      unless converts conversion value.type info.type do
        violate info.span "a conversion between two types that it does not convert"
    | .conditional info _ condition onTrue onFalse => do
      expr condition
      unless Static.typeEq condition.type .bool do violate info.span "a condition that is no `bool`"
      -- names bound inside an arm do not leave it
      inSuite (expr onTrue)
      inSuite (expr onFalse)
      unless Static.typeEq onTrue.type info.type && Static.typeEq onFalse.type info.type do
        violate info.span "a conditional whose arms do not have its type"
    | .block info statements result => do
      let before := (← get).scope
      stmts statements
      expr result
      unless Static.typeEq result.type info.type do violate info.span "a block that does not have the type of its result"
      -- the names of a block do not leave it; a `mut` name from outside keeps what the block left
      modify fun state => { state with
        scope := before.fold (init := before) fun scope binder (type, mutable) =>
          match state.scope[binder]? with
          | some (now, _) => scope.insert binder (if mutable then now else type, mutable)
          | none => scope }
    | .error _ evaluated => evaluated.forM expr

  partial def stmts (statements : Array Stmt) : CheckM Unit := statements.forM stmt

  partial def stmt : Stmt → CheckM Unit
    | .bind mark binder value placement => do
      expr value
      if (← read).function && placement.written.isSome then violate mark.span "a role written in local code"
      unless Static.typeEq value.type binder.type do
        violate mark.span s!"`{binder.name}` is bound at a type other than its value has"
      bind binder
    | .unpack mark binders value placement => do
      expr value
      if (← read).function && placement.written.isSome then violate mark.span "a role written in local code"
      for binder in binders do
        if let some binder := binder then bind binder
    | .update mark target value _ => do
      expr value
      match (← get).scope[target]? with
      | some (_, true) =>
        modify fun state => { state with scope := state.scope.insert target (value.type, true) }
      | some (_, false) => violate mark.span s!"an update of #{target}, which is not `mut`"
      | none => violate mark.span s!"an update of #{target}, which is not bound here"
    | .guard mark condition _ placement => do
      expr condition
      if (← read).function && placement.written.isSome then violate mark.span "a role written in local code"
      unless Static.typeEq condition.type .bool do violate mark.span "a guard on what is no `bool`"
    | .if mark condition onTrue onFalse control => do
      expr condition
      checkControl mark.span control (onTrue ++ onFalse)
      for arm in #[onTrue, onFalse] do
        inSuite do
          stmts arm
          checkEnds mark.span control "an arm"
        -- each arm starts from the types before the statement
      leave control
    | .match mark scrutinee binder _ cases control => do
      expr scrutinee
      checkControl mark.span control (cases.foldl (init := #[]) fun all (.case _ _ _ body) => all ++ body)
      let mut covered : Array Nat := #[]
      for (.case _ alternatives _ _) in cases do
        for alternative in alternatives do
          if covered.contains alternative then violate mark.span s!"two cases cover the alternative {alternative}"
          covered := covered.push alternative
      for (.case _ _ payload body) in cases do
        inSuite do
          if let some binder := binder then bind binder
          for binder in payload do
            if let some binder := binder then bind binder
          stmts body
          checkEnds mark.span control "a case"
      leave control
    | .for mark (.loop index domain collected body) control => do
      match domain with
      | .range start stop _ => do expr start; expr stop
      | .collection source _ _ => expr source
      let bindItem : CheckM Unit := do
        bind index
        if let .collection _ item _ := domain then bind item
      let iteration (statements : Array Stmt) (values : Array Expr) : CheckM Unit := do
        bindItem
        stmts statements
        unless values.size == collected.size do
          violate mark.span "a body that does not give one value per collected name"
        values.forM expr
      match body with
      | .uniform statements values =>
        checkControl mark.span control statements
        inSuite do
          iteration statements values
          checkEnds mark.span control "a uniform body"
      | .stepped iterations =>
        checkControl mark.span control (iterations.foldl (init := #[]) fun all (.iteration _ inner _) => all ++ inner)
        let mut position := 0
        for (.iteration number statements values) in iterations do
          unless number == position do violate mark.span "iterations that are not numbered in order"
          inSuite (iteration statements values)
          position := position + 1
      | .empty .. => pure ()
      leave control
      collected.forM bind
    | .scope _ body => inSuite (stmts body)
    | .event mark _ what => do
      if (← read).function then violate mark.span "an event in local code"
      match what with
      | .send binder payload _ _ => do
        expr payload
        if let some binder := binder then bind binder
      | .draw binder .. | .sample binder .. | .attempt binder .. =>
        if let some binder := binder then bind binder
      | .apply results _ arguments specification _ _ => do
        arguments.forM expr
        specification.forM fun (_, value) => expr value
        for binder in results do
          if let some binder := binder then bind binder
    | .error _ binders => binders.forM bind

  /-- A control statement lists exactly the `mut` names declared before it that its suites
  update, each with the type it leaves it at. -/
  partial def checkControl (span : Span) (control : Control) (suites : Array Stmt) : CheckM Unit := do
    let scope := (← get).scope
    let updated := (updatedIn suites).filter fun binder => (scope[binder]?).any (·.2)
    unless control.carried.size == control.updates.size do
      violate span "a control statement that does not give a type for each name it carries"
    for binder in updated do
      unless control.updates.contains binder do
        violate span s!"a control statement that updates #{binder} and does not list it"
    for binder in control.updates do
      unless updated.contains binder do
        violate span s!"a control statement that lists #{binder}, which its suites do not update"
end

end WellFormed

/-- The violations of the invariants in the tree of a definition. -/
def violations (definition : Definition) : Array Violation :=
  let run (function : Bool) (action : WellFormed.CheckM Unit) : Array Violation :=
    ((action.run { locals := definition.locals, function }).run {}).2.violations
  match definition.body with
  | .function body => run true do
      body.parameters.forM WellFormed.bind
      WellFormed.stmts body.statements
      WellFormed.expr body.result
  | .protocol body => run false do
      for port in body.ports do WellFormed.bind port.binder
      WellFormed.stmts body.statements
      for result in body.results do WellFormed.expr result.value
  | .row _ | .external _ => #[]

end Zkc.Frontend.Passes
