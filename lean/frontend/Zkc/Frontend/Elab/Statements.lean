module

public import Zkc.Frontend.Elab.Events
public import Zkc.Frontend.Semantics.Instantiate.Remake

@[expose] public section

set_option autoImplicit false

/-!
# The elaboration of statements

The statements of a `def` (FN1): bindings, `mut` declarations and updates, guards, `if`,
`match`, `for`. A static name is a binding of a size (TY2): it binds a number and makes no
statement; its uses stand for the number.

A `mut` name has, at each point, the type of its last update (TY10). A statement whose suites
update `mut` names declared before it lists them, and every suite ends with each of them at the
join of the types the suites leave it at: a suite that leaves one narrower ends with an update
that widens it. A pattern is one `unpack` per level; a nested level takes apart a binder that
lowering made.
-/

namespace Zkc.Frontend.Elab

open Syntax
open Static

/-- Why a statement of a protocol body stands in a `def`. -/
def roleless : String := "an event stands only in a protocol body; a `def` runs inside one role"

/-- What the source writes of the roles of a statement that computes: nothing in a `def`,
where a role is refused (FN1). -/
def placementOf (span : Span) (roles : Option RoleSet) : ElabM Typed.Placement := do
  if roles.isSome && (← getContext).roster.isNone then refuseHere "FN1" span roleless
  return { written := roles }

/-- The place of a statement. -/
def spanOf : Lowered.Stmt → Span
  | .bind span .. | .staticName span .. | .unpack span .. | .update span .. | .guard span ..
  | .«if» span .. | .«match» span .. | .«for» span .. | .event span .. | .waiting span .. => span

/-- The names that a statement binds for what follows it. -/
def bindersOf : Lowered.Stmt → Array Lowered.Binder
  | .bind _ binder .. | .staticName _ binder _ => #[binder]
  | .unpack _ _ binders .. => binders.filterMap id
  | .«for» _ _ collected _ => collected.map fun (.collected _ binder _) => binder
  | .event _ _ binder .. => binder.toArray
  | _ => #[]

/-- The local names that statements update with `:=`, nested suites included, each once in the
order written. -/
partial def updatedLocals (statements : Array Lowered.Stmt) : Array LocalId :=
  statements.foldl add #[]
where
  add (names : Array LocalId) : Lowered.Stmt → Array LocalId
    | .update _ (.local _ binder) _ => if names.contains binder then names else names.push binder
    | .«if» _ _ _ onTrue onFalse => onFalse.foldl add (onTrue.foldl add names)
    | .«match» _ _ cases => cases.foldl (init := names) fun names (.«case» _ _ body) => body.foldl add names
    | .«for» _ _ _ body => body.foldl add names
    | _ => names

/-- The `mut` names in scope that statements update. -/
def carriedBy (statements : Array Lowered.Stmt) : ElabM (Array LocalId) := do
  let state ← get
  return (updatedLocals statements).filter fun binder =>
    (state.locals[binder]?).any (·.binder.mutable)

/-- The types of `mut` names at the point reached. -/
def typesOf (carried : Array LocalId) : ElabM (Array ClosedType) := do
  let state ← get
  return carried.map fun binder => ((state.locals[binder]?).map (·.binder.type)).getD default

/-- The name of a local binder, for a message. -/
def nameOf (binder : LocalId) : ElabM String :=
  return (((← get).locals[binder]?).map (·.binder.name)).getD ""

/-- The join of the types of the carried names at the ends of several suites (TY10). -/
def joinEnds (span : Span) (carried : Array LocalId) (ends : Array (Array ClosedType)) :
    ElabM (Array ClosedType) := do
  let some first := ends[0]? | return #[]
  let mut types := first
  for types' in ends do
    for index in [0:types.size] do
      match join types[index]! types'[index]! with
      | some joined => types := types.set! index joined
      | none =>
        refuseHere "TY10" span
          s!"`{← nameOf carried[index]!}` is a `{← renderTypeE types[index]!}` at the end of one arm and a `{← renderTypeE types'[index]!}` at the end of another; they have no join"
  return types

/-- The updates that end a suite which leaves carried names narrower than their join: each is
widened where the suite ends (TY5). -/
def widening (span : Span) (carried : Array LocalId) (ends targets : Array ClosedType) :
    ElabM (Array Typed.Stmt) := do
  let mut updates := #[]
  for index in [0:carried.size] do
    let binder := carried[index]!
    unless typeEq ends[index]! targets[index]! do
      let use : Typed.Expr := .local { span, type := ends[index]! } binder
      let value ← convertTo use targets[index]! span (.text (← nameOf binder))
      updates := updates.push (.update (Typed.Mark.derived span .widening) binder value {})
  return updates

/-- Arms typed in their own suites: each with what binds its names first (which gives `α`), its
statements, and the widening updates that bring the carried names to their join. The carried
names have the join after them, which is returned with the arms. -/
def elabArms {α : Type} (span : Span) (carried : Array LocalId)
    (arms : Array (ElabM (α × Array Typed.Stmt) × Array Lowered.Stmt)) :
    ElabM (Array (α × Array Typed.Stmt) × Array ClosedType) := do
  let start ← typesOf carried
  let mut bodies := #[]
  let mut ends := #[]
  for (prepare, statements) in arms do
    let ((made, body), types) ← inSuite do
      let (made, prepared) ← prepare
      let body ← elabStmtsR statements
      return ((made, prepared ++ body), ← typesOf carried)
    bodies := bodies.push (made, body)
    ends := ends.push types
    -- each arm starts from the types before the statement
    for (binder, type) in carried.zip start do setLocalType binder type
  let joined ← joinEnds span carried ends
  let mut result := #[]
  for ((made, body), types) in bodies.zip ends do
    result := result.push (made, body ++ (← widening span carried types joined))
  for (binder, type) in carried.zip joined do setLocalType binder type
  return (result, joined)

/-- The carried names of a control statement and the types it leaves them at, without the
names that no suite of the statement updates at this instance: an update in an arm that a
static condition does not take is no update here (TY9). -/
def carriedIn (carried : Array LocalId) (types : Array ClosedType) (suites : Array Typed.Stmt) :
    Typed.Control :=
  let updated := Typed.updatedIn suites
  let kept := (carried.zip types).filter fun (binder, _) => updated.contains binder
  { updates := kept.map (·.1), carried := kept.map (·.2) }

/-- The binder of a pattern's place: a name, `_` (a binder made here, that binds nothing), or the
value that a nested level takes apart. -/
def patternBinder (binder : Option Lowered.Binder) (type : ClosedType) (span : Span) :
    ElabM Typed.Binder := do
  match binder with
  | some binder =>
    -- `_` does not match a linear value (LN3)
    if binder.origin == .discarded && !(← getContext).specification &&
        isLinear (← getThe Compile.State) type then
      refuseHere "LN3" binder.span "`_` does not match a linear value: open it, return it or pass it on"
    bindLocal binder type
  | none =>
    -- `_` does not match a linear value (LN3)
    if !(← getContext).specification && isLinear (← getThe Compile.State) type then
      refuseHere "LN3" span "`_` does not match a linear value: open it, return it or pass it on"
    freshBinder "_" span type .discarded

/-- One level of a pattern outside `case` (TY13): the components of a tuple, or the fields of a
record named by its declaration or an alias of its type. -/
def elabUnpack (span : Span) (shape : Lowered.UnpackShape) (binders : Array (Option Lowered.Binder))
    (typed : Typed.Expr) (placement : Typed.Placement := {}) : ElabM Typed.Stmt := do
  let typeText ← renderTypeE typed.type
  match shape, typed.type with
  | .tuple size, .tuple components _ =>
    unless components.size == size do
      refuseHere "TY13" span s!"the pattern has {size} items; the value has {components.size} components"
    let mut typedBinders := #[]
    for index in [0:size] do
      typedBinders := typedBinders.push (some (← patternBinder binders[index]! components[index]! span))
    return .unpack (Typed.Mark.derived span .pattern) typedBinders typed placement
  | .tuple _, _ => refuseHere "TY13" span s!"the pattern is a tuple; the value is a `{typeText}`"
  | .record reference declarationId fields, .record inst =>
    let .reference typeSpan segments := reference
    -- the pattern names the record's declaration, or an alias of its type (TY3)
    let found ← liftM (declaration declarationId : CompileM Declaration)
    let entry := (← getThe Compile.State).table.entries[inst]!
    let same ← if found.kind == .record then pure (entry.key.declaration == declarationId)
      else do
        let env ← staticEnv
        let value ← speculate do
          let thing ← liftM (evalSegments env segments typeSpan : CompileM Thing)
          liftM (thingValue env thing (some .type) typeSpan (pure "") : CompileM StaticValue)
        pure (match value with
          | some (.type (.record other)) => other == inst
          | _ => false)
    unless same do
      refuseHere "TY13" span s!"`{← textOf typeSpan}\{…}` does not match a `{typeText}`"
    let declared ← recordFields inst
    let mut typedBinders : Array (Option Typed.Binder) := declared.map fun _ => none
    for index in [0:fields.size] do
      let (fieldSpan, name) := fields[index]!
      let some position := declared.findIdx? (·.1 == name)
        | refuseHere "TY13" fieldSpan s!"`{typeText}` has no field `{name}`"
      let type := declared[position]!.2
      typedBinders := typedBinders.set! position (some (← patternBinder binders[index]! type span))
    -- a pattern on a linear record names every field: it is the one use of the record, and a
    -- field it does not name would be dropped (TY13, LN1)
    if !(← getContext).specification && isLinear (← getThe Compile.State) typed.type then
      for position in [0:declared.size] do
        if typedBinders[position]!.isNone then
          refuseHere "TY13" span
            s!"`{typeText}` is linear: a pattern on it names every field, and `{declared[position]!.1}` is not named"
    return .unpack (Typed.Mark.derived span .pattern) typedBinders typed placement
  | .record .., _ => refuseHere "TY13" span s!"the pattern is a record; the value is a `{typeText}`"
  | .results, _ => unexpected "the results of an application taken apart"

/-- The alternative a case names, or none for a case that covers every value. -/
def caseAlternative (inst : InstanceId) (alternatives : Array (String × Array ClosedType))
    (pattern : Lowered.CasePattern) (span : Span) : ElabM (Option Nat) := do
  let typeText ← renderTypeE (.«variant» inst)
  let byName (name : String) : ElabM (Option Nat) := do
    match alternatives.findIdx? (·.1 == name) with
    | some index => return some index
    | none => refuseHere "TY13" span s!"`{name}` is not an alternative of `{typeText}`"
  match pattern with
  | .alternative _ (.reference referenceSpan segments) _ =>
    match segments.back? with
    | some (.segment (.alternative «variant» index) _ _) =>
      let entry := (← getThe Compile.State).table.entries[inst]!
      unless entry.key.declaration == «variant» do
        refuseHere "TY13" span s!"`{← textOf referenceSpan}` is not an alternative of `{typeText}`"
      return some index
    | some (.segment (.bareAlternative name) _ _) => byName name
    | _ => refuseHere "TY13" span s!"`{← textOf referenceSpan}` is not an alternative of `{typeText}`"
  -- a case that is one name: an alternative of the matched variant when it has one of that
  -- name, otherwise a name for the matched value that covers every other alternative
  | .any _ (some binder) =>
    return if binder.origin == .written then alternatives.findIdx? (·.1 == binder.name) else none
  | .any .. => return none
  | _ => refuseHere "TY13" span s!"a case of `{typeText}` names one of its alternatives"

/-- The binder of a pattern inside a payload (TY13), and the levels that take it apart: it covers
every value of its type, since an alternative has one case. -/
partial def payloadBinder (pattern : Lowered.CasePattern) (type : ClosedType) (span : Span) :
    ElabM (Typed.Binder × Array Typed.Stmt) := do
  let typeText ← renderTypeE type
  match pattern with
  | .any patternSpan binder =>
    -- a name that is an alternative of the payload's variant is one value of it, unless the
    -- variant has no other
    if let (some name, .«variant» inst) := (binder, type) then
      let alternatives ← variantAlternatives inst
      if name.origin == .written && alternatives.size > 1 && alternatives.any (·.1 == name.name) then
        refuseHere "TY13" patternSpan
          s!"a pattern inside a payload covers every value of its type; `{name.name}` is one alternative of `{typeText}`"
    return (← patternBinder binder type patternSpan, #[])
  | .tuple patternSpan items =>
    let .tuple components _ := type
      | refuseHere "TY13" patternSpan s!"the pattern is a tuple; the value is a `{typeText}`"
    unless components.size == items.size do
      refuseHere "TY13" patternSpan s!"the pattern has {items.size} items; the value has {components.size} components"
    let made ← freshBinder "%pattern" patternSpan type .patternValue
    let mut binders := #[]
    let mut levels := #[]
    for index in [0:items.size] do
      let (binder, nested) ← payloadBinder items[index]! components[index]! span
      binders := binders.push (some binder)
      levels := levels ++ nested
    let use : Typed.Expr := .local { span := patternSpan, type } made.id
    return (made, #[.unpack patternSpan binders use {}] ++ levels)
  | .alternative patternSpan _ patterns =>
    let .«variant» inst := type
      | refuseHere "TY13" patternSpan s!"the pattern names an alternative; the value is a `{typeText}`"
    let alternatives ← variantAlternatives inst
    let some index ← caseAlternative inst alternatives pattern patternSpan | throw .abandoned
    if let some other := (List.range alternatives.size).find? (· != index) then
      refuseHere "TY13" patternSpan
        s!"`match` on `{typeText}` does not cover `{alternatives[other]!.1}`: a pattern inside a payload covers every value of its type"
    -- the payload of the one alternative, taken apart
    let made ← freshBinder "%pattern" patternSpan type .patternValue
    if patterns.isEmpty then return (made, #[])
    let payload := alternatives[index]!.2
    unless patterns.size == payload.size do
      refuseHere "TY13" patternSpan s!"the alternative has {payload.size} values; the case binds {patterns.size}"
    let mut binders := #[]
    let mut levels := #[]
    for position in [0:patterns.size] do
      let (binder, nested) ← payloadBinder patterns[position]! payload[position]! span
      binders := binders.push (some binder)
      levels := levels ++ nested
    let use : Typed.Expr := .local { span := patternSpan, type } made.id
    return (made, #[.unpack patternSpan binders use {}] ++ levels)
  | .record patternSpan (.reference typeSpan segments) fields =>
    let .record inst := type
      | refuseHere "TY13" patternSpan s!"the pattern is a record; the value is a `{typeText}`"
    -- the pattern names the record's declaration, or an alias of its type (TY3)
    let entry := (← getThe Compile.State).table.entries[inst]!
    let named : Bool := match segments.back? with
      | some (.segment (.declaration id) _ _) => id == entry.key.declaration
      | _ => false
    let same ← if named then pure true else do
      let env ← staticEnv
      let value ← speculate do
        let thing ← liftM (evalSegments env segments typeSpan : CompileM Thing)
        liftM (thingValue env thing (some .type) typeSpan (pure "") : CompileM StaticValue)
      pure (match value with
        | some (.type (.record other)) => other == inst
        | _ => false)
    unless same do
      refuseHere "TY13" patternSpan s!"`{← textOf typeSpan}\{…}` does not match a `{typeText}`"
    let declared ← recordFields inst
    let made ← freshBinder "%pattern" patternSpan type .patternValue
    let mut binders : Array (Option Typed.Binder) := declared.map fun _ => none
    let mut levels := #[]
    for (name, inner) in fields do
      let some position := declared.findIdx? (·.1 == name.text)
        | refuseHere "TY13" name.span s!"`{typeText}` has no field `{name.text}`"
      let (binder, nested) ← payloadBinder inner declared[position]!.2 span
      binders := binders.set! position (some binder)
      levels := levels ++ nested
    -- a pattern on a linear record names every field (TY13, LN1)
    if !(← getContext).specification && isLinear (← getThe Compile.State) type then
      for position in [0:declared.size] do
        if binders[position]!.isNone then
          refuseHere "TY13" patternSpan
            s!"`{typeText}` is linear: a pattern on it names every field, and `{declared[position]!.1}` is not named"
    let use : Typed.Expr := .local { span := patternSpan, type } made.id
    return (made, #[.unpack patternSpan binders use {}] ++ levels)
  | .literal patternSpan (.number _ value) =>
    refuseHere "TY13" patternSpan
      s!"a pattern inside a payload covers every value of its type; `{value}` is one value of `{typeText}`"
  | .literal patternSpan _ =>
    refuseHere "TY13" patternSpan
      s!"a pattern inside a payload covers every value of its type; a literal is one value of `{typeText}`"

mutual
  partial def elabStmts (statements : Array Lowered.Stmt) : ElabM (Array Typed.Stmt) := do
    let mut result := #[]
    for statement in statements do
      -- a statement that is refused is an error node: its refusal is reported already, the
      -- names it would have bound are bound, and the suite goes on
      let saved ← get
      try
        result := result ++ (← elabStmt statement)
      catch
        | .abandoned =>
          modify fun state => { state with locals := saved.locals, indices := saved.indices }
          let mut binders := #[]
          for binder in bindersOf statement do
            binders := binders.push (← bindLocal binder .unit)
            modify fun state => { state with refused := state.refused.insert binder.id }
          result := result.push (.error (spanOf statement) binders)
        | other => throw other
    return result

  partial def elabStmt (statement : Lowered.Stmt) : ElabM (Array Typed.Stmt) := do
    match statement with
    | .bind span binder type roles value =>
      let placement ← placementOf span roles
      match type with
      | some written =>
        let target ← liftM (evalType (← staticEnv) written : CompileM ClosedType)
        let converted ← elabAt value target
        bindValue span binder converted (declared := true) (placement := placement)
      | none =>
        if binder.origin == .written && !binder.mutable then
          if ← sizeSyntax value then
            -- a binding of a size is a static name: it stands for the number, and a size that
            -- cannot be evaluated refuses the instance (TY2)
            discard <| bindLocal binder .nat (static? := some (← staticSize value))
            return #[]
        bindValue span binder (← elabExpr value none) (placement := placement)
    | .staticName span binder value =>
      if ← sizeSyntax value then
        discard <| bindLocal binder .nat (static? := some (← staticSize value))
        return #[]
      bindValue span binder (← elabExpr value none)
    | .unpack span shape binders roles value =>
      let placement ← placementOf span roles
      -- the results of an application, taken by a tuple pattern in the order of the head (RM3)
      if let .local _ taken := value then
        if let some results := (← get).results[taken]? then
          if (← get).refused.contains taken then throw .abandoned
          let .tuple size := shape
            | refuseHere "TY13" span "the results of an application are bound by one name or a tuple pattern"
          unless size == results.size do
            refuseHere "TY13" span
              s!"the application returns {results.size} results; the pattern binds {size}"
          let mut bound := #[]
          for index in [0:size] do
            let (_, result) := results[index]!
            let use : Typed.Expr := .local { span, type := result.type } result.id
            match binders[index]! with
            | some binder =>
              bound := bound ++ (← bindValue span binder use (placement := placement) (derivation := .pattern))
            | none =>
              if !(← getContext).specification && isLinear (← getThe Compile.State) result.type then
                refuseHere "LN3" span "`_` does not match a linear value: open it, return it or pass it on"
          return bound
      return #[← elabUnpack span shape binders (← elabExpr value none) placement]
    | .update span target value =>
      let .local _ binder := target | throw .abandoned
      let some entry := (← get).locals[binder]? | throw .abandoned
      unless entry.binder.mutable do
        refuseHere "GR3" span s!"`:=` updates a `mut` name; `{entry.binder.name}` is not one"
      if entry.binder.declared then
        return #[.update span binder (← elabAt value entry.binder.type) {}]
      -- a `mut` name without a written type has the type of its last update: the update is typed
      -- without an expected type (TY10, SP6 step 6)
      let typed ← elabExpr value none
      setLocalType binder typed.type
      return #[.update span binder typed {}]
    | .guard span roles condition reason =>
      let placement ← placementOf span roles
      -- in a protocol body a guard names the roles that perform it (GU2)
      if roles.isNone && (← getContext).roster.isSome then
        refuseHere "GU2" span
          s!"a guard in a protocol body names its roles: write `guard @V {← textOf condition.span}`, or `guard @(P, V) …` if all check"
      -- a guard on a conjunction is a guard on each conjunct, in order: it stops where the
      -- conjunction is false, each conjunct has the facts of those before it, and the suite after
      -- it has the facts of all
      match condition with
      | .conditional _ .and a b _ =>
        return (← elabStmt (.guard span roles a reason)) ++ (← elabStmt (.guard span roles b reason))
      | .operator notSpan .not #[.conditional _ .or a _ b] =>
        return (← elabStmt (.guard span roles (.operator notSpan .not #[a]) reason)) ++
          (← elabStmt (.guard span roles (.operator notSpan .not #[b]) reason))
      | _ => return #[.guard span (← elabBool condition) reason placement]
    | .«if» span _ condition onTrue onFalse =>
      if let some taken ← staticCondition? condition then
        return #[.scope span (← inSuiteKeeping (elabStmts (if taken then onTrue else onFalse)))]
      let test ← elabBool condition
      let carried ← carriedBy (onTrue ++ onFalse)
      let nothing : ElabM (Unit × Array Typed.Stmt) := pure ((), #[])
      let (arms, joined) ← elabArms span carried #[(nothing, onTrue), (nothing, onFalse)]
      return #[.«if» span test arms[0]!.2 arms[1]!.2 (carriedIn carried joined (arms[0]!.2 ++ arms[1]!.2))]
    | .«match» span scrutinee cases => elabMatch span scrutinee cases
    | .«for» span generator collected body => elabFor span generator collected body
    | .event span event binder type roles what => elabEvent span event binder type roles what
    | .waiting span reason _ =>
      if (← getContext).roster.isNone then refuseHere "FN1" span roleless
      waitFor reason

  /-- `for p in D:` (TY10), and the names it collects (TY16). A uniform loop, and a loop with a
  run-time count, is one loop typed once: after it a collected name is a `[U; n]`, or a `[U]`
  for a run-time count. A stepped loop (a `mut` name changes type), and a loop whose index is
  static in its body, is its iterations in sequence, each typed with the index a static natural
  and every `mut` name at the type the one before left it; after it a collected name is the
  collection of its values when they have one type, otherwise their tuple. After a loop of no
  iteration a collected name is `[]`, at the type its expression has in the body typed apart. -/
  partial def elabFor (span : Span) (generator : Lowered.Generator)
      (collected : Array Lowered.Collected) (body : Array Lowered.Stmt) : ElabM (Array Typed.Stmt) := do
    let domain ← elabDomain generator
    checkRangeIndex domain body span
    let carried ← carriedBy body
    let start ← typesOf carried
    let valueOf : Lowered.Collected → Lowered.Expr := fun (.collected _ _ value) => value
    let binderOf : Lowered.Collected → Lowered.Binder := fun (.collected _ binder _) => binder
    if domain.count == some 0 then
      -- the types of the collected names: the body typed apart and forgotten
      let (types, apart) ← if collected.isEmpty then pure (#[], Typed.LoopBody.stepped #[]) else do
        let savedState ← getThe Compile.State
        let saved ← get
        -- a body that does not type apart leaves nothing, also when it does not for the index
        -- standing where a number is needed: there is no iteration to type on its own (TY16)
        let typed ← try
            recover (skipped := true) (waits := true) (fallback := pure none) do
              some <$> inSuite do
                discard <| bindItem domain none
                let statements ← elabStmtsR body
                let values ← collected.mapM fun entry => elabExpr (valueOf entry) none
                return (statements, values)
          catch failure =>
            match failure with
            | .staticIndex _ => pure none
            | other => throw other
        let discarded ← getThe Compile.State
        modifyThe Compile.State fun _ => savedState
        -- a statement refused while the body is typed apart leaves nothing
        modify fun state => { state with refused := saved.refused }
        for (binder, type) in carried.zip start do setLocalType binder type
        -- a type found may name an instance that the body made: it is made again here
        match typed with
        | some (statements, values) =>
          let types ← values.mapM fun value =>
            liftM (Instances.remakeType discarded span value.type : CompileM ClosedType)
          pure (types, Typed.LoopBody.empty statements values)
        | none => pure (collected.map fun _ => ClosedType.unit, Typed.LoopBody.empty #[] #[])
      let (index, item) ← inSuite (bindItem domain none)
      let binders ← (collected.zip types).mapM fun (entry, type) =>
        bindLocal (binderOf entry) (.seq type (some 0))
      -- nothing of the loop exists at the instance: it carries nothing
      return #[.«for» span (.loop index (domain.typed item) binders apart) {}]
    -- one typing for every iteration: the loop is uniform when every `mut` name keeps its type
    let uniform ← try
        let result ← inSuite do
          let (index, item) ← bindItem domain none
          let statements ← elabStmtsR body
          let values ← collected.mapM fun entry => elabExpr (valueOf entry) none
          let ends ← typesOf carried
          let mut stepped := false
          let mut widening := #[]
          for position in [0:carried.size] do
            let binder := carried[position]!
            unless typeEq ends[position]! start[position]! do
              match domain.count with
              | some _ => stepped := true
              | none =>
                let message :=
                  s!"`{← nameOf binder}` is a `{← renderTypeE start[position]!}` at the start of an iteration and a `{← renderTypeE ends[position]!}` at its end; a loop with a run-time count carries state of one type"
                match join ends[position]! start[position]! with
                | some joined =>
                  unless typeEq joined start[position]! do refuseHere "TY10" span message
                  let use : Typed.Expr := .local { span, type := ends[position]! } binder
                  let value ← convertTo use start[position]! span (.text (← nameOf binder))
                  widening := widening.push
                    (Typed.Stmt.update (Typed.Mark.derived span .widening) binder value {})
                | none => refuseHere "TY10" span message
          if stepped then return none
          -- a collected value is the value at the end of the body, before a `mut` name it reads
          -- is widened: it is bound there, and the widening updates come after it (TY16)
          if widening.isEmpty || values.isEmpty then
            return some (index, item, statements ++ widening, values)
          let mut taken := #[]
          let mut uses := #[]
          for value in values do
            let (binder, use) ← operandBinder value
            taken := taken.push (Typed.Stmt.bind value.span binder value {})
            uses := uses.push use
          return some (index, item, statements ++ taken ++ widening, uses)
        for (binder, type) in carried.zip start do setLocalType binder type
        pure result
      catch failure =>
        match failure, domain.count with
        | .staticIndex name, some _ =>
          if some name == indexName domain then pure none else throw failure
        | _, _ => throw failure
    match uniform with
    | some (index, item, statements, values) =>
      let binders ← (collected.zip values).mapM fun (entry, value) =>
        bindLocal (binderOf entry) (.seq value.type domain.count)
      return #[.«for» span (.loop index (domain.typed item) binders (.uniform statements values))
        (carriedIn carried start statements)]
    | none =>
      let some n := domain.count | throw .abandoned
      checkStepped n span
      -- the iterations in sequence, the index a static natural in each (TY10)
      let mut iterations := #[]
      let mut gathered : Array (Array ClosedType) := collected.map fun _ => #[]
      let mut binders : Option (Typed.Binder × Option Typed.Binder) := none
      for k in [0:n] do
        let (index, item, statements, values) ← inSuiteKeeping do
          let (index, item) ← bindItem domain (some k)
          let statements ← elabStmtsR body
          let values ← collected.mapM fun entry => elabExpr (valueOf entry) none
          return (index, item, statements, values)
        binders := some (index, item)
        iterations := iterations.push (Typed.Iteration.iteration k statements values)
        gathered := (gathered.zip values).map fun (types, value) => types.push value.type
      let some (index, item) := binders | throw .abandoned
      -- each collected name: the collection of its values when they have one type, their tuple
      -- otherwise (TY16)
      let mut collectedBinders := #[]
      for (entry, types) in collected.zip gathered do
        let element := types[0]!
        let type : ClosedType := if types.all (typeEq · element) then .seq element (some n)
          else .tuple types (types.map fun _ => none)
        collectedBinders := collectedBinders.push (← bindLocal (binderOf entry) type)
      let suites := iterations.foldl (init := #[]) fun all (.iteration _ statements _) => all ++ statements
      return #[.«for» span (.loop index (domain.typed item) collectedBinders (.stepped iterations))
        (carriedIn carried (← typesOf carried) suites)]

  /-- `match` on a value of a variant (TY13): a case per alternative, or a case for every other
  one. The matched value is evaluated once, before the cases. -/
  partial def elabMatch (span : Span) (scrutinee : Lowered.Expr) (cases : Array Lowered.Case) :
      ElabM (Array Typed.Stmt) := do
    let typed ← elabExpr scrutinee none
    let .«variant» inst := typed.type
      | refuseHere "TY13" span
          s!"`match` takes a value of a variant; `{← textOf scrutinee.span}` is a `{← renderTypeE typed.type}`"
    let alternatives ← variantAlternatives inst
    let typeText ← renderTypeE typed.type
    -- the case of each alternative, and the case of every other one
    let mut chosen : Array (Option Nat) := alternatives.map fun _ => none
    let mut otherwise : Option Nat := none
    for index in [0:cases.size] do
      let .«case» caseSpan pattern _ := cases[index]!
      match ← caseAlternative inst alternatives pattern caseSpan with
      | some alternative =>
        if chosen[alternative]!.isSome then
          refuseHere "TY13" caseSpan s!"`match` on `{typeText}` has two cases for `{alternatives[alternative]!.1}`"
        chosen := chosen.set! alternative (some index)
      | none =>
        -- a `match` has at most one case that covers every other value (TY13)
        if otherwise.isSome then
          refuseHere "TY13" caseSpan s!"`match` on `{typeText}` has a second case that covers every other value"
        otherwise := some index
    for index in [0:alternatives.size] do
      if chosen[index]!.isNone && otherwise.isNone then
        refuseHere "TY13" span s!"`match` on `{typeText}` does not cover `{alternatives[index]!.1}`"
    let carried ← carriedBy (cases.foldl (init := #[]) fun all (.«case» _ _ body) => all ++ body)
    let (binder, value) ← operandBinder typed
    -- the cases taken, each with the alternatives it covers, in the order of the alternatives
    let caseOf (index : Nat) : Option Nat := chosen[index]!.orElse fun _ => otherwise
    let mut taken : Array Nat := #[]
    for index in [0:alternatives.size] do
      let some case := caseOf index | throw .abandoned
      unless taken.contains case do taken := taken.push case
    let mut arms := #[]
    let mut covers := #[]
    for case in taken do
      let .«case» caseSpan pattern body := cases[case]!
      let covered := (List.range alternatives.size).toArray.filter (caseOf · == some case)
      covers := covers.push covered
      let payloadTypes := match covered[0]? with
        | some index => alternatives[index]!.2
        | none => #[]
      let prepare : ElabM (Array Typed.Binder × Array Typed.Stmt) := do
        match pattern with
        | .alternative _ _ patterns =>
          if patterns.isEmpty then
            -- a case that binds no payload drops it: a linear value is not dropped (LN1)
            if !(← getContext).specification &&
                payloadTypes.any (isLinear (← getThe Compile.State) ·) then
              refuseHere "LN1" caseSpan
                "the case binds nothing of a payload that has a linear value; a linear value is used exactly once"
            return (#[], #[])
          unless patterns.size == payloadTypes.size do
            refuseHere "TY13" caseSpan
              s!"the alternative has {payloadTypes.size} values; the case binds {patterns.size}"
          let mut binders := #[]
          let mut levels := #[]
          for index in [0:patterns.size] do
            let (payload, nested) ← payloadBinder patterns[index]! payloadTypes[index]! caseSpan
            binders := binders.push payload
            levels := levels ++ nested
          return (binders, levels)
        | .any _ (some name) =>
          -- a case for every other alternative that names the value
          let named ← bindLocal name typed.type
          return (#[], #[.bind (Typed.Mark.derived caseSpan .pattern) named value {}])
        | _ =>
          -- `_` does not match a linear value (LN3)
          if !(← getContext).specification && isLinear (← getThe Compile.State) typed.type then
            refuseHere "LN3" caseSpan "`_` does not match a linear value: open it, return it or pass it on"
          return (#[], #[])
      arms := arms.push (prepare, body)
    let (bodies, joined) ← elabArms span carried arms
    let mut typedCases := #[]
    for index in [0:taken.size] do
      let .«case» caseSpan _ _ := cases[taken[index]!]!
      let (payload, body) := bodies[index]!
      typedCases := typedCases.push (.«case» caseSpan covers[index]! (payload.map some) body)
    let suites := bodies.foldl (init := #[]) fun all (_, body) => all ++ body
    return #[.«match» span typed (some binder) inst typedCases (carriedIn carried joined suites)]

  /-- Binds the value of a binding to its binder: a name, `_`, or the value that a pattern takes
  apart, bound to a binder that lowering made. -/
  partial def bindValue (span : Span) (binder : Lowered.Binder) (value : Typed.Expr)
      (declared : Bool := false) (placement : Typed.Placement := {})
      (derivation : Typed.Derivation := .written) : ElabM (Array Typed.Stmt) := do
    let mark : Typed.Mark := { span, derivation }
    match binder.origin with
    | .written | .patternValue =>
      let typed ← bindLocal binder value.type (declared := declared)
      return #[.bind mark typed value placement]
    | .discarded =>
      -- `_` does not match a linear value (LN3)
      if !(← getContext).specification && isLinear (← getThe Compile.State) value.type then
        refuseHere "LN3" binder.span "`_` does not match a linear value: open it, return it or pass it on"
      let typed ← bindLocal binder value.type
      return #[.bind mark typed value placement]
    | _ => unexpected "a binder made for another form"
end

end Zkc.Frontend.Elab
