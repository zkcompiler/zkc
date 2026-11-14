module

public import Zkc.Frontend.Passes.Stops
public import Zkc.Frontend.Typed.Checked
public import Zkc.Frontend.Static.Basic

@[expose] public section

set_option autoImplicit false

/-!
# The placement pass

Who holds each name of a protocol body, who computes each statement, who takes part in each
choice and loop, and who sends each payload (HO1, HO2, GU2, EV5, CT1, CT2, RM2). The pass reads
the numbered tree and what the source writes of roles, and fills the tables of `Typed.Roles`.
It changes no node. It reports every refusal it finds, in the order of the body, and goes on.

**Holders.** `hold(e)` is the roster cut by the holders of every local name that `e` reads and
does not itself bind. A static value adds nothing.

**Computing roles.** A binding is computed by `hold(e)`, or by the roles written after `@`,
which must be within it; its name is held by those roles. An update is computed by the holders
of its name; a guard by the roles it names; a collected value and a result by their holders.
Inside a choice or a loop only the participants compute, so the roles that compute a statement
there are the participants among them.

**Acting roles.** `act` of a binding is its computing roles, and none when the binding is
closed and cannot stop. An expression is closed when it reads no name of a value: a static
name and the index of a loop over a static range are none (HO1). A name that every role holds is
still a name of a value: an expression over it is computed, by each holder. A statement that elaboration made for a level
of a pattern acts for nobody: the binding it takes apart acted. The participants of a choice
or a loop are the union of `act` over its suites, nested control included; they are computed
before the suites are placed.
-/

namespace Zkc.Frontend.Passes

open Syntax (Span)
open Typed

structure PlacementContext where
  roster : Array String
  /-- Whether a function instance can stop. -/
  calleeStops : InstanceId → Bool
  /-- The closed signature of a protocol instance that the body applies. -/
  signatureOf : InstanceId → Option ProtocolSignature

structure PlacementState where
  roles : Roles := {}
  /-- The name of each binder, for messages. -/
  names : Std.HashMap LocalId String := {}
  /-- The indices of the loops over static ranges: such a name restricts nothing (HO1). -/
  staticIndices : Std.HashSet LocalId := {}

abbrev PlaceM := ReaderT PlacementContext (StateT PlacementState CompileM)

namespace Placement

def everyone : PlaceM RoleSet := return RoleSet.all (← read).roster.size

def roleName (role : Nat) : PlaceM String := return (((← read).roster)[role]?).getD s!"role{role}"

/-- Roles as a message writes them: `P`, or `P, V`. -/
def roleNames (roles : RoleSet) : PlaceM String :=
  return ", ".intercalate (roles.names (← read).roster).toList

def refuse (rule : String) (span : Span) (message : String) : PlaceM Unit :=
  liftM (logError rule span (.ofText message) : CompileM Unit)

def textOf (span : Span) : PlaceM String := liftM (Static.textAt span : CompileM String)

def holdersOf (binder : LocalId) : PlaceM RoleSet := do
  match (← get).roles.holders[binder]? with
  | some holders => return holders
  | none => everyone

/-- Gives a binder its holders. -/
def hold (binder : Binder) (holders : RoleSet) : PlaceM Unit :=
  modify fun state => { state with
    roles := { state.roles with holders := state.roles.holders.insert binder.id holders }
    names := state.names.insert binder.id binder.name }

mutual
  /-- The local names that an expression reads and does not bind, each once, in the order
  read. -/
  partial def freeLocals (bound : Std.HashSet LocalId) (found : Array LocalId) :
      Expr → Std.HashSet LocalId × Array LocalId
    | .literal .. | .staticValue .. => (bound, found)
    | .local _ binder =>
      if bound.contains binder || found.contains binder then (bound, found) else (bound, found.push binder)
    | .apply _ _ arguments => arguments.foldl (init := (bound, found)) fun (bound, found) argument =>
        freeLocals bound found argument
    | .construct _ _ parts => parts.foldl (init := (bound, found)) fun (bound, found) part =>
        freeLocals bound found part
    | .project _ target _ _ => freeLocals bound found target
    | .convert _ _ value _ => freeLocals bound found value
    | .conditional _ _ condition onTrue onFalse =>
      let (bound, found) := freeLocals bound found condition
      let (bound, found) := freeLocals bound found onTrue
      freeLocals bound found onFalse
    | .block _ statements result =>
      let (inner, found) := freeLocalsOf bound found statements
      let (_, found) := freeLocals inner found result
      (bound, found)
    | .error _ evaluated => evaluated.foldl (init := (bound, found)) fun (bound, found) part =>
        freeLocals bound found part

  /-- The same over the statements of a block, whose binders are bound for what follows. -/
  partial def freeLocalsOf (bound : Std.HashSet LocalId) (found : Array LocalId)
      (statements : Array Stmt) : Std.HashSet LocalId × Array LocalId :=
    statements.foldl (init := (bound, found)) fun (bound, found) statement =>
      match statement with
      | .bind _ binder value _ =>
        let (bound, found) := freeLocals bound found value
        (bound.insert binder.id, found)
      | .unpack _ binders value _ =>
        let (bound, found) := freeLocals bound found value
        (binders.foldl (init := bound) fun bound binder =>
          match binder with
          | some binder => bound.insert binder.id
          | none => bound, found)
      | .update _ target value _ =>
        let (bound, found) := freeLocals bound found value
        if bound.contains target || found.contains target then (bound, found) else (bound, found.push target)
      | .guard _ condition _ _ => freeLocals bound found condition
      | .if _ condition onTrue onFalse _ =>
        let (bound, found) := freeLocals bound found condition
        let (_, found) := freeLocalsOf bound found onTrue
        let (_, found) := freeLocalsOf bound found onFalse
        (bound, found)
      | .match _ scrutinee binder _ cases _ =>
        let (bound, found) := freeLocals bound found scrutinee
        let inner := match binder with
          | some binder => bound.insert binder.id
          | none => bound
        let found := cases.foldl (init := found) fun found (.case _ _ payload body) =>
          let inner := payload.foldl (init := inner) fun inner binder =>
            match binder with
            | some binder => inner.insert binder.id
            | none => inner
          (freeLocalsOf inner found body).2
        (bound, found)
      | .for _ (.loop index domain collected body) _ =>
        let (bound, found) := match domain with
          | .range start stop _ =>
            let (bound, found) := freeLocals bound found start
            freeLocals bound found stop
          | .collection source _ _ => freeLocals bound found source
        let inner := bound.insert index.id
        let inner := match domain with
          | .collection _ item _ => inner.insert item.id
          | .range .. => inner
        let iteration (found : Array LocalId) (statements : Array Stmt) (values : Array Expr) :=
          let (inner, found) := freeLocalsOf inner found statements
          values.foldl (init := found) fun found value => (freeLocals inner found value).2
        let found := match body with
          | .uniform statements values => iteration found statements values
          | .empty .. => found
          | .stepped iterations => iterations.foldl (init := found) fun found
              (.iteration _ statements values) => iteration found statements values
        (collected.foldl (init := bound) fun bound binder => bound.insert binder.id, found)
      | .scope _ body => (bound, (freeLocalsOf bound found body).2)
      | .event .. | .error .. => (bound, found)
end

/-- The holders of an expression (HO1), with what restricted them: each name read and its
holders. -/
def holdOf (expr : Expr) : PlaceM (RoleSet × Array (String × RoleSet)) := do
  let state ← get
  let mut holders ← everyone
  let mut why := #[]
  for binder in (freeLocals {} #[] expr).2 do
    let some held := state.roles.holders[binder]? | continue
    holders := holders.inter held
    why := why.push ((state.names[binder]?).getD "?", held)
  return (holders, why)

/-- Whether an expression is closed (HO1): it reads no name of a value. A static name and the
index of a loop over a static range are none; a name that the expression itself binds is not
free. So a literal, and an operation over literals and static names, is closed. -/
def closed (expr : Expr) : PlaceM Bool := do
  let indices := (← get).staticIndices
  return (freeLocals {} #[] expr).2.all indices.contains

/-- Refuses an expression that the roles needed do not all hold. -/
def requireHeld (expr : Expr) (needed : RoleSet) (rule : String) (place : Span) : PlaceM Unit := do
  let (held, why) ← holdOf expr
  for role in needed.toArray do
    unless held.contains role do
      let roleText ← roleName role
      let text ← textOf expr.span
      match why.find? fun (_, holders) => !holders.contains role with
      | some (name, holders) =>
        if name == text then
          refuse rule place s!"{roleText} does not hold `{name}`, which is held by {← roleNames holders}"
        else
          refuse rule place s!"{roleText} does not hold `{text}`: `{name}` is held by {← roleNames holders}"
      | none => refuse rule place s!"{roleText} does not hold `{text}`"
      return

/-- The holders of an expression, refused when no role can form it (HO1). -/
def formers (expr : Expr) (place : Span) : PlaceM RoleSet := do
  let (held, why) ← holdOf expr
  if held.isEmpty then
    let parts ← why.mapM fun (name, holders) => do return s!"`{name}` is held by {← roleNames holders}"
    refuse "HO1" place s!"no role can form `{← textOf expr.span}`: {" and ".intercalate parts.toList}"
  return held

/-- Every participant of a choice or a loop holds what decides it (CT2). -/
def requireDecided (participants : RoleSet) (expr : Expr) (what kind : String) (span : Span) :
    PlaceM Unit := do
  let held ← formers expr expr.span
  for role in participants.toArray do
    unless held.contains role do
      refuse "CT2" span
        s!"{← roleName role} acts in this {kind} (line {span.startLine}) and does not hold its {what} `{← textOf expr.span}`, held by {← roleNames held}; send it first"
      return

def setComputing (node : NodeId) (roles : RoleSet) : PlaceM Unit :=
  modify fun state => { state with
    roles := { state.roles with computing := state.roles.computing.insert node roles } }

/-- The roles that an event names: the sender and the receivers, the owner and the receivers,
the role that samples, the mapped roles of an application. -/
def eventRoles (what : Event) : PlaceM RoleSet := do
  match what with
  | .send _ payload sender receivers =>
    let receiving := RoleSet.ofArray receivers
    match sender with
    | some role => return receiving.insert role
    | none =>
      let (held, _) ← holdOf payload
      match (held.toArray.filter (!receiving.contains ·))[0]? with
      | some role => return receiving.insert role
      | none => return receiving
  | .draw _ _ owner receivers => return (RoleSet.ofArray receivers).insert owner
  | .sample _ _ role | .attempt _ role => return RoleSet.single role
  | .apply _ _ _ _ roleMap _ => return RoleSet.ofArray roleMap

/-- The holders of a name bound by an event. -/
def bindEvent (what : Event) (roles : RoleSet) : PlaceM Unit := do
  match what with
  | .send binder .. | .draw binder .. | .sample binder .. | .attempt binder .. =>
    if let some binder := binder then hold binder roles
  | .apply results callee _ _ roleMap _ =>
    let signature := (← read).signatureOf callee
    for index in [0:results.size] do
      let some binder := results[index]! | continue
      let holders := match (signature.bind (·.results[index]?)).map (·.holders) with
        | some holders => RoleSet.ofArray (holders.toArray.map fun role => roleMap[role]?.getD role)
        | none => roles
      hold binder holders

mutual
  /-- Walks statements in order and returns the roles that act in them. With `record` it also
  fills the tables and reports refusals, the statements being computed by the roles of
  `active`; without it, it only gives the names their holders. -/
  partial def walk (record : Bool) (active : RoleSet) (statements : Array Stmt) :
      PlaceM RoleSet := do
    let mut acts := RoleSet.empty
    for statement in statements do acts := acts.union (← walkStmt record active statement)
    return acts

  partial def walkStmt (record : Bool) (active : RoleSet) : Stmt → PlaceM RoleSet
    | .bind mark binder value placement => do
      let held ← if record then formers value mark.span else do pure (← holdOf value).1
      let computing ← match placement.written with
        | some written =>
          if record && !written.subset held then
            refuse "HO2" mark.span
              s!"`@{← roleNames written}` is not within the holders of `{← textOf value.span}`, which are {← roleNames held}"
          pure written
        | none => pure held
      hold binder computing
      if record then setComputing mark.id (computing.inter active)
      if mark.derivation != .written then return RoleSet.empty
      if (← closed value) && !value.canStop (← read).calleeStops then return RoleSet.empty
      return computing
    | .unpack mark binders value _ => do
      -- a level of a pattern: the roles that hold the value it takes apart
      let (held, _) ← holdOf value
      for binder in binders do
        if let some binder := binder then hold binder held
      if record then setComputing mark.id (held.inter active)
      return RoleSet.empty
    | .update mark target value _ => do
      let holders ← holdersOf target
      if record then
        requireHeld value holders "HO1" mark.span
        setComputing mark.id holders
      return holders
    | .guard mark condition _ placement => do
      let roles := placement.written.getD RoleSet.empty
      if record then
        requireHeld condition roles "GU2" mark.span
        setComputing mark.id roles
      return roles
    | .event mark _ what => do
      let roles ← eventRoles what
      if record then placeEvent mark what
      bindEvent what roles
      return roles
    | .if mark condition onTrue onFalse _ => do
      let participants := (← walk false active onTrue).union (← walk false active onFalse)
      if record then
        -- a suite with a refused statement does not say who acts in it: nothing is concluded
        -- from its participants
        unless onTrue.any Stmt.hasError || onFalse.any Stmt.hasError do
          if participants.isEmpty then refuse "CT1" mark.span "no role acts in this choice"
        requireDecided participants condition "condition" "branch" mark.span
        modify fun state => { state with roles := { state.roles with
          participants := state.roles.participants.insert mark.id participants } }
        discard <| walk true participants onTrue
        discard <| walk true participants onFalse
      return participants
    | .match mark scrutinee binder _ cases _ => do
      let bindCase (participants : RoleSet) (payload : Array (Option Binder)) : PlaceM Unit := do
        if let some binder := binder then hold binder participants
        for binder in payload do
          if let some binder := binder then hold binder participants
      -- while the participants are computed, the names of a case are held by the roles that
      -- hold the matched value: every participant holds it (CT2), and a role that does not
      -- cannot compute from its payload
      let matched := (← holdOf scrutinee).1
      let mut participants := RoleSet.empty
      for (.case _ _ payload body) in cases do
        bindCase matched payload
        participants := participants.union (← walk false active body)
      if record then
        unless cases.any fun (.case _ _ _ body) => body.any Stmt.hasError do
          if participants.isEmpty then refuse "CT1" mark.span "no role acts in this choice"
        requireDecided participants scrutinee "matched value" "branch" mark.span
        modify fun state => { state with roles := { state.roles with
          participants := state.roles.participants.insert mark.id participants } }
        setComputing scrutinee.info.id participants
        for (.case _ _ payload body) in cases do
          bindCase participants payload
          discard <| walk true participants body
      return participants
    | .for mark (.loop index domain collected body) _ => do
      -- a loop of no iteration has no participant and its body is nothing at the instance
      -- (CT1): its body typed apart gives each collected name the holders of its value (HO2).
      -- Its collection is evaluated once as in every loop (TY10): where that can stop, the
      -- roles that can form it evaluate it, and act
      let evaluating : PlaceM RoleSet := do
        match domain with
        | .collection source _ _ =>
          if source.canStop (← read).calleeStops then
            let roles := (← formers source source.span).inter active
            if record then setComputing source.info.id roles
            return roles
          return RoleSet.empty
        | .range .. => return RoleSet.empty
      if let .stepped #[] := body then
        for binder in collected do hold binder (← everyone)
        return ← evaluating
      if let .empty statements values := body then
        let itemHolders ← match domain with
          | .range start stop _ => do pure ((← holdOf start).1.inter (← holdOf stop).1)
          | .collection source _ _ => do pure (← holdOf source).1
        hold index itemHolders
        if let .collection _ item _ := domain then hold item itemHolders
        -- as at an instance with iterations, a collected name is held by the holders of its
        -- value among the roles that would take part
        let mut participants ← walk false active statements
        for value in values do
          unless (← closed value) && !value.canStop (← read).calleeStops do
            participants := participants.union (← holdOf value).1
        for position in [0:collected.size] do
          let holders ← match values[position]? with
            | some value => do pure ((← holdOf value).1.inter participants)
            | none => everyone
          hold collected[position]! holders
        return ← evaluating
      -- the item is held by the roles that hold the bounds, or the collection (CT3)
      let itemHolders ← match domain with
        | .range start stop _ => do pure ((← holdOf start).1.inter (← holdOf stop).1)
        | .collection source _ _ => do pure (← holdOf source).1
      let bindItem : PlaceM Unit := do
        hold index itemHolders
        match domain with
        | .collection _ item _ => hold item itemHolders
        | .range _ _ (some _) =>
          modify fun state => { state with staticIndices := state.staticIndices.insert index.id }
        | .range _ _ none => pure ()
      let iterations : Array (Array Stmt × Array Expr) := match body with
        | .uniform statements values => #[(statements, values)]
        | .empty .. => #[]
        | .stepped iterations => iterations.map fun (.iteration _ statements values) => (statements, values)
      bindItem
      let mut participants := RoleSet.empty
      for (statements, values) in iterations do
        participants := participants.union (← walk false active statements)
        for value in values do
          unless (← closed value) && !value.canStop (← read).calleeStops do
            participants := participants.union (← holdOf value).1
      if record then
        unless iterations.any fun (statements, _) => statements.any Stmt.hasError do
          if participants.isEmpty then refuse "CT1" mark.span "no role acts in this loop"
        match domain with
        | .range start stop _ =>
          requireDecided participants start "bound" "loop" mark.span
          requireDecided participants stop "bound" "loop" mark.span
        | .collection source _ size =>
          requireDecided participants source "collection" "loop" mark.span
          -- a loop of a protocol body ranges over a range or a sized collection (CT5)
          if size.isNone then
            refuse "CT5" mark.span
              s!"a loop of a protocol body ranges over a range or a sized collection; `{← textOf source.span}` is a `{← liftM (Static.renderTypeM source.type : CompileM String)}`"
        modify fun state => { state with roles := { state.roles with
          participants := state.roles.participants.insert mark.id participants } }
        for (statements, values) in iterations do
          discard <| walk true participants statements
          for value in values do
            setComputing value.info.id ((← formers value value.span).inter participants)
      -- a collected name is held by the holders of its expression among the participants
      let mut collectedHolders : Array RoleSet := collected.map fun _ => participants
      for (_, values) in iterations do
        for position in [0:values.size] do
          let held := (← holdOf values[position]!).1.inter participants
          collectedHolders := collectedHolders.modify position (·.inter held)
      for (binder, holders) in collected.zip collectedHolders do hold binder holders
      return participants
    | .scope _ body => walk record active body
    | .error _ binders => do
      for binder in binders do hold binder (← everyone)
      return RoleSet.empty

  /-- An event, placed: the payload of a send held by its sender (EV5), the arguments of an
  application by the mapped holders of their ports (HO1, RM2). -/
  partial def placeEvent (mark : Mark) : Event → PlaceM Unit
    | .send _ payload sender receivers => do
      let receiving := RoleSet.ofArray receivers
      let held ← formers payload mark.span
      let found ← match sender with
        | some role => do
          requireHeld payload (RoleSet.single role) "EV5" mark.span
          pure (some role)
        | none =>
          match (held.toArray.filter (!receiving.contains ·)).toList with
          | [only] => pure (some only)
          | [] =>
            unless held.isEmpty do
              refuse "EV5" mark.span s!"no role other than the receivers holds `{← textOf payload.span}`"
            pure none
          | first :: rest => do
            let candidates := RoleSet.ofArray (first :: rest).toArray
            refuse "EV5" mark.span
              s!"`{← textOf payload.span}` is held by {← roleNames candidates}: write `send … from {← roleName first} to {← roleNames receiving}`"
            pure (some first)
      -- a receiver is named once, and the sender is none of them (EV5)
      for index in [0:receivers.size] do
        if (receivers.extract 0 index).contains receivers[index]! then
          refuse "EV5" mark.span s!"{← roleName receivers[index]!} is named twice among the receivers of this send"
      if let some role := found then
        if sender.isSome && receivers.contains role then
          refuse "EV5" mark.span s!"{← roleName role} sends to itself: the sender of a send is none of its receivers"
        modify fun state => { state with roles := { state.roles with
          senders := state.roles.senders.insert mark.id role } }
        setComputing payload.info.id (RoleSet.single role)
    | .apply _ callee arguments _ roleMap _ => do
      let some signature := (← read).signatureOf callee | return
      let ports := signature.ports.filter (!·.specification)
      for (port, argument) in ports.zip arguments do
        let mapped := RoleSet.ofArray (port.holders.toArray.map fun role => roleMap[role]?.getD role)
        requireHeld argument mapped "HO1" argument.span
        setComputing argument.info.id mapped
    | .draw _ _ _ receivers => do
      -- a receiver is named once (EV6)
      for index in [0:receivers.size] do
        if (receivers.extract 0 index).contains receivers[index]! then
          refuse "EV6" mark.span s!"{← roleName receivers[index]!} is named twice among the receivers of this draw"
    | .sample .. | .attempt .. => pure ()
end

/-- The roles of a protocol body: its ports held as the head says, its statements placed, and
each result computed by the holders that the head gives it. -/
def body (found : ProtocolBody) : PlaceM Unit := do
  for port in found.ports do
    unless port.specification do hold port.binder port.holders
  discard <| walk true (← everyone) found.statements
  for result in found.results do
    requireHeld result.value result.holders "HO1" result.value.span
    setComputing result.value.info.id result.holders

end Placement

/-- The roles of a protocol body. Its refusals are logged; the tables are returned whatever
was refused. -/
def placeRoles (context : PlacementContext) (body : ProtocolBody) : CompileM Roles := do
  let ((), state) ← ((Placement.body body).run context).run {}
  return state.roles

end Zkc.Frontend.Passes
