module

public import Zkc.Frontend.Driver.Bodies

@[expose] public section

/-! A member's value and the validity of its concrete module are separate dependencies.
Check the latter after the consuming computation finishes. Validation may need further
signatures and bodies, whose instance numbers belong only to the private checking state. -/

namespace Zkc.Frontend.Typing

open Static Instances

private inductive Dependency where
  | owner (key : InstanceKey)
  | query (ref : QueryRef)
  | root (id : InstanceId)
  | input
  deriving Inhabited, BEq, Hashable

private abbrev Selection := Dependency × Syntax.Span

private structure OwnerCheck where
  children : Array Selection := #[]
  failure : Option Interrupt := none
  deriving Inhabited

private structure ModuleWork where
  /-- Every edge is retained, including later uses of an already scheduled dependency. -/
  parents : Std.HashMap Dependency (List Selection) := {}
  queries : Array QueryRef := #[]
  owners : Array (InstanceKey × Syntax.Span) := #[]
  failures : Array (Dependency × Interrupt) := #[]
  /-- Owners at the depth limit. A newly completed local body may still expose a shorter path. -/
  boundary : Array (InstanceKey × Syntax.Span) := #[]
  /-- Settled local checks and their edges in the private table, reusable on a subsequent walk. -/
  checks : Std.HashMap InstanceKey OwnerCheck := {}
  /-- Number of settled checks when an ordinary request first needed a shorter caller. -/
  deferredAt : Option Nat := none
  /-- Entries added to the log by each local check, before its caller chain is attached. -/
  diagnostics : Array (InstanceKey × Log.Cursor × Log.Cursor) := #[]

private def selections (reads : Array Compile.ModuleRead) : CompileM (Array Selection) :=
  reads.mapM fun
    | .query ref => pure (.query ref, default)
    | .owner key place none => pure (.owner key, place)
    | .owner key place (some (shared, signatures)) => do
      let discarded := { (← get) with env.results.signatures := signatures }
      let args ← key.arguments.mapM (remakeValue discarded shared place)
      pure (.owner {key with arguments := args}, place)

private def ModuleWork.discover (work : ModuleWork) (reads : Array Selection)
    (parent : Dependency) : ModuleWork := Id.run do
  let mut work := work
  for (node, place) in reads do
    let previous := work.parents[node]?
    work := {work with parents := work.parents.insert node ((parent, place) :: previous.getD [])}
    if previous.isNone then
      match node with
      | .query ref => work := {work with queries := work.queries.push ref}
      | .owner key => work := {work with owners := work.owners.push (key, place)}
      | _ => pure ()
  return work

/-- A false default precondition makes that law or member inapplicable. Every other
interrupt retains its ordinary source meaning. -/
private def whenApplicable (action : CompileM Unit) : CompileM Unit := do
  try action catch
    | .skipped => pure ()
    | other => throw other

private def checkMemberBody (inst : InstanceId) : CompileM Unit := do
  trace "module.member" fun _ => .ofPart (.instance inst)
  let state ← get
  let some entry := state.table.entryAt? inst | throw (.defect "missing required member")
  if let some (.waits why _) := state.table.content? inst then throw (.waiting why)
  observeApplication inst entry.requested.span
  typeBody inst entry.requested.span
  match (← getResults).body? inst with
  | some (.done _) | some (.protocol _) | some (.row _) => pure ()
  | some (.waiting why) => throw (.waiting why)
  | some (.exhausted e) => throw (.exhausted e)
  | some .failed => throw .abandoned
  | _ => throw (.defect "a required module member has no completed body")

private def completeModule (key : InstanceKey) (place : Syntax.Span) : CompileM Unit := do
  trace "module.owner" fun _ => .ofPart (.instantiation key.declaration key.arguments)
  let inst ← formInstance key.declaration key.arguments ⟨"", place⟩
  match (← get).table.content? inst with
  | some (.waits why _) => throw (.waiting why)
  | some (.«module» _ members) =>
    for (_, value) in members do
      if let .«module» child := value then observeModuleValue child place
    let frame : ChainFrame := ⟨.ofText (← describeInstance key.declaration key.arguments), place⟩
    withChainFrame frame do
      moduleLaws inst checkMemberBody whenApplicable
      typeModuleMembers inst checkMemberBody whenApplicable
  | _ => throw (.defect "a required source module has no completed member table")

private def readsOfRoot (s : Compile.State) (root : InstanceId) : Array Compile.ModuleRead :=
  #[.query ⟨.signature, root⟩, .query ⟨.body, root⟩] ++ s.rootSelectionReads.getD root #[]

/-- Choose one predecessor per node for display. Start at real roots, then cover any remaining
standalone reads. Following predecessors terminates even when validation edges form a cycle. -/
private def ModuleWork.diagnosticPaths (work : ModuleWork) (roots : Array InstanceId) :
    Std.HashMap Dependency Selection := Id.run do
  let mut children : Std.HashMap Dependency (List Selection) := {}
  for (node, parents) in work.parents do
    for (parent, place) in parents do
      children := children.alter parent fun old => some ((node, place) :: old.getD [])
  let mut paths := {}
  for seeds in [roots.map Dependency.root, #[.input]] do
    let mut queue := seeds
    let mut i := 0
    while i < queue.size do
      let parent := queue[i]!
      i := i + 1
      for (child, place) in children.getD parent [] do
        unless paths.contains child do
          paths := paths.insert child (parent, place)
          queue := queue.push child
  return paths

private def callerChain (paths : Std.HashMap Dependency Selection) (key : InstanceKey) :
    CompileM (Array ChainFrame) := do
  let state ← get
  let mut frames := #[]
  let mut node := Dependency.owner key
  while let some (parent, _) := paths[node]? do
    let frame ← match parent with
      | .root id =>
        -- The root's own body or signature query already supplied its frame.
        if let .query ref := node then
          if ref.instance == id then break
        pure (state.results.requested? ⟨.signature, id⟩)
      | .query ref => pure (state.results.requested? ref)
      | .owner owner => do
        let name ← describeInstance owner.declaration owner.arguments
        pure (some ⟨.ofText name, (paths[parent]?.map Prod.snd).getD default⟩)
      | .input => pure none
    if let some f := frame then frames := frames.push f
    node := parent
  return frames

/-- A closed term starts with its own allowance in a program validation pass. Never reuse
that interruption inside a running evaluation, under a different limit or for a selected clause. -/
private def reusableExhaustion (e : Exhaustion) (ctx : Compile.Context) (s : Compile.State) : Bool :=
  e.budget == .staticEvaluation && e.limit == ctx.options.budgets.staticEvaluation &&
    s.staticDepth == 0 && ctx.allClauseReads && ctx.checkingMembers.isEmpty

/-- Isolate the local log so that even a diagnostic deduplicated at an earlier owner can
identify the budget of this check. Preserve both occurrence counts when merging for display. -/
private def checkOwner (key : InstanceKey) (place : Syntax.Span) : CompileM OwnerCheck := do
  let previous ← modifyGet fun s => (s.log, {s with log := {}})
  let mut children := #[]
  let failure ← try
    let (_, more) ← captureModuleReads (completeModule key place)
    children ← selections more
    let log := (← get).log
    if log.hasErrors then throw .abandoned
    if log.hasIncomplete then
      if let some e := log.entries.findSome? (·.exhaustion) then throw (.exhausted e)
      throw (.defect "an incomplete module check has no budget diagnostic")
    pure none
  catch why => pure (some why)
  let depthFailure := failure.any fun
    | .exhausted e => e.budget == .instantiationDepth
    | _ => false
  modify fun s => {s with log := previous.append s.log.toDiagnosticLog depthFailure}
  return ⟨children, failure⟩

private inductive LocalDepth where
  /-- The ordinary fast path. Restart transactionally only on an actual request depth failure. -/
  | firstPass
  /-- Defer a depth-limited check without publishing the private queries it exhausted. -/
  | defer
  /-- Every remaining deferred check ran after the last progress. Publish its final outcome. -/
  | finish
  deriving BEq

private def OwnerCheck.depthFailure? (check : OwnerCheck) : Option Exhaustion := do
  let some (.exhausted e) := check.failure | none
  guard (e.budget == .instantiationDepth)
  return e

private def ModuleWork.useCheck (work : ModuleWork) (node : Dependency) (check : OwnerCheck) :
    ModuleWork := Id.run do
  let work := work.discover check.children node
  if let some why := check.failure then return {work with failures := work.failures.push (node, why)}
  return work

private def ModuleWork.visit (work : ModuleWork) (saved : Compile.State)
    (key : InstanceKey) (place : Syntax.Span) (depth : Nat) (mode : LocalDepth) :
    CompileM ModuleWork := do
  let node := Dependency.owner key
  if let some result := saved.checkedModules[key]? then
    match result with
    | .ok () => return work
    | .error (.exhausted e) =>
      if reusableExhaustion e (← read) saved then
        return {work with failures := work.failures.push (node, .exhausted e)}
    | .error why => return {work with failures := work.failures.push (node, why)}
  modify fun s => { s with moduleDeclarations := s.moduleDeclarations.insert key.declaration }
  if (← read).options.budgets.instantiationDepth ≤ saved.stack.size + depth then
    return {work with boundary := work.boundary.push (key, place)}
  if let some found := work.checks[key]? then return work.useCheck node found
  let first := (← get).log.cursor
  let checked ← if mode == .defer then do
    let (result, trial) := (checkOwner key place).run (← read) (← get)
    match result with
    | .error why => throw why
    | .ok check =>
      if check.depthFailure?.isNone then set trial
      pure check
  else checkOwner key place
  if let some e := checked.depthFailure? then
    match mode with
    | .firstPass => throw (.exhausted e)
    | .defer => return {work with deferredAt := work.deferredAt.orElse (fun _ => some work.checks.size)}
    | .finish => pure ()
  let mut work := work.useCheck node checked
  let last := (← get).log.cursor
  if first != last then work := {work with diagnostics := work.diagnostics.push (key, first, last)}
  if mode != .firstPass then work := {work with checks := work.checks.insert key checked}
  return work

/-- Close all query reads at the current depth before expanding its owners. Only an edge
out of an owner costs one level, so the first visit settles the minimum owner depth. -/
private def walkModules (saved : Compile.State) (seeds : ModuleWork) (mode : LocalDepth) :
    CompileM ModuleWork := do
  let mut work := seeds
  let mut depth := 0
  while !work.queries.isEmpty || !work.owners.isEmpty do
    let mut i := 0
    while i < work.queries.size do
      let ref := work.queries[i]!
      i := i + 1
      if let some more := (← get).readsOfQuery[ref]? then
        work := work.discover (← selections more) (.query ref)
    let owners := work.owners
    work := {work with queries := #[], owners := #[]}
    for (key, place) in owners do
      work ← work.visit saved key place depth mode
    depth := depth + 1
  return work

private def settleModules (saved : Compile.State) (reads : Array Compile.ModuleRead)
    (roots : Array InstanceId) :
    CompileM (ModuleWork × Std.HashMap Dependency Interrupt) := do
  let mut seeds := ({} : ModuleWork)
  for root in roots do
    seeds := seeds.discover (← selections (readsOfRoot saved root)) (.root root)
  seeds := seeds.discover (← selections reads) .input
  let (result, state) := (walkModules saved seeds .firstPass).run (← read) (← get)
  let mut work ← match result with
    | .ok work => set state; pure work
    | .error (.exhausted {budget := .instantiationDepth, ..}) => do
      -- A long ordinary call can exhaust a body that a sibling can compute directly. Keep
      -- completed checks; discard failed trials before the next caller sees their query state.
      let mut mode := LocalDepth.defer
      let mut pass ← walkModules saved seeds mode
      while let some atCount := pass.deferredAt do
        if pass.checks.size == atCount then mode := .finish
        seeds := {seeds with checks := pass.checks, diagnostics := pass.diagnostics}
        pass ← walkModules saved seeds mode
      pure pass
    | .error why => set state; throw why
  let paths := if work.boundary.isEmpty && work.diagnostics.isEmpty then {}
    else work.diagnosticPaths roots
  for (key, originalPlace) in work.boundary do
    let place := (paths[Dependency.owner key]?.map Prod.snd).getD originalPlace
    let first := (← get).log.cursor
    let name ← describeInstance key.declaration key.arguments
    let retry := (← get).log.moduleDepthRetry
    let e ← logExhaustion .instantiationDepth ⟨.ofText name, place⟩
    if retry.any (·.collecting) then modify fun s => {s with log.moduleDepthRetry := retry}
    work := {work with failures := work.failures.push (.owner key, .exhausted e)}
    let last := (← get).log.cursor
    if first != last then work := {work with diagnostics := work.diagnostics.push (key, first, last)}
  -- Insert the selection path between each diagnostic's local and ambient frames. These
  -- historical frames are never active requests and do not spend instantiation depth.
  let ambient := saved.chain.size
  for (key, first, last) in work.diagnostics do
    let callers ← callerChain paths key
    let attach (log : DiagnosticLog) (start stop : Nat) : DiagnosticLog := Id.run do
      let mut entries := log.entries
      for i in [start:stop] do
        entries := entries.modify i fun d =>
          let cut := d.chain.size - ambient
          {d with chain := d.chain.extract 0 cut ++ callers ++ d.chain.extract cut d.chain.size}
      return {log with entries}
    modify fun s => {s with log := {s.log with
      toDiagnosticLog := attach s.log.toDiagnosticLog first.visible last.visible
      moduleDepthRetry := s.log.moduleDepthRetry.map fun retry =>
        {retry with retained := attach retry.retained first.retained last.retained}}}
  let mut failed : Std.HashMap Dependency Interrupt := {}
  for (start, why) in work.failures do
    let mut pending := [start]
    while let head :: tail := pending do
      pending := tail
      unless failed.contains head do
        failed := failed.insert head why
        for (parent, _) in work.parents.getD head [] do pending := parent :: pending
  return (work, failed)

private structure ModuleVerdicts where
  first : Option Interrupt := none
  byRoot : Std.HashMap InstanceId Interrupt := {}

/-- Publish diagnostics and settled checks whose arguments belong to the calling environment.
Validation-only signatures, body instances and default roots stay in the checking table. -/
private def validateReads (reads : Array Compile.ModuleRead) (roots : Array InstanceId) :
    CompileM ModuleVerdicts := do
  if reads.isEmpty then return {}
  let saved ← get
  let (result, checked) := (settleModules saved reads roots).run (← read) saved
  let freeze ← restoreObservations saved checked (reports := false)
  publishValidationObligations saved checked
  let stable : Interrupt → Interrupt
    | .exhausted e => .exhausted (freeze e)
    | other => other
  let reached := checked.results.reachedDeclarations checked.detachedDeclarations
    saved.table.requestedIds.size
  modify fun s => {s with moduleDeclarations := checked.moduleDeclarations, detachedDeclarations := reached}
  let (work, failed) ← match result with
    | .ok value => pure value
    | .error why => throw (stable why)
  let mut memo := saved.checkedModules
  let ctx ← read
  for (node, _) in work.parents do
    let .owner key := node | continue
    if key.arguments.all (sharedValue saved.table saved.table.allocatedCount) then
      match failed[node]? with
      | none => memo := memo.insert key (.ok ())
      | some .abandoned => memo := memo.insert key (.error .abandoned)
      | some (.exhausted e) =>
        if reusableExhaustion e ctx saved then memo := memo.insert key (.error (.exhausted (freeze e)))
        else memo := memo.erase key
      | _ => memo := memo.erase key
  modify fun s => {s with checkedModules := memo}
  let mut rootFailures := {}
  for root in roots do
    if let some why := failed[Dependency.root root]? then
      rootFailures := rootFailures.insert root (stable why)
  return ⟨work.failures[0]?.map (fun (_, why) => stable why), rootFailures⟩

/-- Check the concrete modules that contributed to this result. -/
@[no_expose] def checkModuleReads (reads : Array Compile.ModuleRead) : CompileM Unit := do
  if let some why := (← validateReads reads #[]).first then throw why

private def moduleLack : Interrupt → Lack
  | .waiting reason => .waiting reason
  | .exhausted e => .exhausted e
  | .abandoned => .refused "a required module of this root was refused"
  | .defect reason => .defect reason
  | _ => .defect "a required module check did not finish"

/-- Attribute settled failures to all consuming roots. An interruption before the graph
is available still needs independent checks to identify the affected roots. -/
private def validateProgramModules : CompileM Unit := do
  let s ← get
  let outcome : Except Interrupt ModuleVerdicts ←
    try pure (.ok (← validateReads s.moduleReads s.roots)) catch why => pure (.error why)
  let globalFailure := match outcome with
    | .ok verdicts => verdicts.first
    | .error why => some why
  let mut lacks := {}
  if let some first := globalFailure then
    for root in s.roots do
      let why ← match outcome with
        | .ok verdicts =>
          pure verdicts.byRoot[root]?
        | .error _ => retry root s
      if let some why := why then lacks := lacks.insert root (moduleLack why)
    endItem (throw first)
  modify fun state => { state with rootModuleFailures := lacks }
where
  retry (root : InstanceId) (s : Compile.State) : CompileM (Option Interrupt) := do
    try
      checkModuleReads (readsOfRoot s root)
      return none
    catch why => return some why

/-- The two program checks share all settled observations. Only depth cutoffs from this
validation can be discharged by a shorter path from a new root. Keep their occurrences
visible until the retry publishes its result. -/
@[no_expose] def checkProgramModules (beforeDefaults : Bool := false) : CompileM Unit := do
  let s ← get
  if !beforeDefaults && s.log.moduleDepthRetry.isNone then return ← validateProgramModules
  let ctx ← read
  let depth := ctx.options.budgets.instantiationDepth
  let trial : Log := {moduleDepthRetry := some ⟨{}, s.roots.size, depth, true⟩}
  let (outcome, after) := validateProgramModules.run ctx {s with log := trial}
  let observed := after.log.toDiagnosticLog
  if let .error why := outcome then
    set {after with log := s.log.append observed}
    throw why
  let stable := (after.log.moduleDepthRetry.map (·.retained)).getD observed
  let cutoffs := observed.incomplete - stable.incomplete
  let mut base := {s.log with moduleDepthRetry := none}
  if let some retry := s.log.moduleDepthRetry then
    -- Rechecking the same graph at the same allowance still counts repeated cutoffs.
    if beforeDefaults || retry.roots != after.roots.size || retry.depth != depth ||
        cutoffs != s.log.incomplete - retry.retained.incomplete then
      base := {base with
        toDiagnosticLog := retry.retained
        moduleDepthRevision := s.log.moduleDepthRevision + 1}
  let mut log := base.append observed
  if beforeDefaults && cutoffs != 0 then
    log := {log with moduleDepthRetry := some ⟨base.toDiagnosticLog.append stable, after.roots.size, depth, false⟩}
  set {after with log}

end Zkc.Frontend.Typing
