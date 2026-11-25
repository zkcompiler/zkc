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
  deriving Inhabited, BEq, Hashable

private structure ModuleWork where
  /-- An entry exists for each scheduled node, including the initial reads. -/
  parents : Std.HashMap Dependency (List Dependency) := {}
  pending : Array (Dependency × Syntax.Span × Nat) := #[]
  failures : Array (Dependency × Interrupt) := #[]

private def ModuleWork.discover (work : ModuleWork) (reads : Array Compile.ModuleRead)
    (parent : Option Dependency) (at_ : Syntax.Span) (depth : Nat) : CompileM ModuleWork := do
  let mut work := work
  for item in reads do
    let (node, place) ← match item with
      | .query ref => pure (Dependency.query ref, at_)
      | .owner key place none => pure (.owner key, place)
      | .owner key place (some (shared, signatures)) => do
        let discarded := { (← get) with env.results.signatures := signatures }
        let args ← key.arguments.mapM (remakeValue discarded shared place)
        pure (.owner {key with arguments := args}, place)
    match work.parents[node]? with
    | some parents =>
      if let some from_ := parent then
        work := { work with parents := work.parents.insert node (from_ :: parents) }
    | none =>
      work := { work with parents := work.parents.insert node parent.toList,
                          pending := work.pending.push (node, place, depth) }
  return work

/-- A false default precondition makes that law or member inapplicable. Every other
interrupt retains its ordinary source meaning. -/
private def whenApplicable (action : CompileM Unit) : CompileM Unit := do
  try action catch
    | .skipped => pure ()
    | other => throw other

private def checkMemberBody (inst : InstanceId) : CompileM Unit := do
  let state ← get
  let some entry := state.table.entryAt? inst | throw (.defect "missing required member")
  if let some (.waits why _) := state.table.content? inst then throw (.waiting why)
  typeBody inst entry.requested.span
  match (← getResults).body? inst with
  | some (.done _) | some (.protocol _) | some (.row _) => pure ()
  | some (.waiting why) => throw (.waiting why)
  | some (.exhausted e) => throw (.exhausted e)
  | some .failed => throw .abandoned
  | _ => throw (.defect "a required module member has no completed body")

private def completeModule (key : InstanceKey) (place : Syntax.Span) : CompileM Unit := do
  let inst ← formInstance key.declaration key.arguments ⟨"", place⟩
  match (← get).table.content? inst with
  | some (.waits why _) => throw (.waiting why)
  | some (.«module» ..) =>
    let frame : ChainFrame := ⟨.ofText (← describeInstance key.declaration key.arguments), place⟩
    withChainFrame frame do
      moduleLaws inst checkMemberBody whenApplicable
      typeModuleMembers inst checkMemberBody whenApplicable
  | _ => throw (.defect "a required source module has no completed member table")

private def readsOfRoot (s : Compile.State) (root : InstanceId) : Array Compile.ModuleRead :=
  #[.query ⟨.signature, root⟩, .query ⟨.body, root⟩] ++ s.rootSelectionReads.getD root #[]

/-- Check each reachable owner once. Value recursion stays in the ordinary query machinery.
A cycle of validation edges settles when all its local checks have finished. A failure
propagates to every parent, including parents already visited from another root. -/
private def settleModules (saved : Compile.State) (reads : Array Compile.ModuleRead)
    (roots : Array InstanceId) :
    CompileM (ModuleWork × Std.HashMap Dependency Interrupt) := do
  let mut work ← ({} : ModuleWork).discover reads none default 0
  for root in roots do
    work ← work.discover (readsOfRoot saved root) (some (.root root)) default 0
  let mut i := 0
  while i < work.pending.size do
    let (node, place, depth) := work.pending[i]!
    i := i + 1
    match node with
    | .root _ => pure ()
    | .query ref =>
      if let some nested := (← get).readsOfQuery[ref]? then
        work ← work.discover nested (some node) place depth
    | .owner key =>
      if let some result := saved.checkedModules[key]? then
        if let .error why := result then work := {work with failures := work.failures.push (node, why)}
        continue
      modify fun s => { s with reachedModules := s.reachedModules.insert key.declaration }
      let before := (← get).log
      try
        if (← read).options.budgets.instantiationDepth ≤ saved.stack.size + depth then
          let description ← describeInstance key.declaration key.arguments
          throw (.exhausted (← logExhaustion .instantiationDepth ⟨.ofText description, place⟩))
        let state ← get
        let caller := (work.parents.getD node []).findSome? fun
          | .query ref => state.frameOf (.request ref)
          | _ => none
        let action := completeModule key place
        let (_, more) ← captureModuleReads (caller.elim action (withChainFrame · action))
        work ← work.discover more (some node) place (depth + 1)
        let after := (← get).log
        if after.errors > before.errors then throw .abandoned
        if after.incomplete > before.incomplete then
          if let some e := after.entries.reverse.findSome? (·.exhaustion) then throw (.exhausted e)
          throw (.defect "an incomplete module check has no budget diagnostic")
      catch why =>
        work := {work with failures := work.failures.push (node, why)}
  let mut failed : Std.HashMap Dependency Interrupt := {}
  for (start, why) in work.failures do
    let mut pending := [start]
    while let head :: tail := pending do
      pending := tail
      unless failed.contains head do
        failed := failed.insert head why
        pending := work.parents.getD head [] ++ pending
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
  let stable : Interrupt → Interrupt
    | .exhausted e => .exhausted (freeze e)
    | other => other
  modify fun s => { s with reachedModules := checked.reachedModules }
  let (work, failed) ← match result with
    | .ok value => pure value
    | .error why => throw (stable why)
  let mut memo := saved.checkedModules
  for (node, _, _) in work.pending do
    let .owner key := node | continue
    unless memo.contains key || !key.arguments.all (sharedValue saved.table saved.table.allocatedCount) do
      -- A budget belongs to a request chain. A shorter independent use may still finish.
      match failed[node]? with
      | none => memo := memo.insert key (.ok ())
      | some .abandoned => memo := memo.insert key (.error .abandoned)
      | _ => pure ()
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

/-- Attribute a source refusal to all its consuming roots during the same dependency walk.
A budget on a longer path can be retried from an independent root's own request chain. -/
@[no_expose] def checkProgramModules : CompileM Unit := do
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
          match verdicts.byRoot[root]? with
          | some (.exhausted _) => retry root s
          | other => pure other
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

end Zkc.Frontend.Typing
