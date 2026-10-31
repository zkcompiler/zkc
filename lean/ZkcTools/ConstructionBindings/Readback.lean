module

public import Zkc.Construction.ConnectionFrame
public import Zkc.Construction.ConnectionTargetPlacement
public meta import ZkcTools.ConstructionBindings.LayoutLookup
public meta import Lean.Elab.Tactic

public meta section

/-! Untrusted proposal of finite source-output readback certificates.

The tactic searches the already fixed symbolic frame. Every chosen location
is justified by a kernel-checked equality and the resulting certificate is
interpreted by Readback.sound. A failed search leaves the obligation visible;
it cannot relax source outputs, nominal types or the full return contract.
-/
set_option autoImplicit false
namespace ZkcTools.ConstructionBindings.Readback
open Lean Meta Elab Tactic
open Zkc.Construction

initialize registerTraceClass `zkc.connection.readback

private def cells (layout : Expr) : MetaM (Array Expr) := do
  let mut result := #[]
  let mut rest := layout
  repeat
    rest ← whnf rest
    if rest.isAppOf ``List.nil then return result
    unless rest.isAppOf ``List.cons do
      throwError "readback layout is not a finite list: {rest}"
    result := result.push rest.getAppArgs[1]!
    rest := rest.getAppArgs[2]!
  return result

private def readbackGoals (goals : List MVarId) : MetaM (List MVarId) :=
  goals.filterM fun goal => do
    if ← goal.isAssigned then return false
    let type ← whnf (← instantiateMVars (← goal.getType))
    -- `apply` also reports pre-existing operand holes. They are determined
    -- by the current equality or a later tuple entry, not separate certificates.
    return !(type.isAppOf ``List || type.isConstOf ``Nat ||
      type.isAppOf ``Zkc.Source.Structured.NormalForm.Term || type.isAppOf ``Zkc.Source.Structured.NormalForm.Terms ||
      type.isAppOf ``Zkc.Source.Structured.NormalForm.Comp)

private partial def derive (goal : MVarId) : TacticM Unit := goal.withContext <| Term.withoutErrToSorry <| withoutRecover do
  let target ← instantiateMVars (← goal.getType)
  unless target.isAppOf ``ConnectionFrame.Readback do
    throwError "expected a source-output Readback certificate, got {target}"
  -- Placement families carry finite interface readbacks as ordinary parameters.
  -- Reuse them before inspecting a potentially symbolic caller prefix.
  let saved ← saveState
  try
    goal.assumption
    return
  catch _ => saved.restore
  let arguments := target.getAppArgs
  let layout := arguments[1]!
  let values ← whnf arguments[3]!
  if values.isAppOf ``Zkc.Source.Values.nil then
    let pending ← readbackGoals (← goal.apply (← mkConstWithFreshMVarLevels ``ConnectionFrame.Readback.nil))
    unless pending.isEmpty do throwError "empty source output did not match an empty layout"
    return
  unless values.isAppOf ``Zkc.Source.Values.cons do
    throwError "source outputs are not an explicit typed tuple: {values}"
  let source := values.getAppArgs[values.getAppArgs.size - 2]!
  let source ← whnf source
  -- A reusable return projection may be a symbolic Boolean parameter. Split
  -- that finite interface choice in the family proof, after the effectful
  -- prefix has already been derived, rather than duplicating that prefix.
  let locations ← whnf arguments[4]!
  for parameter in ← getLCtx do
    if parameter.type.isConstOf ``Bool && source.containsFVar parameter.fvarId &&
        locations.containsFVar parameter.fvarId then
      for branch in ← goal.cases parameter.fvarId do derive branch.mvarId
      return
  if source.isAppOf ``Zkc.Source.Structured.NormalForm.Comp.absent then
    let [tail] ← readbackGoals (← goal.apply (← mkConstWithFreshMVarLevels ``ConnectionFrame.Readback.absent))
      | throwError "hidden source output requires an absent location"
    derive tail
    return
  if source.isAppOf ``Zkc.Source.Structured.NormalForm.Comp.present then
    let term ← whnf source.getAppArgs.back!
    if term.isAppOf ``Zkc.Source.Structured.NormalForm.Term.capability then
      let [tail] ← readbackGoals (← goal.apply (← mkConstWithFreshMVarLevels ``ConnectionFrame.Readback.capability))
        | throwError "service output requires its exact ABI capability"
      derive tail
      return
  -- The requested location is often already fixed by the actual instruction.
  -- Query it with a compositional proof before enumerating any caller cells.
  let saved ← saveState
  try
    let locations ← whnf arguments[4]!
    unless locations.isAppOf ``List.cons do throwError "readback-location-undetermined"
    let location ← whnf locations.getAppArgs[1]!
    unless location.isAppOf ``Original.Location.data do throwError "readback-not-data-location"
    let reference := location.getAppArgs.back!
    let some selected ← LayoutLookup.select? layout reference
      | throwError "readback-finite-lookup-deferred"
    let cell ← whnf selected.cell
    let rules := if cell.isAppOf ``ConnectionFrame.Cell.guarded then
        [``ConnectionFrame.Readback.guardedOriginal, ``ConnectionFrame.Readback.guardedTrue]
      else [``ConnectionFrame.Readback.data]
    for rule in rules do
      let attempt ← saveState
      try
        let constructor ← mkConstWithFreshMVarLevels rule
        let pending ← readbackGoals (← goal.apply constructor)
        for checked in pending do
          if (← instantiateMVars (← checked.getType)).isAppOf ``Eq then
            unless ← isDefEq (← inferType selected.proof) (← checked.getType) do
              throwError "readback-finite-lookup-mismatch"
            checked.assign selected.proof
        let [tail] ← pending.filterM fun pending => return !(← pending.isAssigned)
          | throwError "readback-finite-lookup-tail"
        derive tail
        return
      catch error =>
        if error.isRuntime || error.isInterrupt then throw error
        attempt.restore
    throwError "readback-finite-lookup-cell"
  catch error =>
    if error.isRuntime || error.isInterrupt then throw error
    saved.restore
  -- A failed selected-cell query over an open layout must wait for its
  -- determining predecessors. Enumerating or applying the fresh-cell rule
  -- would otherwise unfold every unresolved presence/guard substitution.
  if (← instantiateMVars layout).hasExprMVar then
    throwError "readback-undetermined-layout"
  -- The fresh receive cell can be checked without inspecting the prefix. The
  -- supplied reference remains fixed and is compared with the actual length.
  let saved ← saveState
  try
    let [checked, tail] ← readbackGoals
        (← goal.apply (← mkConstWithFreshMVarLevels ``ConnectionFrame.Readback.data))
      | throwError "readback-not-fresh-data"
    let expanded ← whnf layout
    unless expanded.isAppOf ``List.append do throwError "readback-not-appended-layout"
    let parts := expanded.getAppArgs
    let suffix ← whnf parts.back!
    unless suffix.isAppOf ``List.cons do throwError "readback-not-appended-cell"
    let entries := suffix.getAppArgs
    unless (← whnf entries.back!).isAppOf ``List.nil do throwError "readback-not-single-cell"
    let law ← mkAppM ``ConnectionTargetPlacement.appendedCell
      #[parts[parts.size - 2]!, entries[entries.size - 2]!]
    let [offset] ← checked.apply law | throwError "readback-fresh-cell-mismatch"
    trace[zkc.connection.readback] "fresh offset: {← offset.getType}"
    setGoals [offset]
    evalTactic (← `(tactic|
      simp only [Zkc.Construction.ConnectionFrameLookup.receive_length,
        Zkc.Construction.ConnectionFrameLookup.tuple_length,
        Zkc.Construction.ConnectionFrameLookup.guard_length,
        Zkc.Construction.ConnectionCertificate.GuardReadback.refine,
        List.length_append, List.length_map, List.length_set,
        List.length_cons, List.length_nil]))
    for remaining in ← getGoals do remaining.refl
    derive tail
    return
  catch error =>
    if error.isRuntime || error.isInterrupt then throw error
    trace[zkc.connection.readback] "fresh cell: {error.toMessageData}"
    saved.restore
  let candidates ← cells layout
  -- Helper operands and root outputs usually fix their physical locations.
  -- Do not retry every other cell before checking the one already requested.
  -- Unspecified locations still use the ordinary finite proposal search; in
  -- both cases the same Readback constructor checks the selected cell.
  let locations ← whnf arguments[4]!
  let fixed ← if locations.isAppOf ``List.cons then do
      let location ← whnf locations.getAppArgs[1]!
      if location.isAppOf ``Original.Location.data then
        getNatValue? (← whnf location.getAppArgs.back!)
      else pure none
    else pure none
  let references := match fixed with
    | some reference => if reference < candidates.size then #[reference] else #[]
    | none => (List.range candidates.size).toArray
  let mut selected : Option MVarId := none
  for reference in references do
    let cell ← whnf candidates[reference]!
    let rules := if cell.isAppOf ``ConnectionFrame.Cell.guarded then
        [``ConnectionFrame.Readback.guardedOriginal, ``ConnectionFrame.Readback.guardedTrue]
      else if cell.isAppOf ``ConnectionFrame.Cell.data then [``ConnectionFrame.Readback.data]
      else []
    for rule in rules do
      let saved ← saveState
      try
        setGoals [goal]
        let position := Syntax.mkNumLit (toString reference)
        evalTactic (← `(tactic| apply ($(mkIdent rule) $position:num)))
        let pending ← readbackGoals (← getGoals)
        for checked in pending do
          if (← instantiateMVars (← checked.getType)).isAppOf ``Eq then checked.refl
        let [tail] ← pending.filterM fun pending => return !(← pending.isAssigned)
          | throwError "data readback did not expose its static equality and suffix"
        selected := some tail
        break
      catch error =>
        trace[zkc.connection.readback] "candidate {reference}: {error.toMessageData}"
        saved.restore
    if selected.isSome then break
  let some tail := selected
    | throwError "no checked physical cell contains source output {source}; layout has {candidates.size} cells"
  derive tail

/-- Propose and check locations for all source outputs. The proposition fixes
those outputs before search; every successful path constructs Readback data. -/
elab "derive_source_readback" : tactic => withMainContext do
  let goal ← getMainGoal
  let pending := (← getGoals).tail
  let start ← IO.monoMsNow
  derive goal
  let elapsed := (← IO.monoMsNow) - start
  if elapsed > 1000 && (← getOptions).getBool `zkc.connection.trace false then
    let destination := (← getOptions).get `zkc.connection.traceFile ("" : String)
    if !destination.isEmpty then
      IO.FS.withFile destination .append fun handle =>
        handle.putStrLn s!"readback ms={elapsed}"
  setGoals pending

end ZkcTools.ConstructionBindings.Readback
