module

public import Zkc.Construction.ConnectionFrame
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
    return !(type.isAppOf ``List || type.isConstOf ``Nat)

private partial def derive (goal : MVarId) : TacticM Unit := goal.withContext <| Term.withoutErrToSorry <| withoutRecover do
  let target ← instantiateMVars (← goal.getType)
  unless target.isAppOf ``ConnectionFrame.Readback do
    throwError "expected a source-output Readback certificate, got {target}"
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
      catch _ => saved.restore
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
