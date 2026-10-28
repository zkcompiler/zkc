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

private partial def derive (goal : MVarId) : TacticM Unit := goal.withContext <| Term.withoutErrToSorry <| withoutRecover do
  let target ← instantiateMVars (← goal.getType)
  unless target.isAppOf ``ConnectionFrame.Readback do
    throwError "expected a source-output Readback certificate, got {target}"
  let arguments := target.getAppArgs
  let layout := arguments[1]!
  let values ← whnf arguments[3]!
  if values.isAppOf ``Zkc.Source.Values.nil then
    let pending ← goal.apply (← mkConstWithFreshMVarLevels ``ConnectionFrame.Readback.nil)
    unless pending.isEmpty do throwError "empty source output did not match an empty layout"
    return
  unless values.isAppOf ``Zkc.Source.Values.cons do
    throwError "source outputs are not an explicit typed tuple: {values}"
  let source := values.getAppArgs[values.getAppArgs.size - 2]!
  let source ← whnf source
  if source.isAppOf ``Zkc.Source.Structured.NormalForm.Comp.absent then
    let [tail] ← goal.apply (← mkConstWithFreshMVarLevels ``ConnectionFrame.Readback.absent)
      | throwError "hidden source output requires an absent location"
    derive tail
    return
  if source.isAppOf ``Zkc.Source.Structured.NormalForm.Comp.present then
    let term ← whnf source.getAppArgs.back!
    if term.isAppOf ``Zkc.Source.Structured.NormalForm.Term.capability then
      let [tail] ← goal.apply (← mkConstWithFreshMVarLevels ``ConnectionFrame.Readback.capability)
        | throwError "service output requires its exact ABI capability"
      derive tail
      return
  let candidates ← cells layout
  for reference in [:candidates.size] do
    let cell ← whnf candidates[reference]!
    unless cell.isAppOf ``ConnectionFrame.Cell.data do continue
    let saved ← saveState
    try
      setGoals [goal]
      let position := Syntax.mkNumLit (toString reference)
      evalTactic (← `(tactic| apply Zkc.Construction.ConnectionFrame.Readback.data $position:num))
      let checked :: tail :: [] ← getGoals
        | throwError "data readback did not expose its static equality and suffix"
      checked.refl
      derive tail
      return
    catch _ => saved.restore
  throwError "no checked physical cell contains source output {source}; layout has {candidates.size} cells"

/-- Propose and check locations for all source outputs. The proposition fixes
those outputs before search; every successful path constructs Readback data. -/
elab "derive_source_readback" : tactic => withMainContext do
  let goal ← getMainGoal
  let pending := (← getGoals).tail
  derive goal
  setGoals pending

end ZkcTools.ConstructionBindings.Readback
