module

public import Zkc.Construction.ConnectionInputs
public meta import Lean.Elab.Tactic

public meta section

/-! Untrusted proposal of root input-shape and initial-layout data. Only typed
input positions and physical selectors are searched; the kernel checks every
association. Runtime values, history contents and service identities are never
invented by the proposer. -/
set_option autoImplicit false
namespace ZkcTools.ConstructionBindings.Inputs
open Lean Meta Elab Tactic
open Zkc.Source Zkc.Source.Structured Zkc.Construction

private def applyChecked (goal : MVarId) (rule : Expr) : TacticM (List MVarId) := do
  let pending ← goal.apply rule
  for next in pending do
    unless ← next.isAssigned do
      let saved ← saveState
      try next.refl catch _ => saved.restore
  pending.filterM fun next => return !(← next.isAssigned)

private partial def inputPositions (types : Expr) : MetaM (Array Expr) := do
  let list ← whnf types
  if list.isAppOf ``List.nil then return #[]
  unless list.isAppOf ``List.cons do throwError "input schema is not a finite list"
  let args := list.getAppArgs
  let ty := args[1]!
  let rest := args[2]!
  let first ← mkAppOptM ``Var.here #[some (mkConst ``Ty), some rest, some ty]
  let others ← inputPositions rest
  let others ← others.mapM fun position =>
    mkAppOptM ``Var.there #[some (mkConst ``Ty), some rest, none, some ty, some position]
  return #[first] ++ others

private partial def derive (goal : MVarId) : TacticM Unit := goal.withContext <|
    Term.withoutErrToSorry <| withoutRecover do
  let expected ← instantiateMVars (← goal.getType)
  if expected.isAppOf ``ConnectionInputs.Shape then
    for rule in [``ConnectionInputs.Shape.nil, ``ConnectionInputs.Shape.absent,
        ``ConnectionInputs.Shape.data, ``ConnectionInputs.Shape.capability] do
      let saved ← saveState
      try
        let remaining ← applyChecked goal (← mkConstWithFreshMVarLevels rule)
        for next in remaining do derive next
        return
      catch _ => saved.restore
    throwError "input pattern does not match the fixed source ABI"
  if expected.isAppOf ``ConnectionInputs.InitialLayout then
    let saved ← saveState
    try
      let [] ← applyChecked goal (← mkConstWithFreshMVarLevels ``ConnectionInputs.InitialLayout.nil)
        | throwError "nonempty input frame"
      return
    catch _ => saved.restore
    let [head, tail] ← applyChecked goal (← mkConstWithFreshMVarLevels ``ConnectionInputs.InitialLayout.cons)
      | throwError "input frame is not a finite layout"
    derive head
    derive tail
    return
  if expected.isAppOf ``ConnectionInputs.InitialCell then
    let args := expected.getAppArgs
    let cell ← whnf args.back!
    if cell.isAppOf ``ConnectionFrame.Cell.unused then
      let [] ← applyChecked goal (← mkConstWithFreshMVarLevels ``ConnectionInputs.InitialCell.unused)
        | throwError "unused input cell mismatch"
      return
    if cell.isAppOf ``ConnectionFrame.Cell.history then
      let [] ← applyChecked goal (← mkConstWithFreshMVarLevels ``ConnectionInputs.InitialCell.history)
        | throwError "input history is not at its fixed slot or suite"
      return
    for position in ← inputPositions args[0]! do
      let saved ← saveState
      try
        let supplied := (args.extract 0 5).map some ++ #[none, some position, some args[5]!]
        let candidate ← mkAppOptM ``ConnectionInputs.InitialCell.input supplied
        let [] ← applyChecked goal candidate | throwError "input location mismatch"
        return
      catch _ => saved.restore
    throwError "input frame cell has no matching source ABI input"
  throwError "expected an input Shape or InitialLayout certificate"

elab "derive_connection_inputs" : tactic => withMainContext do
  let goal ← getMainGoal
  let pending := (← getGoals).tail
  derive goal
  setGoals pending

end ZkcTools.ConstructionBindings.Inputs
