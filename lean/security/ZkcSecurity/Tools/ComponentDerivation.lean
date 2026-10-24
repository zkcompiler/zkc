module

public import ZkcSecurity.Obligations.Derivation
public meta import Lean.Elab.Tactic
public meta import Mathlib.Tactic.Tauto

@[expose] public meta section

/-! Assemble rejection certificates from installed component contracts. The
actual process supplies sequencing, branches and stops. Mathematical admission
conditions are proved or split into two checked cases. A component may be
forgotten only when the continuation still proves the requested postcondition.
Every continuation is checked at its actual returned value and reached history.
The tactic constructs ordinary Derivation terms, interpreted by the existing
reduction engine; it introduces no new proof or probability semantics. -/

namespace ZkcSecurity.Tools.ComponentDerivation
open Lean Meta Elab Tactic

def derivationGoals : TacticM (List MVarId) := do
  (← getGoals).filterM fun goal => goal.withContext do
    forallTelescope (← goal.getType) fun _ body =>
      pure (body.isAppOf ``Zkc.Obligations.Derivation)

def proveSide (goal : MVarId) : TacticM Bool := do
  let saved ← saveState
  try
    setGoals [goal]
    evalTactic (← `(tactic| solve | assumption | tauto))
    if (← getGoals).isEmpty then return true
  catch _ => pure ()
  saved.restore
  return false

partial def derive (goal : MVarId) (leaves definitions : Array (TSyntax `term))
    (finish : TSyntax `tactic) : TacticM Unit := goal.withContext <| classical <| Term.withoutErrToSorry <| withoutRecover do
  setGoals [goal]
  let simpTerms := definitions ++ #[← `(PIR.Process.bind_assoc), ← `(PIR.Process.bind)]
  let simpLemmas ← simpTerms.mapM fun term => `(Parser.Tactic.simpLemma| $term:term)
  evalTactic (← `(tactic| try simp only [$simpLemmas,*]))
  if (← getGoals).isEmpty then return
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let process := target.getAppArgs.back!
  if process.isAppOf ``PIR.Process.halt then
    evalTactic (← `(tactic| exact Zkc.Obligations.Derivation.halt _))
    return
  if process.isAppOf ``PIR.Process.done then
    evalTactic (← `(tactic| apply Zkc.Obligations.Derivation.done))
    evalTactic finish
    unless (← getGoals).isEmpty do throwError "terminal obligation remains: {← ppGoal (← getMainGoal)}"
    return
  if process.isAppOf ``ite then
    evalTactic (← `(tactic| split))
    for branch in ← getGoals do derive branch leaves definitions finish
    return
  unless process.isAppOf ``PIR.Process.bind do
    throwError "no installed structural derivation for {process.getAppFn}"
  let original ← saveState
  let mut missing : Option Expr := none
  let mut errors : Array MessageData := #[]
  for leaf in leaves do
    original.restore
    try
      evalTactic (← `(tactic| apply Zkc.Obligations.Derivation.bind))
      let [head, continuation] ← derivationGoals | throwError "unexpected bind goals"
      setGoals [head]
      -- Elaborate indices normally, but do not unfold an opaque component
      -- body while trying to match the next installed theorem.
      let proof ← Term.elabTerm leaf none
      setGoals (← withReducible <| head.apply proof)
      let obligations ← getGoals
      let mut ready := true
      for obligation in obligations do
        unless ← proveSide obligation do
          let ty ← instantiateMVars (← obligation.getType)
          if (← isProp ty) && !ty.hasMVar then missing := some ty
          ready := false
      if ready then
        setGoals [continuation]
        evalTactic (← `(tactic| intro reached value holds))
        derive (← getMainGoal) leaves definitions finish
        return
    catch error => errors := errors.push error.toMessageData
  original.restore
  if let some premise := missing then
    -- Splitting a mathematical admission condition supplies no new assumption:
    -- both branches must produce derivations of the same actual process.
    let negative ← mkFreshExprMVar (mkNot premise)
    let refuted ← proveSide negative.mvarId!
    original.restore
    if !refuted then
      let conditionSyntax ← Term.exprToSyntax premise
      evalTactic (← `(tactic| by_cases componentCondition : $conditionSyntax))
      for branch in ← getGoals do derive branch leaves definitions finish
      return
  evalTactic (← `(tactic| apply Zkc.Obligations.Derivation.bind))
  let [head, continuation] ← derivationGoals | throwError "unexpected bind goals"
  setGoals [head]
  evalTactic (← `(tactic| exact ZkcSecurity.Obligations.unrestricted _ _))
  setGoals [continuation]
  evalTactic (← `(tactic| intro reached value holds))
  try
    derive (← getMainGoal) leaves definitions finish
  catch error =>
    throwError "component derivation failed: {error.toMessageData}\ninstalled rules: {errors}"

elab "derive_component_rejection " "[" leaves:term,* "]" " unfolding " "[" definitions:term,* "]" " finishing " finish:tactic : tactic =>
    withMainContext <| withoutRecover do
  let target ← instantiateMVars (← getMainTarget)
  unless target.isAppOf ``Zkc.Obligations.Derivation do
    throwError "derive_component_rejection expects a component derivation"
  let pending := (← getGoals).tail
  derive (← getMainGoal) leaves.getElems definitions.getElems finish
  setGoals ((← getGoals) ++ pending)
end ZkcSecurity.Tools.ComponentDerivation

