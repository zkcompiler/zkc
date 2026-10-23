module

public import ZkcSecurity.FiatShamir.DomainReduction
public meta import Lean.Elab.Tactic

@[expose] public meta section

/-! Compose installed source-to-presentation bridges at the actual reached
history and complete returned value. Guard splits preserve both branches;
terminal and stopped results retain the exact result and stop reason. The
normalizer supplies checked pure/helper equations, not an alternate evaluator.
The result is an ordinary kernel-checked Bridge proof. -/

open Lean Meta Elab Tactic
namespace ZkcSecurity.Tools.ComponentBridge

def tryClose (goal : MVarId) (tactic : TSyntax `tactic) : TacticM Bool := do
  let saved ← saveState
  try
    setGoals [goal]
    evalTactic tactic
    if (← getGoals).isEmpty then return true
  catch _ => pure ()
  saved.restore
  return false

partial def compose (goal : MVarId) (leaves : Array (TSyntax `term))
    (normalize side finish : TSyntax `tactic) : TacticM Unit :=
    goal.withContext <| Term.withoutErrToSorry <| withoutRecover do
  setGoals [goal]
  evalTactic (← `(tactic| try simp_all only [ite_true, ite_false]))
  if (← getGoals).isEmpty then return
  evalTactic normalize
  if (← getGoals).isEmpty then return
  let [goal] ← getGoals | throwError "normalizer must leave at most one goal"
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    unless target.isAppOf ``ZkcSecurity.FiatShamir.DomainReduction.Bridge do
      throwError "expected a Bridge"
    let args := target.getAppArgs
    let actual := args[args.size - 2]!
    let presented := args.back!
    if actual.isAppOf ``PIR.Process.done && presented.isAppOf ``PIR.Process.done then
      evalTactic (← `(tactic| apply ZkcSecurity.FiatShamir.DomainReduction.Bridge.done))
      evalTactic finish
      unless (← getGoals).isEmpty do throwError "terminal postcondition not proved"
      return
    if actual.isAppOf ``PIR.Process.halt then
      evalTactic (← `(tactic| exact ZkcSecurity.FiatShamir.DomainReduction.Bridge.halt _ _))
      return
    if actual.isAppOf ``ite || presented.isAppOf ``ite then
      let conditional := if actual.isAppOf ``ite then actual else presented
      let conditionSyntax ← goal.withContext <| Term.exprToSyntax conditional.getAppArgs[1]!
      evalTactic (← `(tactic| by_cases componentCondition : $conditionSyntax))
      for branch in ← getGoals do compose branch leaves normalize side finish
      return
    let original ← saveState
    let mut errors : Array MessageData := #[]
    for leaf in leaves do
      original.restore
      try
        evalTactic (← `(tactic| apply ZkcSecurity.FiatShamir.DomainReduction.Bridge.bind))
        let componentGoals ← (← getGoals).filterM fun g => g.withContext do
          forallTelescope (← g.getType) fun _ body =>
            pure (body.isAppOf ``ZkcSecurity.FiatShamir.DomainReduction.Bridge)
        let [head, continuation] := componentGoals | throwError "unexpected bind premises: {componentGoals}"
        setGoals [head]
        let proof ← Term.elabTerm leaf none
        setGoals (← withReducible <| head.apply proof)
        for premise in ← getGoals do
          unless ← tryClose premise side do throwError "component premise unproved"
        setGoals [continuation]
        evalTactic (← `(tactic| intro reached value holds))
        compose (← getMainGoal) leaves normalize side finish
        return
      catch error => errors := errors.push error.toMessageData
    original.restore
    throwError "no installed bridge for the reached component and continuation: {errors}"

elab "compose_component_bridge " "[" leaves:term,* "]" " normalizing " normalizer:tactic
    " solving " side:tactic " finishing " finish:tactic : tactic => withMainContext do
  let pending := (← getGoals).tail
  compose (← getMainGoal) leaves.getElems normalizer side finish
  setGoals ((← getGoals) ++ pending)

end ZkcSecurity.Tools.ComponentBridge
