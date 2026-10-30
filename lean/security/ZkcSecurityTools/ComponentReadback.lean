module

public import ZkcSecurity.Bindings.Transcript.HonestReadback
public meta import Lean.Elab.Tactic

@[expose] public meta section

/-! Compose installed honest component rules on the actual paired processes.
Every side premise and every returned-state continuation is checked. Refusal,
unmatched effects, or a false terminal condition leave an explicit failure. -/
namespace ZkcSecurity.Tools.ComponentReadback
open Lean Meta Elab Tactic

partial def compose (goal : MVarId) (rules : Array (TSyntax `term))
    (normalize side finish : TSyntax `tactic) : TacticM Unit :=
    goal.withContext <| Term.withoutErrToSorry <| withoutRecover do
  setGoals [goal]
  evalTactic normalize
  if (← getGoals).isEmpty then return
  let [goal] ← getGoals | throwError "readback normalizer must leave at most one goal"
  goal.withContext do
    let target ← whnf (← instantiateMVars (← goal.getType))
    unless target.isAppOf ``ZkcSecurity.FiatShamir.Readback do
      throwError "expected a paired Readback goal: {← ppGoal goal}"
    let arguments := target.getAppArgs
    let left := arguments[arguments.size - 2]!
    let right := arguments.back!
    if left.isAppOf ``PIR.Process.done && right.isAppOf ``PIR.Process.done then
      evalTactic (← `(tactic| apply ZkcSecurity.FiatShamir.Readback.done))
      evalTactic finish
      unless (← getGoals).isEmpty do throwError "honest terminal postcondition not proved"
      return
    if left.isAppOf ``PIR.Process.halt || right.isAppOf ``PIR.Process.halt then
      throwError "a stopped execution cannot establish successful honest readback"
    let original ← saveState
    let mut errors : Array MessageData := #[]
    for rule in rules do
      original.restore
      try
        let proof ← Term.elabTerm rule none
        let premises ← withTransparency .default <| goal.apply proof
        let mut continuations : Array MVarId := #[]
        for premise in premises do
          let isContinuation ← premise.withContext <|
            forallTelescope (← premise.getType) fun _ body =>
              return (← whnf body).isAppOf ``ZkcSecurity.FiatShamir.Readback
          if isContinuation then continuations := continuations.push premise
          else
            premise.withContext do
              setGoals [premise]
              evalTactic side
              unless (← getGoals).isEmpty do throwError "honest component premise not proved"
        if continuations.isEmpty then throwError "installed composition rule has no checked continuation"
        for continuation in continuations do
          let (_, body) ← continuation.intros
          compose body rules normalize side finish
        return
      catch error => errors := errors.push error.toMessageData
    original.restore
    throwError "no installed honest component rule applies: {errors}"

elab "compose_component_readback " "[" rules:term,* "]" " normalizing " normalize:tactic
    " solving " side:tactic " finishing " finish:tactic : tactic => withMainContext do
  let pending := (← getGoals).tail
  compose (← getMainGoal) rules.getElems normalize side finish
  setGoals ((← getGoals) ++ pending)

end ZkcSecurity.Tools.ComponentReadback
