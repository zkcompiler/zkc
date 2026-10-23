module

public import ZkcSecurity.FiatShamir.CostComposition
public meta import Lean.Elab.Tactic
public meta import Mathlib.Tactic.SplitIfs

@[expose] public meta section

/-! Assemble existing component cost proofs by bind, pure return, stop and
input-dependent branches. Installed laws are explicit theorem inputs. Every
composition and final budget comparison produces an ordinary kernel proof.
An unsupported component or a nonuniform continuation leaves no certificate.
-/
namespace ZkcSecurity.Tools.ComponentCost
open ZkcSecurity.FiatShamir
open Lean Meta Elab Tactic

partial def inferCost (goal : MVarId) (leaves : Array (TSyntax `term))
    (definitions : Array (TSyntax `term)) : TacticM Unit := goal.withContext <| withoutRecover do
  setGoals [goal]
  -- Installed component rules are tried before opening their process bodies.
  for leaf in leaves do
    let saved ← saveState
    try
      evalTactic (← `(tactic| apply $leaf))
      if (← getGoals).isEmpty then return
    catch _ => pure ()
    saved.restore
  let saved ← saveState
  try
    evalTactic (← `(tactic| first | exact ZkcSecurity.FiatShamir.CostComposition.done _ | exact ZkcSecurity.FiatShamir.CostComposition.halt _))
    return
  catch _ => saved.restore
  let target ← instantiateMVars (← goal.getType)
  let args := target.getAppArgs
  let process := args[args.size - 3]!
  let saved ← saveState
  try
    unless process.isAppOf ``PIR.Process.bind do throwError "not a bind"
    evalTactic (← `(tactic| apply ZkcSecurity.FiatShamir.CostComposition.bind))
    let goals ← (← getGoals).filterM fun goal => do isProp (← goal.getType)
    unless goals.length == 2 do throwError "unexpected cost bind goals"
    inferCost goals[0]! leaves definitions
    setGoals [goals[1]!]
    evalTactic (← `(tactic| intro value reached))
    inferCost (← getMainGoal) leaves definitions
    return
  catch _ => saved.restore
  let saved ← saveState
  try
    unless process.isAppOf ``ite do throwError "not a branch"
    evalTactic (← `(tactic| apply ZkcSecurity.FiatShamir.CostComposition.branch))
    let goals ← (← getGoals).filterM fun goal => do isProp (← goal.getType)
    unless goals.length == 2 do throwError "unexpected cost branch goals"
    for goal in goals do
      setGoals [goal]
      evalTactic (← `(tactic| intro branchCondition))
      inferCost (← getMainGoal) leaves definitions
    return
  catch _ => saved.restore
  let before ← instantiateMVars (← goal.getType)
  let terms := definitions ++ #[← `(PIR.Process.bind_assoc), ← `(PIR.Process.bind)]
  let simplifiers ← terms.mapM fun term => `(Parser.Tactic.simpLemma| $term:term)
  evalTactic (← `(tactic| simp only [$simplifiers,*]))
  let [after] ← getGoals | throwError "unexpected normalization goals"
  if (← instantiateMVars (← after.getType)) == before then
    throwError "no installed cost rule or structural composition applies"
  inferCost after leaves definitions

elab "derive_component_cost " "[" leaves:term,* "]" " unfolding " "[" definitions:term,* "]" : tactic => withMainContext <| withoutRecover do
  let pending := (← getGoals).tail
  let original ← getMainGoal
  let target ← instantiateMVars (← original.getType)
  unless target.isAppOf ``Typed.ChargedCostBound do
    throwError "derive_component_cost expects a charged-cost bound"
  let args := target.getAppArgs
  let cost ← mkFreshExprMVar (← inferType args.back!)
  let bounded ← mkFreshExprMVar (mkAppN target.getAppFn (args.set! (args.size - 1) cost))
  inferCost bounded.mvarId! leaves.getElems definitions.getElems
  let bounded ← instantiateMVars bounded
  if bounded.hasMVar then throwError "cost derivation left unresolved component parameters"
  let cost ← instantiateMVars cost
  let domination ← mkFreshExprMVar (← mkAppM ``LE.le #[cost, args.back!])
  original.assign (← mkAppM ``ZkcSecurity.FiatShamir.CostComposition.mono #[bounded, domination])
  setGoals [domination.mvarId!]
  evalTactic (← `(tactic| try simp only [List.length_range, add_zero, zero_add, max_self,
    ite_self,
    ← add_nsmul]))
  evalTactic (← `(tactic| (try split_ifs) <;>
    first | exact le_rfl | exact bot_le |
      (try simp only [add_zero, zero_add, ← add_nsmul];
       apply nsmul_le_nsmul_left (bot_le : (0 : ENNReal) ≤ _); omega)))

  setGoals ((← getGoals) ++ pending)

end ZkcSecurity.Tools.ComponentCost
