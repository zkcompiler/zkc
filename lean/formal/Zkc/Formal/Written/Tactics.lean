module

public import Zkc.Formal.Written.Steps
public meta import Lean

public meta section
open Lean Meta Elab Tactic

namespace Zkc.Formal.Written

/-- Expose only the constructors of a straight-line projection. Keeping the operands and
contexts shared avoids repeated reduction of the entire dependent term during conversion. -/
partial def exposeSteps (term : Expr) : MetaM Expr := do
  let node ← withTransparency .default (whnf term)
  if node.isAppOfArity ``Zkc.Core.Term.step 8 then
    let args := node.getAppArgs
    let inst ← withTransparency .default (whnf args[5]!)
    let inst ← if inst.isAppOfArity ``Zkc.Core.Instr.op 6 then do
      let xs := inst.getAppArgs
      pure (mkAppN inst.getAppFn (xs.set! 4 (← withTransparency .default (whnf xs[4]!))))
    else pure inst
    let tail ← exposeSteps args[7]!
    let signature ← instantiateForall (← inferType node.getAppFn) (args.extract 0 7)
    let expected := signature.bindingDomain!.getAppArgs[1]!
    let current := tail.getAppArgs[1]!
    let tail := if expected == current then tail else tail.replace fun e => if e == current then some expected else none
    return mkAppN node.getAppFn ((args.set! 5 inst).set! 7 tail)
  return node

elab "expose_projection" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← Meta.transform (← goal.getType) (pre := fun e => do
    if e.isAppOfArity ``Zkc.Core.project 6 then return .done (← exposeSteps e)
    return .continue)
  replaceMainGoal [← goal.replaceTargetDefEq target]

/-- Instantiate the return rule with the context already on the goal. Inferring a
dependent environment from an empty exit can otherwise normalize all earlier bindings. -/
elab "finish_return" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  unless target.isAppOfArity ``Returns 5 do throwError "expected a returning Core trace"
  let process := target.getArg! 3
  unless process.isAppOfArity ``Zkc.Core.Term.denote 7 do throwError "expected a Core term"
  let args := process.getAppArgs
  let term := args[4]!
  unless term.isAppOfArity ``Zkc.Core.Term.ret 4 do throwError "expected the end of the verifier"
  let proof := mkAppN (mkConst ``afterReturn) #[args[0]!,args[1]!,args[2]!,args[3]!,term.getAppArgs.back!,args[6]!,args[5]!]
  goal.assign proof
  replaceMainGoal []

/-- Keep a residual failure attached to the declaration that produced the obligation. -/
elab "source_proof " place:str " => " steps:tacticSeq : tactic => do
  try
    withoutRecover (evalTactic steps)
    unless (← getUnsolvedGoals).isEmpty do throwError "open verification conditions"
  catch ex =>
    throwError "{place.getString}: WK-PROOF: {ex.toMessageData}"

end Zkc.Formal.Written
