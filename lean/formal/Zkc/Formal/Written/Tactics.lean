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

/-- Apply the projection equation at one source constructor. Its right-hand side keeps
the real continuation as a recursive call. The recursive call keeps the source context and suffix shared across instructions. -/
private def projectOne (projected : Expr) : MetaM (Expr × Expr) := do
  unless projected.isAppOfArity ``Zkc.Core.project 6 do throwError "expected a source projection"
  let p := projected.getAppArgs
  let term ← whnf p[5]!
  let t := term.getAppArgs
  let initial := p.extract 0 5
  let equation ← if term.isAppOfArity ``Zkc.Core.Term.ret 4 then
    pure (mkAppN (mkConst ``Zkc.Core.project.eq_1) (initial.push t[3]!))
  else if term.isAppOfArity ``Zkc.Core.Term.step 8 then do
    let ins ← whnf t[5]!
    let i := ins.getAppArgs
    if ins.isAppOfArity ``Zkc.Core.Instr.op 6 then
      pure (mkAppN (mkConst ``Zkc.Core.project.eq_2) (initial ++ #[t[3]!,t[4]!,i[2]!,i[4]!,t[6]!,i[5]!,t[7]!]))
    else throwError "unsupported projected instruction"
  else throwError "expected a straight-line source term"
  let eq ← whnf (← inferType equation)
  return (← whnf eq.getAppArgs[2]!, equation)

/-- Expose a single instruction, retaining the projected continuation as a shared term. -/
elab "expose_cursor" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let lhs := target.getArg! 0
  let process := lhs.getArg! 3
  let args := process.getAppArgs
  let (head, headEq) ← projectOne args[4]!
  let exposedProcess := mkAppN process.getAppFn (args.set! 4 head)
  let exposedLhs := mkAppN lhs.getAppFn (lhs.getAppArgs.set! 3 exposedProcess)
  let prop := target.getArg! 1
  let pending ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``Iff) exposedLhs prop)
  let congr := mkAppN (mkConst ``returnsTerm)
    #[args[0]!,args[1]!,args[2]!,args[3]!,args[5]!,args[6]!,lhs.getArg! 4,prop,
      args[4]!,head,headEq,pending]
  goal.assign congr
  replaceMainGoal [pending.mvarId!]

/-- Instantiate the return rule with the context already on the goal. Inferring a
dependent environment from an empty exit can otherwise normalize all earlier bindings. -/
private def closeReturn (equivalence : Bool) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let target := if equivalence && target.isAppOfArity ``Iff 2 then target.getArg! 0 else target
  unless target.isAppOfArity ``Returns 5 do throwError "expected a returning Core trace"
  let process := target.getArg! 3
  unless process.isAppOfArity ``Zkc.Core.Term.denote 7 do throwError "expected a Core term"
  let args := process.getAppArgs
  let term := args[4]!
  unless term.isAppOfArity ``Zkc.Core.Term.ret 4 do throwError "expected the end of the verifier"
  let proof := mkAppN (mkConst (if equivalence then ``afterReturnIff else ``afterReturn)) #[args[0]!,args[1]!,args[2]!,args[3]!,term.getAppArgs.back!,args[6]!,args[5]!]
  goal.assign proof
  replaceMainGoal []

elab "finish_return" : tactic => closeReturn false
elab "finish_guard_replay" : tactic => closeReturn true

/-- Keep a residual failure attached to the declaration that produced the obligation. -/
elab "source_proof " place:str " => " steps:tacticSeq : tactic => do
  try
    withoutRecover (evalTactic steps)
    unless (← getUnsolvedGoals).isEmpty do throwError "open verification conditions"
  catch ex =>
    throwError "{place.getString}: WK-PROOF: {ex.toMessageData}"

end Zkc.Formal.Written
