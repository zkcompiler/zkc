module

public meta import Lean.Elab.Tactic

@[expose] public section

/-! Definitional equalities between closed computations, such as an admission
phase and its literal result, are checked by the kernel's evaluator alone. The
elaborator does not first attempt the same reduction with its slower unifier. -/

namespace Zkc.Source
open Lean Meta Elab Tactic

/-- Close `lhs = rhs` with `Eq.refl lhs`, checked only by the kernel. As with
`decide +kernel`, the proof is an auxiliary theorem; a failed kernel check is
an ordinary error, never an assumption. -/
syntax (name := kernelRfl) "kernel_rfl" : tactic

@[tactic kernelRfl] meta def evalKernelRfl : Tactic := fun _ => withMainContext do
  let goal ← getMainGoal
  let type ← instantiateMVars (← goal.getType)
  let some (α, lhs, _) := type.eq? | throwError "kernel_rfl: expected an equality goal, got{indentExpr type}"
  if type.hasExprMVar || type.hasLevelMVar || type.hasFVar then
    throwError "kernel_rfl: expected a closed equality goal, got{indentExpr type}"
  let proof := mkApp2 (mkConst ``Eq.refl [← getLevel α]) α lhs
  let levels := (collectLevelParams {} type).params
  let lemmaLevels := (← Term.getLevelNames).reverse.filter levels.contains
  let name ← try
      withOptions (Elab.async.set · false) do
        mkAuxLemma lemmaLevels type proof
    catch error =>
      if error.isInterrupt || error.isRuntime then throw error
      throwError "kernel_rfl: the kernel does not reduce both sides to the same value{indentExpr type}"
  goal.assign (mkConst name (lemmaLevels.map .param))
  replaceMainGoal []

end Zkc.Source
