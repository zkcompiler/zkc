import ZkcTools.ConstructionBindings.Family
import ZkcTools.ConstructionBindings.LayoutLookup

/-! Malformed raw expressions are refused before indexing their arguments.
These controls exercise proposal code; no malformed expression is evidence. -/
namespace Tests.ConnectionExpressionShapes
open Lean Meta Elab Command
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction
open ZkcTools.ConstructionBindings

structure CallbackBox where
  callback : Nat → Nat

run_cmd liftTermElabM do
  let scope ← mkListLit (mkConst ``Slot) []
  let cell ← mkAppOptM ``ConnectionFrame.Cell.unused #[some scope]
  let layout ← mkListLit (← inferType cell) [cell]
  for operand in [mkConst ``Nat.add, mkApp (mkConst ``Nat.add) (mkNatLit 1),
      mkConst ``Nat.sub, mkApp (mkConst ``Nat.sub) (mkNatLit 1), mkConst ``Nat.succ] do
    if (← LayoutLookup.select? layout operand).isSome then
      throwError "malformed arithmetic operand was accepted"
  for constructor in [mkConst ``CallbackBox.mk, mkConst ``Nat.add] do
    let refused ← try
      let _ ← Family.constructorFields constructor
      pure false
    catch error =>
      if error.isRuntime || error.isInterrupt then throw error
      pure true
    unless refused do throwError "partial or nonconstructor expression was accepted"
  let callback ← withLocalDeclD `n (mkConst ``Nat) fun n => mkLambdaFVars #[n] n
  let fields ← Family.constructorFields (mkApp (mkConst ``CallbackBox.mk) callback)
  unless fields.size == 1 && fields[0]!.1 == `callback && fields[0]!.2 == callback do
    throwError "a saturated function-valued constructor field was lost"

-- TacticM's ordinary catch inherits Core.tryCatch: resource exceptions and
-- interrupts bypass candidate recovery. Observe them only at the explicit
-- outer test boundary, without exhausting time or memory.
private meta def recoveringCandidate (exception : Exception) : Elab.Tactic.TacticM Unit := do
  try throw exception
  catch _ => throwError "candidate incorrectly swallowed a fatal exception"

private meta def observeCandidate (exception : Exception) : TermElabM (Option Exception) := do
  let goal ← mkFreshExprMVar (mkConst ``True)
  let _ : MonadExceptOf Exception TermElabM := MonadAlwaysExcept.except
  try
    let _ ← Elab.Tactic.run goal.mvarId! (recoveringCandidate exception)
    pure none
  catch error => pure (some error)

run_cmd liftTermElabM do
  for exception in [Exception.error Syntax.missing (.tagged `runtime.maxHeartbeats m!"control"),
      Exception.error Syntax.missing (.tagged `runtime.maxRecDepth m!"control"),
      Exception.internal interruptExceptionId] do
    let some observed ← observeCandidate exception
      | throwError "fatal exception did not propagate"
    unless (exception.isRuntime && observed.isRuntime) ||
        (exception.isInterrupt && observed.isInterrupt) do
      throwError "fatal exception was replaced by candidate refusal"

end Tests.ConnectionExpressionShapes
