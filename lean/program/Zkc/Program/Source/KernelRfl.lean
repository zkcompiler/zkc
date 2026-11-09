module

public meta import Lean.Elab.Tactic

@[expose] public section

/-! Definitional equalities between computations, such as an admission phase
and its literal result, are checked by the kernel's evaluator alone. The
elaborator does not first attempt the same reduction with its slower unifier.

An equation may mention local variables, section variables and instances, or
be stated under universal binders. The local declarations it depends on are
reverted, and the kernel checks `fun xs => Eq.refl lhs` against the closed
universal statement: it decides the equation for every value of the binders at
once, by reduction with the binders left symbolic. -/

namespace Zkc.Source
open Lean Meta Elab Tactic

/-- Close `lhs = rhs`, or `∀ xs, lhs = rhs`, with `Eq.refl lhs` under the
binders, checked only by the kernel. The equation may be stated through
reducible definitions. The local declarations the goal depends on
are reverted first, so the checked statement is closed. As with `decide +kernel`, the proof is an
auxiliary theorem; a failed kernel check is an ordinary error, never an
assumption. -/
syntax (name := kernelRfl) "kernel_rfl" : tactic

/-- The proof `fun xs => Eq.refl lhs` of a closed statement `∀ xs, lhs = rhs`;
`let` binders are kept. -/
meta def kernelRflProof (statement : Expr) : MetaM Expr := do
  let proof ← mkFreshExprSyntheticOpaqueMVar statement
  let (_, body) ← proof.mvarId!.intros
  body.withContext do
    let type ← whnfR (← instantiateMVars (← body.getType))
    let some (α, lhs, _) := type.eq?
      | throwError "kernel_rfl: expected an equation under universal binders, got{indentExpr statement}"
    body.assign (mkApp2 (mkConst ``Eq.refl [← getLevel α]) α lhs)
  instantiateMVars proof

/-- The local declarations of a declaration's type and value. -/
meta def declarationFVars (fvar : FVarId) : MetaM (Array FVarId) := do
  let declaration ← fvar.getDecl
  let mut inner := collectFVars {} (← instantiateMVars declaration.type)
  if let some value := declaration.value? then
    inner := collectFVars inner (← instantiateMVars value)
  return inner.fvarIds

/-- The local declarations an expression depends on, directly or through the
types and values of other declarations, in context order. Reverting them also
reverts every declaration that depends on one of them, so those and their own
dependencies are included too, and the reverted statement is closed. -/
meta def dependencies (expression : Expr) : MetaM (Array FVarId) := do
  let context ← getLCtx
  let mut found : FVarIdSet := {}
  let mut pending := (collectFVars {} expression).fvarIds.toList
  let mut changed := true
  while changed do
    while !pending.isEmpty do
      let fvar := pending.head!
      pending := pending.tail!
      if found.contains fvar then continue
      found := found.insert fvar
      pending := pending ++ (← declarationFVars fvar).toList
    changed := false
    for declaration in context do
      if declaration.isImplementationDetail || found.contains declaration.fvarId then continue
      let uses ← declarationFVars declaration.fvarId
      if uses.any found.contains then
        pending := pending ++ [declaration.fvarId]
        changed := true
  return context.foldl (init := #[]) fun selected declaration =>
    if found.contains declaration.fvarId then selected.push declaration.fvarId else selected

@[tactic kernelRfl] meta def evalKernelRfl : Tactic := fun _ => withMainContext do
  let goal ← getMainGoal
  let type ← instantiateMVars (← goal.getType)
  if type.hasExprMVar || type.hasLevelMVar then
    throwError "kernel_rfl: the goal has unassigned metavariables{indentExpr type}"
  let (_, closed) ← goal.revert (← dependencies type) (preserveOrder := true)
  closed.withContext do
    let statement ← instantiateMVars (← closed.getType)
    if statement.hasFVar || statement.hasExprMVar then
      throwError "kernel_rfl: the reverted goal is not closed{indentExpr statement}"
    let proof ← kernelRflProof statement
    let levels := (collectLevelParams {} statement).params
    let lemmaLevels := (← Term.getLevelNames).reverse.filter levels.contains
    -- Preserve the kernel's diagnostic. Its timeout/recursion exceptions are
    -- ordinary messages, not the elaborator's tagged `Exception.isRuntime`.
    -- Rewriting every failure as a false equation would misreport resource limits.
    let name ← withOptions (Elab.async.set · false) do
      mkAuxLemma lemmaLevels statement proof
    closed.assign (mkConst name (lemmaLevels.map .param))
  replaceMainGoal []

end Zkc.Source
