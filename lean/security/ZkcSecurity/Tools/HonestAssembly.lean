module

public import ZkcSecurity.Tools.SubjectABI
public meta import Lean.Elab.Tactic
public meta import Mathlib.Tactic.Substs

@[expose] public meta section

/-! Prepare an honest-pair proof from the fixed typed ABI, input policy and
one independently proved relation equation. The caller first applies its
checked ABI projection. This tool applies the selected laws, exposes carrier
types, eliminates conjunctions and substitutes equalities. The component
composer still has to prove the complete execution and successful terminal.
-/
namespace ZkcSecurity.Tools.HonestAssembly
open Lean Meta Elab Tactic

partial def splitFacts : TacticM Unit := do
  let goals ← getGoals
  let some goal := goals.head? | return
  let found ← goal.withContext do
    for declaration in ← getLCtx do
      unless declaration.isImplementationDetail do
        if declaration.type.isAppOf ``And then return some declaration.fvarId
    return none
  if let some fact := found then
    let branches ← goal.cases fact
    let mut remaining := []
    for branch in branches do
      setGoals [branch.mvarId]
      splitFacts
      remaining := remaining ++ (← getGoals)
    setGoals (remaining ++ goals.tail!)

/-- Expose only carrier-type projections in derived facts. Arithmetic tactics
must see Nat rather than an opaque model's index carrier; source terms and
mathematical operations remain opaque. The replacement is definitionally equal. -/
def normalizeCarrierTypes (type : Expr) : MetaM Expr :=
  transform type (pre := fun expression => do
    if expression.isAppOf ``Zkc.Source.Structured.Carriers.Value ||
        expression.isAppOf ``Zkc.Source.Structured.Carriers.Field ||
        expression.isAppOf ``Zkc.Source.Structured.Carriers.Group then
      let normalized ← withTransparency .default <| whnf expression
      if normalized != expression then return .visit normalized
    return .continue)

/-- Apply a supplied iff to a matching assumption. Dependent ABI aliases are
resolved by ordinary definitional equality, without rewriting unrelated goals.
All extra premises must already be available in the local context. -/
def forwardIff (law : TSyntax `term) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let proof ← Term.elabTerm law none
  let original ← saveState
  for declaration in ← getLCtx do
    unless declaration.isImplementationDetail do
      original.restore
      let found ← try (do
        let (parameters, _, body) ← forallMetaTelescopeReducing (← inferType proof)
        unless body.isAppOfArity ``Iff 2 do return none
        unless ← withTransparency .default <| isDefEq body.getAppArgs[0]! declaration.type do
          return none
        for parameter in parameters do
          let parameter ← instantiateMVars parameter
          if parameter.isMVar then parameter.mvarId!.assumption
        let applied ← instantiateMVars (mkAppN proof parameters)
        if applied.hasExprMVar then return none
        let derived ← mkAppM ``Iff.mp #[applied, declaration.toExpr]
        return some derived : TacticM (Option Expr))
      catch _ => pure none
      if let some derived := found then
        let type ← normalizeCarrierTypes (← inferType derived)
        let (_, next) ← goal.note (← mkFreshUserName `inputFact) derived (some type)
        replaceMainGoal [next]
        return
  original.restore
  throwError "the supplied input law does not apply with proved premises"

elab "prepare_honest_readback " "using " policy:term " and " relation:term : tactic =>
    Term.withoutErrToSorry <| withoutRecover do
  forwardIff policy
  splitFacts
  forwardIff relation
  splitFacts
  evalTactic (← `(tactic| subst_vars))

end ZkcSecurity.Tools.HonestAssembly
