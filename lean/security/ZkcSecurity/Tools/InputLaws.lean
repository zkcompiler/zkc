module

public import ZkcSecurity.Tools.SubjectABI
public meta import Lean.Elab.Tactic
public meta import Mathlib.Tactic.Substs

@[expose] public meta section

/-! Transport input assertions through selected, independently proved laws.
Every extra premise is proved in the caller's context. The honest-pair helper
also splits policy and relation facts after the checked ABI projection; the
component composer still proves the complete execution and successful terminal.
Adversarial assembly uses only its own source guards and component guarantees.
-/
namespace ZkcSecurity.Tools.InputLaws
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
Extra premises come from the local context or the supplied checked tactic. -/
def forwardIff (law : TSyntax `term) (side : Option (TSyntax `tactic) := none) : TacticM FVarId := withMainContext do
  let callerGoals ← getGoals
  let goal ← getMainGoal
  let proof ← Term.elabTerm law none
  let original ← saveState
  let mut errors : Array MessageData := #[]
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
          if parameter.isMVar then
            match side with
            | none => parameter.mvarId!.assumption
            | some solve =>
              setGoals [parameter.mvarId!]
              evalTactic solve
              unless (← getGoals).isEmpty do throwError "input law premise remains unproved"
        let applied ← instantiateMVars (mkAppN proof parameters)
        if applied.hasExprMVar then return none
        let derived ← mkAppM ``Iff.mp #[applied, declaration.toExpr]
        return some derived : TacticM (Option Expr))
      catch error =>
        errors := errors.push error.toMessageData
        pure none
      if let some derived := found then
        setGoals callerGoals
        let type ← normalizeCarrierTypes (← inferType derived)
        let (fact, next) ← goal.note (← mkFreshUserName `inputFact) derived (some type)
        replaceMainGoal [next]
        return fact
  original.restore
  throwError "the supplied input law does not apply with proved premises: {errors}"

/-- Transport an available input assertion through a selected mathematical
law, proving every extra premise by the supplied checked tactic. -/
elab "apply_input_law " law:term " solving " side:tactic : tactic =>
    Term.withoutErrToSorry <| withoutRecover do
  let _ ← forwardIff law (some side)

elab "prepare_honest_readback " "using " policy:term " and " relation:term : tactic =>
    Term.withoutErrToSorry <| withoutRecover do
  let _ ← forwardIff policy
  splitFacts
  let _ ← forwardIff relation
  splitFacts
  evalTactic (← `(tactic| subst_vars))

end ZkcSecurity.Tools.InputLaws
