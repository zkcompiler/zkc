module

public meta import Lean.Elab.Tactic
public import Zkc.Semantics.Interaction
public import Zkc.Source.Structured.ObservedLoop

public meta section

/-! Read checked counted Process equations, retaining the complete callback
and continuation. Definitional wrappers may expose a library presentation;
the consuming theorem checks both laws at the original reference. -/
set_option autoImplicit false
namespace ZkcTools.StructuredSource.CountedShape
open Lean Meta

/-- Both laws concern the original reference, including its full continuation. -/
structure Presentation where
  reference : Expr
  step : Expr
  zero : Expr
  succ : Expr

private def equationAt (equation : Name) (actual : Expr) : MetaM (Expr × Expr) := do
  let equationProof ← mkConstWithFreshMVarLevels equation
  let (parameters, _, type) ← forallMetaTelescopeReducing (← inferType equationProof)
  let some (_, lhs, rhs) := type.consumeMData.eq?
    | throwError "not a counted equation"
  unless lhs.getAppFn == actual.getAppFn && (← isDefEq lhs actual) do
    throwError "not the actual counted equation"
  return (← instantiateMVars (mkAppN equationProof parameters), ← instantiateMVars rhs)

/-- The final three arguments are the actual index, count and complete state.
A callback depending on the remaining count is a different shape and is refused.
Only a bounded sequence of head definitions is unfolded, stopping at the
library counted combinator or a direct recursive successor. -/
def extract (reference : Expr) : MetaM Presentation := do
  let args := reference.getAppArgs
  unless args.size ≥ 3 do throwError "a counted reference must expose index, count and state"
  let referencePrefix := mkAppN reference.getAppFn (args.extract 0 (args.size - 3))
  withLocalDeclD `state (← inferType args.back!) fun state =>
    withLocalDeclD `index (mkConst ``Nat) fun index =>
      withLocalDeclD `count (mkConst ``Nat) fun count => do
        let actual := mkAppN referencePrefix #[index, ← mkAppM ``Nat.succ #[count], state]
        let mut exposed := actual
        for _ in [:16] do
          let some name := exposed.getAppFn.constName?
            | throwError "a counted reference needs a checked recursion equation"
          let observed := name == ``Zkc.Source.Structured.ObservedLoop.counted
          let equations ← if observed then
              pure #[``Zkc.Source.Structured.ObservedLoop.counted_succ]
            else pure ((← getEqnsFor? name).getD #[])
          for equation in equations do
            let saved ← saveState
            let candidate ← try
              let (proof, rhs) ← equationAt equation exposed
              pure (some (proof, rhs))
            catch error =>
              if error.isRuntime then throw error
              if let .internal _ _ := error then throw error
              saved.restore
              pure none
            if let some (proof, rhs) := candidate then
              if rhs.isAppOfArity ``PIR.Process.bind 5 then
                let body := rhs.getAppArgs[3]!
                if body.containsFVar count.fvarId! then
                  throwError "the selected step depends on the remaining count"
                let nextIndex ← mkAppM ``Nat.succ #[index]
                let expected ← mkEq actual (← mkAppM ``PIR.Process.bind
                  #[body, mkAppN referencePrefix #[nextIndex, count]])
                unless ← isDefEq (← inferType proof) expected do
                  throwError "a counted successor must retain its complete continuation"
                let atZero := mkAppN referencePrefix #[index, mkNatLit 0, state]
                let zero ← if observed then
                    let mut zeroActual := atZero
                    for _ in [:16] do
                      if zeroActual.isAppOf ``Zkc.Source.Structured.ObservedLoop.counted then break
                      let some unfolded ← unfoldDefinition? zeroActual
                        | throwError "no counted zero equation for the actual process"
                      zeroActual := unfolded.headBeta.consumeMData
                    pure (← equationAt ``Zkc.Source.Structured.ObservedLoop.counted_zero zeroActual).1
                  else mkEqRefl atZero
                let processType ← whnf (← inferType atZero)
                let done ← mkAppOptM ``PIR.Process.done
                  #[some processType.getAppArgs[0]!, none, some state]
                unless ← isDefEq (← inferType zero) (← mkEq atZero done) do
                  throwError "a counted zero must return the complete state"
                let result : Presentation := {
                  reference := referencePrefix
                  step := ← instantiateMVars (← mkLambdaFVars #[state, index] body)
                  zero := ← instantiateMVars (← mkLambdaFVars #[index, state] zero)
                  succ := ← instantiateMVars (← mkLambdaFVars #[index, count, state] proof) }
                if result.step.hasExprMVar || result.zero.hasExprMVar || result.succ.hasExprMVar then
                  throwError "a counted presentation leaves unresolved arguments"
                return result
          if observed || exposed.isAppOf ``PIR.Process.bind then
            throwError "no counted successor equation for the actual process {name}"
          let some unfolded ← unfoldDefinition? exposed
            | throwError "no counted successor equation for the actual process {name}"
          exposed := unfolded.headBeta.consumeMData
        throwError "counted presentation exceeds the definitional wrapper limit"

end ZkcTools.StructuredSource.CountedShape
