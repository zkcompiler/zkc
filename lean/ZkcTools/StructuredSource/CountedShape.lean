module

public meta import Lean.Elab.Tactic
public import Zkc.Semantics.Interaction

public meta section

/-! Read a counted Process presentation's checked successor equation. This
produces a proposal only; the consuming theorem checks both recursion laws,
including the complete continuation. It never evaluates an alternate loop. -/
set_option autoImplicit false
namespace ZkcTools.StructuredSource.CountedShape
open Lean Meta

/-- The final three arguments are the actual index, count and complete state.
A callback depending on the remaining count is a different shape and is refused.
The returned callback includes every occurrence frame and effect. -/
def extract (reference : Expr) : MetaM (Expr × Expr) := do
  let args := reference.getAppArgs
  unless args.size ≥ 3 do throwError "a counted reference must expose index, count and state"
  let referencePrefix := mkAppN reference.getAppFn (args.extract 0 (args.size - 3))
  let some name := reference.getAppFn.constName?
    | throwError "a counted reference needs a checked recursion equation"
  let some equations ← getEqnsFor? name
    | throwError "no checked recursion equations for {name}"
  for equation in equations do
    let saved ← saveState
    try
      let step ← withLocalDeclD `state (← inferType args.back!) fun state =>
        withLocalDeclD `index (mkConst ``Nat) fun index =>
        withLocalDeclD `count (mkConst ``Nat) fun count => do
          let actual := mkAppN referencePrefix #[index, ← mkAppM ``Nat.succ #[count], state]
          let (_, _, type) ← forallMetaTelescopeReducing
            (← inferType (← mkConstWithFreshMVarLevels equation))
          let some (_, lhs, rhs) := type.consumeMData.eq?
            | throwError "not a recursion equation"
          unless lhs.getAppFn == actual.getAppFn && (← isDefEq lhs actual) do
            throwError "not the actual successor equation"
          let rhs ← instantiateMVars rhs
          unless rhs.isAppOfArity ``PIR.Process.bind 5 do
            throwError "a counted successor must retain its complete continuation"
          let body := rhs.getAppArgs[3]!
          if body.containsFVar count.fvarId! then
            throwError "the selected step depends on the remaining count"
          mkLambdaFVars #[state, index] body
      return (referencePrefix, ← instantiateMVars step)
    catch error =>
      if error.isRuntime || error.isInterrupt then throw error
      saved.restore
  throwError "no counted successor equation for the actual process {name}"

end ZkcTools.StructuredSource.CountedShape
