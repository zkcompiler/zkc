module

public import Zkc.Construction.ConnectionTargetPlacement
public meta import Lean.Elab.Tactic
public meta import Lean.LabelAttribute

public meta section

/-! Untrusted discovery of reusable checked target-body families. Matching
uses the entire indexed derivation type, including the exact source entry and
actual target. Names only select candidates; the kernel checks every use.
-/
set_option autoImplicit false
namespace ZkcTools.ConstructionBindings.TargetPlacement
open Lean Meta Elab Tactic
open Zkc.Construction.ConnectionTargetPlacement

initialize registerTraceClass `zkc.connection.placement

initialize checkedBodies : LabelExtension ←
  registerLabelAttr `connection_target_body
    "a placement-parametric family returning ConnectionTargetPlacement.CheckedBody"

register_option zkc.connection.requireReusableBodies : Bool := {
  defValue := false
  descr := "refuse applications without a matching reusable checked target body"
}

structure Use where
  family : Name
  body : Expr
  proposalNanos : Nat

structure UseCost where
  family : Name
  proposalNanos : Nat
  deriving Repr

initialize useCosts : IO.Ref (Array UseCost) ← IO.mkRef #[]

/-- Infer parameters from the actual body goal, then discharge only finite
interface obligations. A candidate cannot ask this search to derive another
alignment. Failure restores all assignments before another candidate is tried.
The family constant remains in the returned term, without unfolding its proof.
-/
def propose (goal : MVarId) (entry placement : Expr) (solve : MVarId → TacticM Unit) :
    TacticM (Option Use) := goal.withContext do
  let expected ← instantiateMVars (← goal.getType)
  let start ← IO.monoNanosNow
  for family in checkedBodies.getState (← getEnv) do
    let saved ← saveState
    try
      let constant ← mkConstWithFreshMVarLevels family
      let (parameters, _, result) ← forallMetaTelescopeReducing (← inferType constant)
      let result ← whnf result
      unless result.isAppOf ``CheckedBody do
        throwError "connection-target-body-family-type"
      -- Alignment indices contain the instantiated form, but two different
      -- declarations can normalize to equal forms. Retain exact source-entry
      -- identity as a separate checked association, before matching the form.
      unless ← withTransparency .all <| isDefEq result.getAppArgs[2]! entry do
        throwError "connection-target-body-source-entry"
      let body := mkAppN constant parameters
      let alignment ← mkAppM ``CheckedBody.alignment #[body]
      -- Routing is a parameter of the body family, but not a field of
      -- Placement. Fix it before matching target role names through a routing
      -- projection; Lean must not guess an arbitrary structure from a field.
      let alignmentType ← inferType alignment
      unless ← withTransparency .all <| isDefEq alignmentType.getAppArgs[0]! expected.getAppArgs[0]! do
        throwError "connection-target-body-routing"
      -- Match determining interface fields before result locations and the
      -- prefix. In particular the return selection determines projected
      -- outputs, rather than asking unification to invert a conditional.
      for field in [``Placement.scope, ``Placement.context, ``Placement.arguments,
          ``Placement.frames, ``Placement.layout, ``Placement.returns, ``Placement.history,
          ``Placement.outputs, ``Placement.spine, ``Placement.extent] do
        let proposed ← mkAppM field #[result.getAppArgs[5]!]
        let actual ← mkAppM field #[placement]
        unless ← withTransparency .all <| isDefEq proposed actual do
          throwError "connection-target-body-placement: {field}"
      unless ← withTransparency .all <| isDefEq (← inferType alignment) expected do
        throwError "connection-target-body-association"
      for parameter in parameters do
        if ← parameter.mvarId!.isAssigned then continue
        let type ← instantiateMVars (← parameter.mvarId!.getType)
        if type.isAppOf ``Zkc.Construction.ConnectionCertificate.Alignment ||
            type.isAppOf ``CheckedBody then
          throwError "connection-target-body-recursive-premise"
        -- Data parameters (for example a resolved message template) can be
        -- determined by a later finite equality. Never invent such data or
        -- ask the body prover for it; unresolved data refuses below.
        if (← isProp type) || type.isAppOf ``Zkc.Construction.ConnectionFrame.Readback ||
            type.isAppOf ``Zkc.Construction.ConnectionCertificate.GuardReadback ||
            type.isAppOf ``Zkc.Construction.ConnectionCertificate.HistoryReadback ||
            type.isAppOf ``Zkc.Construction.ConnectionFrame.IndexReadback then
          solve parameter.mvarId!
      let body ← instantiateMVars body
      if body.hasExprMVar then throwError "connection-target-body-unresolved-placement"
      let alignment ← mkAppM ``CheckedBody.alignment #[body]
      goal.assign alignment
      let elapsed := (← IO.monoNanosNow) - start
      useCosts.modify (·.push ⟨family, elapsed⟩)
      return some ⟨family, body, elapsed⟩
    catch error =>
      if error.isRuntime || error.isInterrupt then throw error
      trace[zkc.connection.placement] "{family}: {error.toMessageData}"
      saved.restore
  return none

end ZkcTools.ConstructionBindings.TargetPlacement
