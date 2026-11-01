module

public import Zkc.Construction.ConnectionTargetPlacement
public meta import ZkcTools.ConstructionBindings.Interface
public meta import ZkcTools.ConstructionBindings.TargetEquality
public meta import Lean.Elab.Tactic
public meta import Lean.LabelAttribute
public meta import Lean.Meta.Closure

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

register_option zkc.connection.cacheInterfaceFacts : Bool := {
  defValue := false
  descr := "check finite interface facts separately before applying a body family"
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

private def phase (message : MessageData) : CoreM Unit := do
  if !(← getOptions).getBool `zkc.connection.trace false then return
  let destination := (← getOptions).get `zkc.connection.traceFile ("" : String)
  unless destination.isEmpty do
    IO.FS.withFile destination .append fun handle => do
      handle.putStrLn s!"{← IO.monoMsNow} {← message.toString}"

private def sameKeyTag (key entry : Expr) : MetaM Bool := do
  let actual := (← inferType entry).getAppArgs.back!
  let name := fun key => mkApp (mkConst ``Zkc.Source.Structured.ProtocolSignature.name)
    (mkApp (mkConst ``Zkc.Source.Structured.NormalForm.CalleeKey.signature) key)
  unless ← isDefEq (name key) (name actual) do return false
  isDefEq (mkApp (mkConst ``Zkc.Source.Structured.NormalForm.CalleeKey.role) key)
    (mkApp (mkConst ``Zkc.Source.Structured.NormalForm.CalleeKey.role) actual)

/-- Once an Entry has an installed family, generation must not reconstruct
its body at a mismatched placement. Exact Entry identity includes its source
template, role, input pattern, pins and transitive earlier library. -/
def hasEntry (entry : Expr) : TacticM Bool := do
  for family in checkedBodies.getState (← getEnv) do
    let saved ← saveState
    let matched ← try
      let (_, _, result) ← forallMetaTelescopeReducing (← inferType (← mkConstWithFreshMVarLevels family))
      let result ← whnf result
      if result.isAppOf ``CheckedBody then
        if ← sameKeyTag result.getAppArgs[1]! entry then
          withTransparency .all <| isDefEq result.getAppArgs[2]! entry
        else pure false
      else pure false
      catch error =>
        if error.isRuntime || error.isInterrupt then throw error
        pure false
    saved.restore
    if matched then return true
  return false

/-- Avoid assembling a dependent application constructor for a target slice
whose instruction schedule cannot match any installed family for this Entry.
Unknown schedules and Entries without an installed family remain candidates.
This filters proposals only; it supplies no evidence or parameter assignments. -/
def compatiblePrefix (entry spine : Expr) : TacticM Bool := do
  let mut found := false
  for family in checkedBodies.getState (← getEnv) do
    let saved ← saveState
    let candidate ← try
      let (_, _, result) ← forallMetaTelescopeReducing (← inferType (← mkConstWithFreshMVarLevels family))
      let result ← whnf result
      if !result.isAppOf ``CheckedBody then pure none
      else if !(← sameKeyTag result.getAppArgs[1]! entry) then pure none
      else if !(← withTransparency .all <| isDefEq result.getAppArgs[2]! entry) then pure none
      else
        let proposed ← whnf (← mkAppM ``Placement.spine #[result.getAppArgs[5]!])
        pure (some (← TargetEquality.compatiblePrefixShape proposed spine))
    catch error =>
      if error.isRuntime || error.isInterrupt then throw error
      -- Inability to inspect a candidate is not evidence of incompatibility.
      pure (some true)
    saved.restore
    match candidate with
    | some true => return true
    | some false => found := true
    | none => pure ()
  return !found

/-- Infer parameters from the actual body goal, then discharge only finite
interface obligations. A candidate cannot ask this search to derive another
alignment. Failure restores all assignments before another candidate is tried.
The family constant remains in the returned term, without unfolding its proof.
-/
def propose (goal : MVarId) (entry placement : Expr) (solve : MVarId → TacticM Unit) :
    TacticM (Option Use) := goal.withContext do
  let expected ← instantiateMVars (← goal.getType)
  let start ← IO.monoNanosNow
  let collecting := (← getOptions).getBool `zkc.connection.collectFamilyPremises false
  for family in checkedBodies.getState (← getEnv) do
    let saved ← saveState
    try
      let constant ← mkConstWithFreshMVarLevels family
      Interface.auditFamilyType (← inferType constant)
      phase s!"family match telescope {family}"
      let (parameters, _, result) ← forallMetaTelescopeReducing (← inferType constant)
      let result ← whnf result
      unless result.isAppOf ``CheckedBody do
        throwError "connection-target-body-family-type"
      unless ← sameKeyTag result.getAppArgs[1]! entry do
        throwError "connection-target-body-source-key"
      -- Alignment indices contain the instantiated form, but two different
      -- declarations can normalize to equal forms. Retain exact source-entry
      -- identity as a separate checked association, before matching the form.
      unless ← withTransparency .all <| isDefEq result.getAppArgs[2]! entry do
        throwError "connection-target-body-source-entry"
      phase "family match entry"
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
        phase s!"family match {field}"
        -- Reduce each projection before comparing it. Congruence on the
        -- unreduced projections can compare their entire dependent callee
        -- keys before reaching the determining placement field.
        let proposed ← whnf (← mkAppM field #[result.getAppArgs[5]!])
        let actual ← whnf (← mkAppM field #[placement])
        let matched ← if field == ``Placement.spine then
          TargetEquality.matchPrefix proposed actual
        else withTransparency .all <| isDefEq proposed actual
        unless matched do
          if field == ``Placement.arguments then
            phase m!"family arguments proposed {proposed} actual {actual}"
          throwError "connection-target-body-placement: {field}"
      unless ← withTransparency .all <| isDefEq (← inferType alignment) expected do
        throwError "connection-target-body-association"
      phase "family match association"
      let mut lastFailure : MessageData := "no determining finite fact"
      let mut equationsOnly := true
      for _ in [:2 * parameters.size + 2] do
        let before ← parameters.filterM fun parameter => return !(← parameter.mvarId!.isAssigned)
        for parameter in before, index in [:before.size] do
          let type ← instantiateMVars (← parameter.mvarId!.getType)
          let operand := if type.isAppOf ``Eq then type.getAppArgs[0]!.getAppFn.constName? else none
          phase s!"family fact {index}/{before.size}: operand={operand}; open={type.hasExprMVar}"
          -- Keep timing traces cheap. Full dependent expressions belong to
          -- the separately enabled diagnostic trace, not every phase sample.
          trace[zkc.connection.placement] "family fact type {type}"
          unless (← Interface.structural type) || (← Interface.finiteData type) do
            throwError "connection-target-body-nonstructural-premise: {type}"
          -- A finite equation can determine data needed by an earlier fact.
          -- Retry only after some parameter was assigned; never enumerate
          -- speculative bodies or invent unresolved data.
          if equationsOnly && !type.isAppOf ``Eq then continue
          -- The audited structural interface also contains Type-valued
          -- routing certificates. Dispatch from that one policy so newly
          -- supported certificate kinds cannot be silently left unsolved.
          if ← Interface.structural type then
            let attempt ← saveState
            try solve parameter.mvarId!
            catch error =>
              if error.isRuntime || error.isInterrupt then throw error
              lastFailure := error.toMessageData
              attempt.restore
        let after ← parameters.filterM fun parameter => return !(← parameter.mvarId!.isAssigned)
        if after.isEmpty then break
        if after.size == before.size && equationsOnly then
          -- Projection equations determine exact locations and history before
          -- any readback search may select an equivalent physical cell.
          equationsOnly := false
          continue
        if after.size < before.size then equationsOnly := true
        if after.size == before.size then
          -- A parent family may abstract the child's finite interface, but
          -- never its alignment. Entry and complete placement have already
          -- matched, and every remaining parameter passed the interface audit.
          if collecting then break
          phase m!"family stalled: {lastFailure}"
          for parameter in after do
            let type ← instantiateMVars (← parameter.mvarId!.getType)
            phase m!"family undetermined {type.getAppFn.constName?} {type}"
          throwError "connection-target-body-undetermined-interface: {lastFailure}"
      let mut arguments ← parameters.mapM instantiateMVars
      if !collecting && (← getOptions).getBool `zkc.connection.cacheInterfaceFacts false then
        for parameter in parameters, index in [:parameters.size] do
          let type ← whnf (← instantiateMVars (← parameter.mvarId!.getType))
          if ← Interface.structural type then
            let name := (← getCurrNamespace) ++ (← mkFreshUserName `checkedConnectionInterface)
            let closed ← Closure.mkValueTypeClosure type arguments[index]! false
            let (type, value) := _root_.ShareCommon.shareCommon' (closed.type, closed.value)
            let declaration ← mkDefinitionValInferringUnsafe name closed.levelParams.toList type value
              (.regular (getMaxHeight (← getEnv) value + 1))
            phase s!"interface kernel start {index} {type.getAppFn.constName?}"
            withExporting <| withOptions (Elab.async.set · false) <|
              addDecl (.defnDecl declaration) (forceExpose := true)
            phase s!"interface kernel done {index}"
            modifyEnv (addNoncomputable · name)
            arguments := arguments.set! index (mkAppN
              (mkConst name (closed.levelParams.toList.map Level.param)) closed.exprArgs)
      let body ← instantiateMVars (mkAppN constant arguments)
      if !collecting && body.hasExprMVar then throwError "connection-target-body-unresolved-placement"
      let alignment ← mkAppM ``CheckedBody.alignment #[body]
      goal.assign alignment
      let elapsed := (← IO.monoNanosNow) - start
      useCosts.modify (·.push ⟨family, elapsed⟩)
      return some ⟨family, body, elapsed⟩
    catch error =>
      if error.isRuntime || error.isInterrupt then throw error
      phase m!"family refused {family}: {error.toMessageData}"
      trace[zkc.connection.placement] "{family}: {error.toMessageData}"
      saved.restore
  return none

end ZkcTools.ConstructionBindings.TargetPlacement
