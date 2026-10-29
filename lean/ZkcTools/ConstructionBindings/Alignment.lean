module

public import Zkc.Construction.ConnectionCertificate
public import Zkc.Construction.ConnectionInstallation
public import ZkcTools.ConstructionBindings.Readback
public meta import Lean.Elab.Tactic

public meta section

register_option zkc.connection.trace : Bool := {
  defValue := false
  descr := "print structural connection proposal phase markers"
}

register_option zkc.connection.traceFile : String := {
  defValue := ""
  descr := "optional destination for structural connection proposal traces"
}

/-! Untrusted proposal for finite alignment derivations. Search reads
explicit source/view syntax and the symbolic frame; every accepted association
is rechecked by the kernel through the core derivation constructors. No simp
database, protocol names, evaluator or semantic proof callbacks are used. -/
set_option autoImplicit false
namespace ZkcTools.ConstructionBindings.Alignment
open Lean Meta Elab Tactic
open Zkc.Source Zkc.Source.Structured Zkc.Construction

def tracePhase (message : String) : TacticM Unit := do
  if (← getOptions).getBool `zkc.connection.trace false then
    let now ← IO.monoMsNow
    let destination := (← getOptions).get `zkc.connection.traceFile ("" : String)
    if destination.isEmpty then logInfo m!"{now} {message}"
    else IO.FS.withFile destination .append fun handle => handle.putStrLn s!"{now} {message}"

private def listEntries (expression : Expr) : MetaM (Array Expr) := do
  let mut entries := #[]
  let mut rest := expression
  repeat
    rest ← whnf rest
    if rest.isAppOf ``List.nil then return entries
    unless rest.isAppOf ``List.cons do throwError "alignment-nonfinite-list"
    entries := entries.push rest.getAppArgs[1]!
    rest := rest.getAppArgs[2]!
  return entries

private def operandTerms (scope layout references : Expr) : MetaM Expr := do
  let frame ← listEntries layout
  let refs ← listEntries references
  let laws ← mkListLit (mkConst ``NormalForm.LawKey) []
  let mut terms := #[]
  for reference in refs do
    let some index ← getNatValue? reference | throwError "alignment-nonstatic-reference"
    let some proposed := frame[index]? | throwError "alignment-reference-out-of-range"
    let cell ← whnf proposed
    if cell.isAppOf ``ConnectionFrame.Cell.guarded then
      terms := terms.push (← mkAppOptM ``NormalForm.Term.bool #[some laws, some scope, some (mkConst ``Bool.true)])
      continue
    unless cell.isAppOf ``ConnectionFrame.Cell.data do throwError "alignment-operand-not-data"
    let component ← whnf cell.getAppArgs.back!
    unless component.isAppOf ``NormalForm.Comp.present do throwError "alignment-operand-not-present"
    terms := terms.push component.getAppArgs.back!
  let mut result ← mkAppOptM ``NormalForm.Terms.nil #[some laws, some scope]
  for term in terms.reverse do
    result ← mkAppM ``NormalForm.Terms.cons #[term, result]
  return result

private def presentTerms (scope components : Expr) : MetaM Expr := do
  let mut terms := #[]
  let mut current := components
  repeat
    current ← whnf current
    if current.isAppOf ``Values.nil then break
    unless current.isAppOf ``Values.cons do throwError "alignment-nonfinite-helper-inputs"
    let parts := current.getAppArgs
    let component ← whnf parts[parts.size - 2]!
    unless component.isAppOf ``NormalForm.Comp.present do
      throwError "alignment-inline-helper-input-not-present"
    terms := terms.push component.getAppArgs.back!
    current := parts.back!
  let laws ← mkListLit (mkConst ``NormalForm.LawKey) []
  let mut result ← mkAppOptM ``NormalForm.Terms.nil #[some laws, some scope]
  for term in terms.reverse do result ← mkAppM ``NormalForm.Terms.cons #[term, result]
  return result

private def tryReflexivity (goals : List MVarId) : TacticM (List MVarId) := do
  for goal in goals do
    unless ← goal.isAssigned do
      let saved ← saveState
      try goal.refl catch _ => saved.restore
  goals.filterM fun goal => do
    if ← goal.isAssigned then return false
    let type ← whnf (← instantiateMVars (← goal.getType))
    -- These shared finite metavariables are determined by the return readback
    -- or physical extent, rather than synthesized as independent proof goals.
    return !(type.isAppOf ``List || type.isAppOf ``Option || type.isConstOf ``Nat)

private def applyRule (goal : MVarId) (rule : Name) : TacticM (List MVarId) := do
  let pending ← goal.apply (← mkConstWithFreshMVarLevels rule)
  tryReflexivity pending

/-- Keep unsolved finite proof fields as goals until their checking equalities
have determined the body form. AppBuilder rejects these intentional holes. -/
private def finiteApplication (name : Name) (supplied : Array (Option Expr)) : MetaM Expr := do
  let constructor ← mkConstWithFreshMVarLevels name
  let mut type ← inferType constructor
  let mut arguments := #[]
  for proposed in supplied, index in [:supplied.size] do
    let .forallE _ domain body _ ← whnf type | throwError "alignment-constructor-arity"
    let argument ← match proposed with
      | some value => pure value
      | none => mkFreshExprMVar domain
    unless ← withTransparency .all <| isDefEq (← inferType argument) domain do
      throwError "alignment-constructor-field-type: {name}, field={index}, expected={domain}, actual={← inferType argument}"
    arguments := arguments.push argument
    type := body.instantiate1 argument
  return mkAppN constructor arguments

private def viewHead (expression : Expr) : MetaM Expr := do
  let mut current := expression
  repeat
    current := (← instantiateMVars current).consumeMData
    while current.isHeadBetaTarget do current := current.headBeta.consumeMData
    if [``Domain.View.sequence, ``Domain.View.calculation, ``Domain.View.receive,
        ``Domain.View.send, ``Domain.View.guard, ``Domain.View.helper, ``Domain.View.loop,
        ``Domain.View.indicesEmpty, ``Domain.View.indicesAppend, ``Domain.View.observe,
        ``Domain.View.challenge, ``Domain.View.localService, ``Domain.View.empty].any current.isAppOf then return current
    let some unfolded ← unfoldDefinition? current | return current
    current := unfolded
  return current

/-- Discover only the finite coordinate-building prefix. Its exact cells and
instruction tree are subsequently checked by CoordinatePrefix. -/
private partial def coordinatePrefix (layout block model : Expr) : MetaM (Expr × Expr × Expr) := do
  let view ← viewHead block
  let layoutType ← whnf (← inferType layout)
  let cellType := layoutType.getAppArgs.back!
  let scope := cellType.getAppArgs.back!
  if view.isAppOf ``Domain.View.sequence then
    let first ← viewHead view.getAppArgs[1]!
    if first.isAppOf ``Domain.View.indicesEmpty then
      let cell ← mkAppM ``ConnectionFrame.Cell.coordinates #[← mkListLit
        (← mkAppOptM ``NormalForm.Term #[some (← mkListLit (mkConst ``NormalForm.LawKey) []),
          some scope, some (mkConst ``Ty.index)]) []]
      let next ← mkAppM ``List.append #[layout, ← mkListLit (← inferType cell) [cell]]
      let (prepared, tail, suffix) ← coordinatePrefix next view.getAppArgs[2]! model
      let certificate ← mkAppOptM ``ConnectionFrame.CoordinatePrefix.indicesEmpty
        #[some scope, some layout, none, none, some tail]
      return (prepared, certificate, suffix)
    if first.isAppOf ``Domain.View.indicesAppend then
      let parts := first.getAppArgs
      let coordinateRef := parts[1]!
      let indexRef := parts[2]!
      let frame ← listEntries layout
      let some coordinate ← getNatValue? (← whnf coordinateRef) | throwError "alignment-prefix-reference"
      let some index ← getNatValue? (← whnf indexRef) | throwError "alignment-prefix-reference"
      let some coordinateCell := frame[coordinate]? | throwError "alignment-prefix-coordinate-range"
      let some indexCell := frame[index]? | throwError "alignment-prefix-index-range"
      let coordinateCell ← whnf coordinateCell
      let indexCell ← whnf indexCell
      unless coordinateCell.isAppOf ``ConnectionFrame.Cell.coordinates && indexCell.isAppOf ``ConnectionFrame.Cell.data do
        throwError "alignment-prefix-cell-kind"
      let component ← whnf indexCell.getAppArgs.back!
      unless component.isAppOf ``NormalForm.Comp.present do throwError "alignment-prefix-index-absent"
      let term := component.getAppArgs.back!
      let terms := coordinateCell.getAppArgs.back!
      let extended ← mkAppM ``List.append #[terms, ← mkListLit (← inferType term) [term]]
      let cell ← mkAppM ``ConnectionFrame.Cell.coordinates #[extended]
      let next ← mkAppM ``List.append #[layout, ← mkListLit (← inferType cell) [cell]]
      let (prepared, tail, suffix) ← coordinatePrefix next view.getAppArgs[2]! model
      let certificate ← mkAppOptM ``ConnectionFrame.CoordinatePrefix.indicesAppend
        #[some scope, some layout, none, none, some terms, some term, some coordinateRef, some indexRef,
          some (← mkEqRefl (← mkAppM ``Option.some #[coordinateCell])),
          some (← mkEqRefl (← mkAppM ``Option.some #[indexCell])), some tail]
      return (prepared, certificate, suffix)
  return (layout, ← mkAppM ``ConnectionFrame.CoordinatePrefix.empty #[layout], view)

/-- Supply the prepared frame before matching an observation rule; higher-order
unification is never asked to invent an instruction schedule. -/
private def preparedAction (goal : MVarId) (rule : Name) (args : Array Expr)
    (model block first : Expr) : TacticM (List MVarId) := do
  let source ← whnf args[13]!
  let sourceParts := source.getAppArgs
  if rule == ``ConnectionCertificate.Alignment.observedSend then
    unless source.isAppOf ``NormalForm.Form.send do throwError "alignment-expected-send"
  else unless source.isAppOf ``NormalForm.Form.receive do throwError "alignment-expected-receive"
  let layout := args[12]!
  let mut initial := layout
  if rule == ``ConnectionCertificate.Alignment.observedReceive then
    initial ← mkAppM ``ConnectionCertificate.receiveLayout #[layout, sourceParts[sourceParts.size - 4]!]
  if rule == ``ConnectionCertificate.Alignment.delivery then
    let ty ← whnf sourceParts[sourceParts.size - 4]!
    unless ty.isAppOf ``Ty.field do throwError "alignment-delivery-nominal-field"
    let suite ← mkAppM ``Context.suite #[← mkAppM ``Original.Routing.context #[args[0]!]]
    initial ← mkAppM ``ConnectionFrame.queryLayout #[layout, ty.getAppArgs.back!, suite]
  let after := if first.isAppOf ``Domain.View.observe then block else block.getAppArgs[2]!
  let (_, certificate, suffix) ← coordinatePrefix initial after model
  unless suffix.isAppOf ``Domain.View.sequence do throwError "alignment-observation-suffix"
  let observation ← viewHead suffix.getAppArgs[1]!
  unless observation.isAppOf ``Domain.View.observe do throwError "alignment-observation-prefix"
  let rest ← mkLambdaFVars #[model] suffix.getAppArgs[2]!
  let observationParts := observation.getAppArgs
  let certificateType ← whnf (← inferType certificate)
  let certificateArgs := certificateType.getAppArgs
  unless certificateArgs.size == 4 do throwError "alignment-prefix-certificate-type: {certificateType}"
  unless observationParts.size > 6 do throwError "alignment-observation-arity: {observation}"
  let mut supplied : Array (Name × Expr) := #[( `prepared, certificateArgs[2]!),
    (`preparation, certificateArgs[3]!), (`preparationProof, certificate), (`rest, rest)]
  if rule == ``ConnectionCertificate.Alignment.delivery then
    supplied := supplied ++ #[(`observeStateRef, observationParts[4]!), (`observePathRef, observationParts[6]!)]
  else
    supplied := supplied ++ #[(`stateRef, observationParts[4]!), (`pathRef, observationParts[6]!),
      (`template, observationParts[3]!)]
    if rule == ``ConnectionCertificate.Alignment.observedSend then
      supplied := supplied.push (`reference, observationParts[5]!)
  let constructor ← mkConstWithFreshMVarLevels rule
  let mut type ← inferType constructor
  let mut fields := #[]
  for index in [:200] do
    let .forallE name domain body _ := type | break
    let value ← if index < 13 then pure args[index]! else
      match supplied.find? (fun item => item.1 == name) with
      | some (_, value) => pure value
      | none => mkFreshExprMVar domain
    unless ← isDefEq (← inferType value) domain do throwError "alignment-observation-field {name}"
    fields := fields.push value
    type := body.instantiate1 value
  tryReflexivity (← goal.apply (mkAppN constructor fields))




private def splitSubject (component : Expr) : MetaM Expr := do
  let component ← whnf component
  let parts := component.getAppArgs
  if component.isAppOf ``NormalForm.Comp.input then
    return ← mkAppM ``NormalForm.Subject.input #[parts.back!]
  if component.isAppOf ``NormalForm.Comp.read then
    return ← mkAppM ``NormalForm.Subject.read #[parts[parts.size - 2]!, parts.back!]
  throwError "alignment-unsupported-split-subject"

private def helperBinding (definitions helper program : Expr) : TacticM Expr := do
  let payload ← mkAppM ``Program.payload #[program]
  let targetDefinitions ← mkAppM ``UnitPayload.definitions #[payload]
  unless ← isDefEq definitions targetDefinitions do throwError "alignment-helper-declaration-mismatch"
  let entries ← listEntries definitions
  for entry in entries, index in [:entries.size] do
    let key ← mkAppM ``CheckedDefinition.helper #[entry]
    if ← isDefEq key helper then
      let bindingType ← mkAppM ``ConnectionHelpers.Binding #[definitions, helper, program]
      let binding ← Term.elabTerm (← `(⟨⟨$(quote index), by decide⟩, rfl, rfl⟩)) bindingType
      Term.synthesizeSyntheticMVarsNoPostponing
      return ← instantiateMVars binding
  throwError "alignment-helper-key-mismatch"

private partial def staticGoal (goal : MVarId) : TacticM Unit := goal.withContext do
  if ← goal.isAssigned then return
  let saved ← saveState
  try
    goal.refl
    return
  catch _ => saved.restore
  let saved ← saveState
  try
    goal.assumption
    return
  catch _ => saved.restore
  let type ← whnf (← instantiateMVars (← goal.getType))
  if type.hasExprMVar && type.isAppOf ``Eq then
    let saved ← saveState
    try
      withTransparency .all goal.refl
      return
    catch _ => saved.restore
  if type.isAppOf ``ConnectionFrame.Readback then
    setGoals [goal]
    evalTactic (← `(tactic| derive_source_readback))
    return
  if type.isAppOf ``ConnectionCertificate.HistoryReadback then
    let args := type.getAppArgs
    let frame ← listEntries args[1]!
    for cell in frame, reference in [:frame.size] do
      let cell ← whnf cell
      if !(cell.isAppOf ``ConnectionFrame.Cell.history) then continue
      let saved ← saveState
      try
        let constructor ← mkAppOptM ``ConnectionCertificate.HistoryReadback.transcript
          #[some args[0]!, some args[1]!, some args[2]!, some (mkNatLit reference)]
        for pending in ← tryReflexivity (← goal.apply constructor) do staticGoal pending
        return
      catch _ => saved.restore
    for pending in ← applyRule goal ``ConnectionCertificate.HistoryReadback.plain do staticGoal pending
    return
  if type.isAppOf ``ConnectionStaticRoutes.Local || type.isAppOf ``ConnectionStaticRoutes.Delivery then
    let rule := if type.isAppOf ``ConnectionStaticRoutes.Local then
      ``ConnectionStaticRoutes.Local.mk else ``ConnectionStaticRoutes.Delivery.mk
    let pending ← applyRule goal rule
    for remaining in pending do staticGoal remaining
    return
  if type.isAppOf ``ConnectionStaticRoutes.LocalMode then
    for rule in [``ConnectionStaticRoutes.LocalMode.producer, ``ConnectionStaticRoutes.LocalMode.validatorHandle,
        ``ConnectionStaticRoutes.LocalMode.validatorService, ``ConnectionStaticRoutes.LocalMode.validatorRoute] do
      let saved ← saveState
      try
        for pending in ← applyRule goal rule do staticGoal pending
        return
      catch _ => saved.restore
  if type.isAppOf ``ConnectionFrame.IndexReadback then
    let args := type.getAppArgs
    let terms ← listEntries args[2]!
    if terms.isEmpty then
      let [] ← applyRule goal ``ConnectionFrame.IndexReadback.nil | throwError "alignment-coordinate-count"
      return
    let frame ← listEntries args[1]!
    for cell in frame, reference in [:frame.size] do
      let cell ← whnf cell
      if !(cell.isAppOf ``ConnectionFrame.Cell.data) then continue
      let component ← whnf cell.getAppArgs.back!
      if !(component.isAppOf ``NormalForm.Comp.present) then continue
      let saved ← saveState
      try
        unless ← isDefEq component.getAppArgs.back! terms[0]! do throwError "coordinate-term"
        let constructor ← mkAppOptM ``ConnectionFrame.IndexReadback.cons
          #[some args[0]!, some args[1]!, none, none, some terms[0]!, some (mkNatLit reference)]
        for pending in ← tryReflexivity (← goal.apply constructor) do staticGoal pending
        return
      catch _ => saved.restore
    throwError "alignment-coordinate-order-or-binder"
  unless ← isProp type do
    if type.isAppOf ``List || type.isAppOf ``Option || type.isConstOf ``Nat then return
    throwError "alignment-unresolved-static-data: {type}"
  setGoals [goal]
  evalTactic (← `(tactic| decide +kernel))

private partial def deriveExtent (goal : MVarId) : TacticM Unit := goal.withContext do
  let expected ← whnf (← instantiateMVars (← goal.getType))
  let args := expected.getAppArgs
  let input := args[0]!
  let output := args[1]!
  let target := args[2]!
  withLocalDeclD `extentModel (mkConst ``DomainModel) fun model => do
    let view ← viewHead (mkApp target model)
    if view.isAppOf ``Domain.View.empty then
      for pending in ← applyRule goal ``ConnectionTargetExtent.Extent.empty do staticGoal pending
      return
    let parts := view.getAppArgs
    if view.isAppOf ``Domain.View.sequence then
      let first ← mkLambdaFVars #[model] parts[1]!
      let rest ← mkLambdaFVars #[model] parts[2]!
      let constructor ← finiteApplication ``ConnectionTargetExtent.Extent.sequence
        #[some input, none, some output, some first, some rest]
      let pending ← tryReflexivity (← goal.apply constructor)
      for next in pending do
        let nextType ← whnf (← instantiateMVars (← next.getType))
        if nextType.isAppOf ``ConnectionTargetExtent.Extent then deriveExtent next
      for next in pending do unless ← next.isAssigned do staticGoal next
      return
    let rules := [( ``Domain.View.receive, ``ConnectionTargetExtent.Extent.receive),
      (``Domain.View.send, ``ConnectionTargetExtent.Extent.send),
      (``Domain.View.indicesEmpty, ``ConnectionTargetExtent.Extent.indicesEmpty),
      (``Domain.View.indicesAppend, ``ConnectionTargetExtent.Extent.indicesAppend),
      (``Domain.View.observe, ``ConnectionTargetExtent.Extent.observe),
      (``Domain.View.challenge, ``ConnectionTargetExtent.Extent.challenge),
      (``Domain.View.localService, ``ConnectionTargetExtent.Extent.localService),
      (``Domain.View.calculation, ``ConnectionTargetExtent.Extent.calculation),
      (``Domain.View.helper, ``ConnectionTargetExtent.Extent.helper),
      (``Domain.View.guard, ``ConnectionTargetExtent.Extent.guard),
      (``Domain.View.loop, ``ConnectionTargetExtent.Extent.loop)]
    for (viewName, rule) in rules do
      unless view.isAppOf viewName do continue
      let mut fields := #[some input] ++ (parts.extract 1 parts.size).map some
      if viewName == ``Domain.View.loop then
        fields := fields.set! (fields.size - 1) (some (← mkLambdaFVars #[model] parts.back!))
      let constructor ← mkAppOptM rule fields
      for pending in ← tryReflexivity (← goal.apply constructor) do staticGoal pending
      return
    throwError "alignment-unsupported-target-extent: target={target}, view={view}, type={← inferType view}"

structure PlacementCost where
  name : Name
  proposalNanos : Nat
  kernelNanos : Nat
  deriving Inhabited, Repr

initialize placementCosts : IO.Ref (Array PlacementCost) ← IO.mkRef #[]

initialize checkedAlignments : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun imported => imported.foldl (· ++ ·) #[]
  }

/-- Close an exact retained placement behind a checked declaration. This is
an exact-placement boundary: it does not assert relocation invariance. -/
private def checkedBody (goal : MVarId) (build : MVarId → TacticM Unit) : TacticM Unit :=
  goal.withContext do
    let expected ← instantiateMVars (← goal.getType)
    for name in checkedAlignments.getState (← getEnv) do
      unless (← getEnv).contains name do continue
      let candidate := mkConst name
      let type ← inferType candidate
      if type.isForall then continue
      let saved ← saveState
      if ← isDefEq type expected then
        goal.assign candidate
        return
      saved.restore
    let start ← IO.monoNanosNow
    let body ← mkFreshExprSyntheticOpaqueMVar expected
    build body.mvarId!
    Term.synthesizeSyntheticMVarsNoPostponing
    let value ← instantiateMVars body
    if value.hasExprMVar then throwError "alignment-body-unresolved-finite-data"
    -- Direct auxiliary declarations bypass Lean's predefinition pipeline.
    -- Use its same hash-consing boundary before closing and checking the term;
    -- this changes object sharing only, never the certificate or its type.
    let value := _root_.ShareCommon.shareCommon' value
    let name ← mkAuxDeclName `retainedConnectionAlignment
    -- Finish closure before timing the synchronous declaration check. Only
    -- used local variables are abstracted; the enclosing root is not captured.
    let closed ← Closure.mkValueTypeClosure (← inferType value).headBeta value false
    let (closedType, closedValue) := _root_.ShareCommon.shareCommon' (closed.type, closed.value)
    let hints := ReducibilityHints.regular (getMaxHeight (← getEnv) closedValue + 1)
    let declaration ← mkDefinitionValInferringUnsafe name closed.levelParams.toList
      closedType closedValue hints
    let proposed ← IO.monoNanosNow
    withOptions (Elab.async.set · false) <| addDecl (.defnDecl declaration)
    let checked ← IO.monoNanosNow
    modifyEnv fun environment => addNoncomputable (checkedAlignments.addEntry environment name) name
    placementCosts.modify (·.push ⟨name, proposed - start, checked - proposed⟩)
    tracePhase s!"checked body {name}: proposal_ns={proposed-start}; kernel_ns={checked-proposed}"
    let reference := mkAppN (mkConst name closed.levelArgs.toList) closed.exprArgs
    goal.assign reference

/-- A proposal-local cache of closed syntax reductions. Backtracking across
candidate target cuts does not change these finite source/layout expressions.
It contains no evidence and is discarded after one root proposal. -/
private abbrev SyntaxCache := IO.Ref (Std.HashMap Expr Expr)

private def reducedSyntax (cache : SyntaxCache) (expression : Expr) : MetaM Expr := do
  let expression ← instantiateMVars expression
  let closed := !expression.hasMVar && !expression.hasFVar
  if closed then
    if let some result := (← cache.get)[expression]? then return result
  let result ← withTransparency .all <| reduce expression true true true
  if closed then cache.modify (·.insert expression result)
  return result

private structure CutDiscovery where
  suffixes : Array Expr
  found : IO.Ref (Option Nat)

initialize discoveredCutException : InternalExceptionId ←
  registerInternalExceptionId `ZkcTools.ConstructionBindings.discoveredCut

/-- Discover a caller suffix by the existing full-return readback, without
installing a new trusted rule. The final selected prefix is checked again by
`Alignment.application`, including its extent, output row and continuation. -/
private def discoverReturn (discovery : CutDiscovery) (expected : Expr) : TacticM Unit := do
  let args := expected.getAppArgs
  let target := args[14]!
  withLocalDeclD `discoveryModel (mkConst ``DomainModel) fun model => do
    let view ← viewHead (mkApp target model)
    if view.isAppOf ``Domain.View.empty then return
    let mut selected : Option Nat := none
    for suffix in discovery.suffixes, index in [:discovery.suffixes.size] do
      let candidate ← viewHead (mkApp suffix model)
      if ← isDefEq view candidate then
        selected := some index
        break
    let some index := selected | return
    let saved ← saveState
    let matched ← try
      let carriers ← mkAppM ``FieldModel.toCarriers #[← mkAppM ``DomainModel.toFieldModel #[model]]
      let empty ← mkLambdaFVars #[model] (← mkAppOptM ``Domain.View.empty #[some carriers])
      let trial ← mkFreshExprSyntheticOpaqueMVar
        (mkAppN expected.getAppFn (args.set! 14 empty))
      let [readback, historyRead] ← tryReflexivity
          (← trial.mvarId!.apply (← mkConstWithFreshMVarLevels ``ConnectionCertificate.Alignment.done))
        | throwError "alignment-discovery-return-shape"
      setGoals [readback]
      evalTactic (← `(tactic| derive_source_readback))
      staticGoal historyRead
      pure true
    catch _ => pure false
    saved.restore
    if matched then
      discovery.found.set (some index)
      throw (.internal discoveredCutException)

private partial def derive (cache : SyntaxCache) (discovery : Option CutDiscovery) (goal : MVarId) : TacticM Unit := goal.withContext <| withTransparency .all <|
    Term.withoutErrToSorry <| withoutRecover do
  let expected ← whnf (← instantiateMVars (← goal.getType))
  if expected.isAppOf ``ConnectionCertificate.Certificate then
    tracePhase "certificate constructor"
    -- The root already fixes every certificate index. Supplying them before
    -- applying the constructor avoids rediscovering the admitted source and
    -- library by unification at each root.
    let constructor ← mkConstWithFreshMVarLevels ``ConnectionCertificate.Certificate.mk
    let pending ← goal.apply (mkAppN constructor expected.getAppArgs)
    tracePhase "certificate fields"
    let [alignment] ← tryReflexivity pending
      | throwError "alignment-normalization-failed"
    tracePhase "certificate normalized"
    derive cache discovery alignment
    return
  unless expected.isAppOf ``ConnectionCertificate.Alignment do
    throwError "alignment-expected-derivation"
  let mut args := expected.getAppArgs
  let sourceSyntax ← reducedSyntax cache args[13]!
  let frameSyntax ← reducedSyntax cache args[12]!
  args := (args.set! 13 sourceSyntax).set! 12 frameSyntax
  goal.setType (mkAppN expected.getAppFn args)
  let scope := args[10]!
  let layout := args[12]!
  tracePhase "before source"
  let source ← whnf args[13]!
  tracePhase s!"source {source.getAppFn.constName?}"
  let target := args[14]!
  if source.isAppOf ``NormalForm.Form.apply then
    let selection ← whnf args[4]!
    unless selection.isAppOf ``ConnectionLibrary.Selection.selected do
      throwError "alignment-unsupported-callee"
    let selected := selection.getAppArgs
    let payload := selected[selected.size - 3]!
    let same := selected[selected.size - 2]!
    let library := selected.back!
    let parts := source.getAppArgs
    let calleeType ← inferType parts[parts.size - 6]!
    let position ← whnf (← mkAppM ``Fin.val #[parts[parts.size - 6]!])
    let some position ← getNatValue? position | throwError "alignment-nonfinite-callee"
    let callee ← Term.elabTerm (← `(⟨$(quote position), by decide +kernel⟩)) (some calleeType)
    Term.synthesizeSyntheticMVarsNoPostponing
    let signature := parts[parts.size - 5]!
    let roles := parts[parts.size - 4]!
    let site := parts[parts.size - 3]!
    let arguments := parts[parts.size - 2]!
    let next := parts.back!
    let slices ← withLocalDeclD `sliceModel (mkConst ``DomainModel) fun model => do
      let mut current ← viewHead (mkApp target model)
      let mut views : Array Expr := #[]
      let mut result : Array (Expr × Expr) := #[]
      repeat
        let mut spine := mkConst ``ConnectionTargetPrefix.Prefix.empty
        for view in views.reverse do spine ← mkAppM ``ConnectionTargetPrefix.Prefix.step #[view, spine]
        result := result.push (spine, ← mkLambdaFVars #[model] current)
        unless current.isAppOf ``Domain.View.sequence do break
        views := views.push (← mkLambdaFVars #[model] current.getAppArgs[1]!)
        current ← viewHead current.getAppArgs[2]!
      return result
    let search : CutDiscovery := ⟨slices.map Prod.snd, ← IO.mkRef none⟩
    let mut candidates := if slices.isEmpty then [] else
      (slices.size - 1) :: (List.range (slices.size - 1))
    let mut visited : List Nat := []
    let mut failure : MessageData := "no finite target slice"
    while !candidates.isEmpty do
      let index := candidates.head!
      candidates := candidates.tail!
      if visited.contains index then continue
      visited := index :: visited
      let (spine, rest) := slices[index]!
      search.found.set none
      tracePhase s!"application slice {index}/{slices.size}"

      let saved ← saveState
      try
        let supplied := [( `payload, payload), (`same, same), (`library, library), (`callee, callee),
          (`signature, signature), (`roles, roles), (`site, site), (`arguments, arguments),
          (`spine, spine), (`next, next), (`rest, rest)]
        let constructor ← mkConstWithFreshMVarLevels ``ConnectionCertificate.Alignment.application
        let mut type ← inferType constructor
        let mut fields := #[]
        for index in [:100] do
          let .forallE name domain body _ := type | break
          let value ← if index < 4 then pure args[index]!
            else if index < 12 then pure args[index + 1]! else
            match supplied.find? (fun item => item.1 == name) with
            | some (_, value) => pure value
            | none => mkFreshExprMVar domain
          unless ← withTransparency .all <| isDefEq (← inferType value) domain do
            let actual ← inferType value
            let wanted ← whnf domain.getAppArgs.back!
            let got ← whnf actual.getAppArgs.back!
            throwError "alignment-application-field {name}: wanted={wanted}, got={got}"
          fields := fields.push value
          type := body.instantiate1 value
        tracePhase "application assemble"
        let pending ← goal.apply (mkAppN constructor fields) {newGoals := .all}
        tracePhase "application assembled"
        let mut alignments := []
        let mut statics := []
        for pending in pending do
          let pendingType ← whnf (← instantiateMVars (← pending.getType))
          if pendingType.isAppOf ``ConnectionTargetExtent.Extent then
            tracePhase "application extent"
            deriveExtent pending
            tracePhase "application extent complete"
          else if pendingType.isAppOf ``ConnectionCertificate.Alignment then alignments := alignments ++ [pending]
          else statics := statics ++ [pending]
        match alignments with
        | body :: tails =>
          checkedBody body (derive cache (some search))
          for alignment in tails do derive cache discovery alignment
        | [] => throwError "alignment-application-body-missing"
        for pending in statics do unless ← pending.isAssigned do staticGoal pending
        return
      catch error =>
        saved.restore
        if let .internal id _ := error then
          if id == discoveredCutException then
            if let some cut ← search.found.get then
              tracePhase s!"application discovered prefix {cut}"
              candidates := cut :: candidates
              continue
            throw error
        failure := error.toMessageData
        tracePhase s!"slice failed: {← failure.toString}"
    throwError "alignment-callee-slice-refused: {failure}"
  if source.isAppOf ``NormalForm.Form.split then
    let parts := source.getAppArgs
    let component ← whnf parts[parts.size - 3]!
    if component.isAppOf ``NormalForm.Comp.absent || component.isAppOf ``NormalForm.Comp.present then
      let pending ← applyRule goal (if component.isAppOf ``NormalForm.Comp.absent then
        ``ConnectionCertificate.Alignment.splitAbsent else ``ConnectionCertificate.Alignment.splitValue)
      for remaining in pending do
        if (← whnf (← instantiateMVars (← remaining.getType))).isAppOf ``ConnectionCertificate.Alignment then derive cache discovery remaining
        else staticGoal remaining
      return
    let subject ← splitSubject component
    let frame ← listEntries layout
    for cell in frame, index in [:frame.size] do
      let cell ← whnf cell
      if cell.isAppOf ``ConnectionFrame.Cell.data && (← isDefEq cell.getAppArgs.back! component) then
        let constructor ← mkAppOptM ``ConnectionCertificate.Alignment.splitPresent
          ((args.extract 0 13).map some ++ #[none, some subject, some parts[parts.size - 2]!, some parts.back!, some target, some (mkNatLit index)])
        let [tail] ← tryReflexivity (← goal.apply constructor)
          | throwError "alignment-presence-static-mismatch"
        derive cache discovery tail
        return
    let constructor ← mkAppOptM ``ConnectionCertificate.Alignment.split
      ((args.extract 0 13).map some ++ #[none, some subject, some parts[parts.size - 2]!, some parts.back!, some target])
    let [absent, present] ← goal.apply constructor | throwError "alignment-split-shape"
    derive cache discovery absent
    derive cache discovery present
    return
  if source.isAppOf ``NormalForm.Form.math then
    let sourceParts := source.getAppArgs
    let helper := sourceParts[sourceParts.size - 3]!
    let retained ← withLocalDeclD `projectionModel (mkConst ``DomainModel) fun model => do
      let block ← viewHead (mkApp target model)
      if block.isAppOf ``Domain.View.sequence then
        let first ← viewHead block.getAppArgs[1]!
        if first.isAppOf ``Domain.View.helper then
          return ← isDefEq first.getAppArgs[2]! (← mkAppM ``Helper.name #[helper])
      return false
    unless retained do
      let entries ← listEntries args[2]!
      for entry in entries, index in [:entries.size] do
        if ← isDefEq (← mkAppM ``CheckedDefinition.helper #[entry]) helper then
          let body ← whnf (← mkAppM ``CheckedDefinition.body #[entry])
          let before ← mkAppM ``List.take #[mkNatLit index, args[2]!]
          let after ← mkAppM ``List.drop #[mkNatLit (index + 1), args[2]!]
          let definitionsSyntax ← Term.exprToSyntax args[2]!
          let selected ← Term.elabTerm
            (← `(($definitionsSyntax).get ⟨$(quote index), by decide +kernel⟩)) (mkConst ``CheckedDefinition)
          let beforeSyntax ← Term.exprToSyntax before
          let afterSyntax ← Term.exprToSyntax after
          let (rule, certificate, suppliedArguments, extra) ← if body.isAppOf ``Region.ret then do
              let projectionType ← mkAppM ``ConnectionHelpers.Projection #[args[2]!, selected]
              let positionsSyntax ← Term.exprToSyntax body.getAppArgs.back!
              let projection ← Term.elabTerm
                (← `(⟨$beforeSyntax, $afterSyntax, rfl, by decide +kernel, $positionsSyntax, rfl⟩)) projectionType
              pure (``ConnectionCertificate.Alignment.projectionHelper, projection, sourceParts[sourceParts.size - 2]!, #[])
            else do
              unless body.isAppOf ``Region.letOp do break
              let bodyParts := body.getAppArgs
              let returned ← whnf bodyParts.back!
              unless returned.isAppOf ``Region.ret do break
              let operation ← whnf (← mkAppM ``Calculation.ofOp? #[bodyParts[bodyParts.size - 4]!])
              unless operation.isAppOf ``Option.some do break
              let operation := operation.getAppArgs.back!
              let operationSyntax ← Term.exprToSyntax operation
              let inputsSyntax ← Term.exprToSyntax bodyParts[bodyParts.size - 3]!
              let outputsSyntax ← Term.exprToSyntax returned.getAppArgs.back!
              let certificateType ← mkAppM ``ConnectionHelpers.CalculationBody #[args[2]!, selected]
              let certificate ← Term.elabTerm
                (← `(⟨$beforeSyntax, $afterSyntax, rfl, by decide +kernel,
                  $operationSyntax, by decide +kernel, $inputsSyntax, $outputsSyntax, rfl⟩)) certificateType
              let arguments := sourceParts[sourceParts.size - 2]!
              let selected ← mkAppM ``NormalForm.lookup #[arguments, bodyParts[bodyParts.size - 3]!]
              let absent ← whnf (← mkAppM ``NormalForm.anyAbsent #[selected])
              if absent.isConstOf ``Bool.true then
                pure (``ConnectionCertificate.Alignment.inlineMissingCalculation, certificate,
                  arguments, #[← mkEqRefl (mkConst ``Bool.true)])
              else
                pure (``ConnectionCertificate.Alignment.inlineCalculation, certificate,
                  ← presentTerms scope arguments, #[])
          Term.synthesizeSyntheticMVarsNoPostponing
          let constructor ← mkAppOptM rule
            ((args.extract 0 13).map some ++ #[some selected, some certificate,
              some suppliedArguments] ++ extra.map some ++ #[some sourceParts.back!, some target])
          let mut tails := []
          for pending in ← goal.apply constructor do
            if (← whnf (← instantiateMVars (← pending.getType))).isAppOf ``ConnectionCertificate.Alignment then
              tails := tails ++ [pending]
            else staticGoal pending
          for tail in tails do derive cache discovery tail
          return
  if source.isAppOf ``NormalForm.Form.done then
    if let some search := discovery then discoverReturn search (← instantiateMVars (← goal.getType))
  let saved ← saveState
  let mut returnFailure : MessageData := "not a return"
  try
    let [readback, historyRead] ← tryReflexivity (← goal.apply (← mkConstWithFreshMVarLevels ``ConnectionCertificate.Alignment.done))
      | throwError "alignment-not-return"
    setGoals [readback]
    evalTactic (← `(tactic| derive_source_readback))
    staticGoal historyRead
    return
  catch exception =>
    returnFailure := exception.toMessageData
    saved.restore
  let saved ← saveState
  try
    let pending ← applyRule goal ``ConnectionCertificate.Alignment.halt
    unless pending.isEmpty do throwError "alignment-not-stop"
    return
  catch _ => saved.restore
  withLocalDeclD `model (mkConst ``DomainModel) fun model => do
    let block ← viewHead (mkApp target model)
    unless block.isAppOf ``Domain.View.sequence do
      if source.isAppOf ``NormalForm.Form.done then
        throwError "alignment-return-or-view-mismatch: {returnFailure}"
      if source.isAppOf ``NormalForm.Form.compute then throwError "alignment-compute-view-mismatch"
      if source.isAppOf ``NormalForm.Form.math then throwError "alignment-helper-view-mismatch"
      if source.isAppOf ``NormalForm.Form.repeat then throwError "alignment-loop-view-mismatch"
      throwError "alignment-return-or-view-mismatch: source={source.getAppFn}, view={block.getAppFn}"
    let first ← viewHead block.getAppArgs[1]!
    if first.isAppOf ``Domain.View.calculation then
      let parts := first.getAppArgs
      let operation := parts[1]!
      let references := parts[2]!
      let computing := source.isAppOf ``NormalForm.Form.compute
      let sourceParts := source.getAppArgs
      let sameOperation ← if computing then
          isDefEq (← mkAppM ``Calculation.op #[operation]) sourceParts[sourceParts.size - 4]!
        else pure false
      if computing && sameOperation then
        let terms := sourceParts[sourceParts.size - 2]!
        let yes ← mkEqRefl (mkConst ``Bool.true)
        let rest ← mkLambdaFVars #[model] block.getAppArgs[2]!
        let pending ← try
          let constructor ← mkAppOptM ``ConnectionCertificate.Alignment.compute
            ((args.extract 0 13).map some ++
              #[some operation, some terms, some sourceParts.back!, some rest, some references, some yes, some yes])
          goal.apply constructor
          catch _ => throwError "alignment-compute-operation-or-view-mismatch"
        let [readback, tail] ← tryReflexivity pending | throwError "alignment-compute-shape"
        setGoals [readback]
        evalTactic (← `(tactic| derive_source_readback))
        derive cache discovery tail
        return
      -- Normalization removes total source instructions before a compute node.
      -- Retain their real target checkpoints and extend the symbolic frame
      -- before proposing the partial step; never treat that step as total.
      let pending ← try
        let terms ← operandTerms scope layout references
        let yes ← mkEqRefl (mkConst ``Bool.true)
        let supplied := (args.extract 0 14).map some ++
          #[some operation, some yes, some terms, some references, some yes, some yes]
        let constructor ← mkAppOptM ``ConnectionCertificate.Alignment.calculation supplied
        goal.apply constructor
      catch exception =>
        if computing then throwError "alignment-compute-operation-or-view-mismatch"
        else throw exception
      let [readback, tail] ← tryReflexivity pending
        | throwError "alignment-calculation-shape"
      setGoals [readback]
      evalTactic (← `(tactic| derive_source_readback))
      derive cache discovery tail
      return
    if [``Domain.View.receive, ``Domain.View.send, ``Domain.View.observe, ``Domain.View.challenge,
        ``Domain.View.localService, ``Domain.View.indicesEmpty, ``Domain.View.indicesAppend].any first.isAppOf then
      let rules := if first.isAppOf ``Domain.View.receive then
          [``ConnectionCertificate.Alignment.receive, ``ConnectionCertificate.Alignment.observedReceive]
        else if first.isAppOf ``Domain.View.send then
          [``ConnectionCertificate.Alignment.send, ``ConnectionCertificate.Alignment.observedSend]
        else if first.isAppOf ``Domain.View.observe then [``ConnectionCertificate.Alignment.observedSend]
        else if first.isAppOf ``Domain.View.challenge then
          [``ConnectionCertificate.Alignment.publicQuery, ``ConnectionCertificate.Alignment.delivery]
        else if first.isAppOf ``Domain.View.localService then [``ConnectionCertificate.Alignment.localQuery]
        else if first.isAppOf ``Domain.View.indicesEmpty then [``ConnectionCertificate.Alignment.indicesEmpty]
        else [``ConnectionCertificate.Alignment.indicesAppend]
      let mut selected : Option (List MVarId) := none
      let mut failure : MessageData := "no applicable action rule"
      for rule in rules do
        let saved ← saveState
        try
          let pending ← if [``ConnectionCertificate.Alignment.observedSend,
              ``ConnectionCertificate.Alignment.observedReceive, ``ConnectionCertificate.Alignment.delivery].contains rule then
              preparedAction goal rule args model block first
            else applyRule goal rule
          let mut tails := []
          for remaining in pending do
            let type ← instantiateMVars (← remaining.getType)
            if type.isAppOf ``ConnectionCertificate.Alignment then tails := tails ++ [remaining]
            else staticGoal remaining
          selected := some tails
          break
        catch exception =>
          failure := m!"{failure}\n{rule}: {exception.toMessageData}"
          saved.restore
      let some tails := selected
        | throwError "alignment-route-request-history-coordinate-or-operand-mismatch: {failure}"
      -- Once finite indices and readbacks select the rule, continuation failure
      -- belongs to that suffix. Do not retry other actions or hide its location.
      for tail in tails do derive cache discovery tail
      return
    if first.isAppOf ``Domain.View.guard then
      let mut selected : Option (List MVarId) := none
      for rule in [``ConnectionCertificate.Alignment.guard,
          ``ConnectionCertificate.Alignment.trueGuard, ``ConnectionCertificate.Alignment.falseGuard] do
        let saved ← saveState
        try
          let pending ← applyRule goal rule
          let mut tails := []
          for pendingGoal in pending do
            let type ← instantiateMVars (← pendingGoal.getType)
            if type.isAppOf ``ConnectionCertificate.GuardReadback then
              let saved ← saveState
              try
                for checked in ← applyRule pendingGoal ``ConnectionCertificate.GuardReadback.comparison do
                  staticGoal checked
              catch _ =>
                saved.restore
                for checked in ← applyRule pendingGoal ``ConnectionCertificate.GuardReadback.boolean do
                  staticGoal checked
            else if type.isAppOf ``ConnectionCertificate.Alignment then
              tails := pendingGoal :: tails
            else staticGoal pendingGoal
          selected := some tails
          break
        catch _ => saved.restore
      let some tails := selected | throwError "alignment-guard-mismatch"
      for tail in tails do derive cache discovery tail
      return
    if first.isAppOf ``Domain.View.helper then
      unless source.isAppOf ``NormalForm.Form.math || source.isAppOf ``NormalForm.Form.strict ||
          source.isAppOf ``NormalForm.Form.owned do
        throwError "alignment-helper-source-mismatch"
      let sourceParts := source.getAppArgs
      let helper := sourceParts[sourceParts.size - 3]!
      let arguments := sourceParts[sourceParts.size - 2]!
      let parts := first.getAppArgs
      let program := parts[1]!
      let references := parts[3]!
      let binding ← helperBinding args[2]! helper program
      let math ← mkEqRefl (mkConst ``HelperKind.math)
      let yes ← mkEqRefl (mkConst ``Bool.true)
      let rest ← mkLambdaFVars #[model] block.getAppArgs[2]!
      let strict := source.isAppOf ``NormalForm.Form.strict
      let owned := source.isAppOf ``NormalForm.Form.owned
      let rule := if strict then ``ConnectionCertificate.Alignment.strictHelper
        else if owned then ``ConnectionCertificate.Alignment.ownedHelper
        else ``ConnectionCertificate.Alignment.mathHelper
      let fields := (if owned then #[some sourceParts[sourceParts.size - 4]!] else #[]) ++
        #[some program, some helper] ++ (if strict || owned then #[] else #[some math])
      let constructor ← mkAppOptM rule
        ((args.extract 0 13).map some ++ fields ++ #[some binding,
          some arguments, some sourceParts.back!, some rest, some references, some yes, some yes])
      let pending ← try goal.apply constructor
        catch exception => throwError "alignment-helper-static-mismatch: {exception.toMessageData}"
      let pending ← tryReflexivity pending
      let [readback, tail] := pending | throwError "alignment-helper-static-mismatch: remaining={pending.length}"
      setGoals [readback]
      try evalTactic (← `(tactic| derive_source_readback))
      catch _ => throwError "alignment-helper-operand-readback-mismatch-or-optional"
      derive cache discovery tail
      return
    if first.isAppOf ``Domain.View.loop then
      unless source.isAppOf ``NormalForm.Form.repeat do throwError "alignment-loop-source-mismatch"
      let parts := source.getAppArgs
      let spec := parts[parts.size - 7]!
      let site := parts[parts.size - 6]!
      let callback := parts[parts.size - 5]!
      let count ← whnf parts[parts.size - 4]!
      unless count.isAppOf ``NormalForm.Comp.present do throwError "alignment-loop-count-not-present"
      let context ← mkAppM ``Original.Routing.context #[args[0]!]
      let profile ← whnf (← mkAppM ``Context.profile #[context])
      let fiatShamir := profile.isAppOf ``Profile.fiatShamir
      unless fiatShamir || profile.isAppOf ``Profile.plain do throwError "alignment-loop-profile-not-static"
      let viewParts := first.getAppArgs
      let yielded := viewParts[2]!
      let initial := viewParts[4]!
      let splitProfile (references : Expr) : MetaM (Expr × Expr) := do
        let entries ← listEntries references
        if fiatShamir then
          if entries.isEmpty then throwError "alignment-loop-history-missing"
          return (← mkListLit (mkConst ``Nat) entries.toList.dropLast,
            ← mkAppM ``Option.some #[entries.back!])
        return (references, ← mkAppOptM ``Option.none #[some (mkConst ``Nat)])
      let (stateReferences, initialHistory) ← splitProfile initial
      let (yieldData, bodyHistory) ← splitProfile yielded
      let roster ← mkAppM ``List.length #[← mkAppM ``ContextIdentity.roles #[← mkAppM ``Context.toContextIdentity #[context]]]
      let distinct ← mkAppM ``ConnectionFrame.rosterCheck_sound #[args[1]!, args[6]!, roster,
        ← mkEqRefl (mkConst ``Bool.true)]
      let body ← mkLambdaFVars #[model] viewParts[6]!
      let rest ← mkLambdaFVars #[model] block.getAppArgs[2]!
      let visible ← whnf (← mkAppM ``ConnectionFrame.visibleState
        #[args[6]!, ← mkAppM ``RepeatSpec.stateScopes #[spec], ← mkAppM ``RepeatSpec.state #[spec]])
      let constructor ← if visible.isConstOf ``Bool.true then
        finiteApplication ``ConnectionCertificate.Alignment.repeat
          ((args.extract 0 13).map some ++ #[some spec, some site, some callback, some count.getAppArgs.back!,
            some parts[parts.size - 3]!, some parts[parts.size - 2]!, some parts.back!, some body, some rest,
            some roster, some distinct, none, none, none, some viewParts[3]!, none,
            some stateReferences, some initial, some yieldData, some yielded, some initialHistory, some bodyHistory])
      else do
        let scopes ← mkAppM ``RepeatSpec.stateScopes #[spec]
        let initialLocations ← whnf (← mkAppM ``ConnectionInstallation.returnLocations #[args[6]!, scopes, stateReferences])
        let yieldLocations ← whnf (← mkAppM ``ConnectionInstallation.returnLocations #[args[6]!, scopes, yieldData])
        unless initialLocations.isAppOf ``Option.some && yieldLocations.isAppOf ``Option.some do
          throwError "alignment-loop-projected-location-arity"
        let mappedRole ← mkAppM ``ProtocolContext.roles #[args[1]!, args[6]!]
        let mappedScopes ← mkAppM ``ProtocolContext.mapScopes #[args[1]!, scopes]
        let schema ← whnf (← mkAppM ``Original.roleOutputSorts
          #[mappedRole, mappedScopes, ← mkAppM ``RepeatSpec.state #[spec]])
        unless schema.isAppOf ``Option.some do throwError "alignment-loop-projected-schema"
        finiteApplication ``ConnectionCertificate.Alignment.projectedRepeat
          ((args.extract 0 13).map some ++ #[some spec, some site, some callback, some count.getAppArgs.back!,
            some parts[parts.size - 3]!, some parts[parts.size - 2]!, some parts.back!, some body, some rest,
            some roster, some distinct, none, none, some schema.getAppArgs.back!, none, some viewParts[3]!, none,
            some initialLocations.getAppArgs.back!, some yieldLocations.getAppArgs.back!,
            some stateReferences, some initial, some yieldData, some yielded, some initialHistory, some bodyHistory])
      let pending ← try goal.apply constructor catch _ => throwError "alignment-loop-bound-schema-or-layout-mismatch"
      let pending ← tryReflexivity pending
      let mut tails := []
      for remaining in pending do
        if ← remaining.isAssigned then continue
        let type ← instantiateMVars (← remaining.getType)
        if type.isAppOf ``ConnectionCertificate.Alignment then tails := tails ++ [remaining]
        else if type.isAppOf ``ConnectionFrame.Readback then
          setGoals [remaining]
          try evalTactic (← `(tactic| derive_source_readback))
          catch _ => throwError "alignment-loop-state-readback-mismatch"
        else
          try staticGoal remaining
          catch _ => throwError "alignment-loop-count-scope-profile-or-return-mismatch"
      for tail in tails do derive cache discovery tail
      return
    throwError "alignment-unsupported-target"

/-- Propose a source Certificate, or a finite Derivation for a fixed normal
form. This is not an executable verified checker: failure diagnostics and
search are untrusted; successful output is data checked by the Lean kernel. -/
elab "derive_connection_alignment" : tactic => withMainContext do
  let goal ← getMainGoal
  let pending := (← getGoals).tail
  let cache ← IO.mkRef ({} : Std.HashMap Expr Expr)
  derive cache none goal
  let result ← instantiateMVars (mkMVar goal)
  if result.hasExprMVar then throwError "alignment-unresolved-finite-admission"
  setGoals pending

end ZkcTools.ConstructionBindings.Alignment
