module

public import Zkc.Construction.ConnectionCertificate
public import Zkc.Construction.ConnectionInstallation
public import ZkcTools.ConstructionBindings.Readback
public meta import Lean.Elab.Tactic

public meta section

/-! Untrusted proposal for finite alignment derivations. Search reads
explicit source/view syntax and the symbolic frame; every accepted association
is rechecked by the kernel through the core derivation constructors. No simp
database, protocol names, evaluator or semantic proof callbacks are used. -/
set_option autoImplicit false
namespace ZkcTools.ConstructionBindings.Alignment
open Lean Meta Elab Tactic
open Zkc.Source Zkc.Source.Structured Zkc.Construction

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

private def tryReflexivity (goals : List MVarId) : TacticM (List MVarId) := do
  for goal in goals do
    unless ← goal.isAssigned do
      let saved ← saveState
      try goal.refl catch _ => saved.restore
  goals.filterM fun goal => return !(← goal.isAssigned)

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
    unless ← isDefEq (← inferType argument) domain do
      throwError "alignment-constructor-field-type: {name}, field={index}, expected={domain}, actual={← inferType argument}"
    arguments := arguments.push argument
    type := body.instantiate1 argument
  return mkAppN constructor arguments

private def viewHead (expression : Expr) : MetaM Expr := do
  let mut current := expression
  repeat
    current := current.headBeta
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
  let source ← whnf args[12]!
  let sourceParts := source.getAppArgs
  if rule == ``ConnectionCertificate.Derivation.observedSend then
    unless source.isAppOf ``NormalForm.Form.send do throwError "alignment-expected-send"
  else unless source.isAppOf ``NormalForm.Form.receive do throwError "alignment-expected-receive"
  let layout := args[11]!
  let mut initial := layout
  if rule == ``ConnectionCertificate.Derivation.observedReceive then
    initial ← mkAppM ``ConnectionCertificate.receiveLayout #[layout, sourceParts[sourceParts.size - 4]!]
  if rule == ``ConnectionCertificate.Derivation.delivery then
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
  if rule == ``ConnectionCertificate.Derivation.delivery then
    supplied := supplied ++ #[(`observeStateRef, observationParts[4]!), (`observePathRef, observationParts[6]!)]
  else
    supplied := supplied ++ #[(`stateRef, observationParts[4]!), (`pathRef, observationParts[6]!),
      (`template, observationParts[3]!)]
    if rule == ``ConnectionCertificate.Derivation.observedSend then
      supplied := supplied.push (`reference, observationParts[5]!)
  let constructor ← mkConstWithFreshMVarLevels rule
  let mut type ← inferType constructor
  let mut fields := #[]
  for index in [:200] do
    let .forallE name domain body _ := type | break
    let value ← if index < 12 then pure args[index]! else
      match supplied.find? (fun item => item.1 == name) with
      | some (_, value) => pure value
      | none => mkFreshExprMVar domain
    unless ← isDefEq (← inferType value) domain do throwError "alignment-observation-field {name}"
    fields := fields.push value
    type := body.instantiate1 value
  tryReflexivity (← goal.apply (mkAppN constructor fields))

private def refuseSource (source : Expr) : TacticM Unit := do
  let source ← whnf source
  if source.isAppOf ``NormalForm.Form.apply then throwError "alignment-unsupported-callee"


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
  let type ← instantiateMVars (← goal.getType)
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
    for rule in [``ConnectionCertificate.HistoryReadback.plain, ``ConnectionCertificate.HistoryReadback.transcript] do
      let saved ← saveState
      try
        for pending in ← applyRule goal rule do staticGoal pending
        return
      catch _ => saved.restore
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
  unless ← isProp type do throwError "alignment-unresolved-static-data: {type}"
  setGoals [goal]
  evalTactic (← `(tactic| decide +kernel))

private partial def derive (goal : MVarId) : TacticM Unit := goal.withContext <|
    Term.withoutErrToSorry <| withoutRecover do
  let expected ← instantiateMVars (← goal.getType)
  if expected.isAppOf ``ConnectionCertificate.Certificate then
    let [alignment] ← applyRule goal ``ConnectionCertificate.Certificate.mk
      | throwError "alignment-normalization-failed"
    derive alignment
    return
  unless expected.isAppOf ``ConnectionCertificate.Derivation do
    throwError "alignment-expected-derivation"
  let args := expected.getAppArgs
  let scope := args[9]!
  let layout := args[11]!
  let source ← whnf args[12]!
  let target := args[13]!
  if source.isAppOf ``NormalForm.Form.split then
    let parts := source.getAppArgs
    let component ← whnf parts[parts.size - 3]!
    if component.isAppOf ``NormalForm.Comp.absent || component.isAppOf ``NormalForm.Comp.present then
      let pending ← applyRule goal (if component.isAppOf ``NormalForm.Comp.absent then
        ``ConnectionCertificate.Derivation.splitAbsent else ``ConnectionCertificate.Derivation.splitValue)
      for remaining in pending do
        if (← instantiateMVars (← remaining.getType)).isAppOf ``ConnectionCertificate.Derivation then derive remaining
        else staticGoal remaining
      return
    let subject ← splitSubject component
    let frame ← listEntries layout
    for cell in frame, index in [:frame.size] do
      let cell ← whnf cell
      if cell.isAppOf ``ConnectionFrame.Cell.data && (← isDefEq cell.getAppArgs.back! component) then
        let constructor ← mkAppOptM ``ConnectionCertificate.Derivation.splitPresent
          ((args.extract 0 12).map some ++ #[none, some subject, some parts[parts.size - 2]!, some parts.back!, some target, some (mkNatLit index)])
        let [tail] ← tryReflexivity (← goal.apply constructor)
          | throwError "alignment-presence-static-mismatch"
        derive tail
        return
    let constructor ← mkAppOptM ``ConnectionCertificate.Derivation.split
      ((args.extract 0 12).map some ++ #[none, some subject, some parts[parts.size - 2]!, some parts.back!, some target])
    let [absent, present] ← goal.apply constructor | throwError "alignment-split-shape"
    derive absent
    derive present
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
          unless body.isAppOf ``Region.ret do break
          let before ← mkAppM ``List.take #[mkNatLit index, args[2]!]
          let after ← mkAppM ``List.drop #[mkNatLit (index + 1), args[2]!]
          let definitionsSyntax ← Term.exprToSyntax args[2]!
          let selected ← Term.elabTerm
            (← `(($definitionsSyntax).get ⟨$(quote index), by decide +kernel⟩)) (mkConst ``CheckedDefinition)
          let projectionType ← mkAppM ``ConnectionHelpers.Projection #[args[2]!, selected]
          let beforeSyntax ← Term.exprToSyntax before
          let afterSyntax ← Term.exprToSyntax after
          let positionsSyntax ← Term.exprToSyntax body.getAppArgs.back!
          let projection ← Term.elabTerm
            (← `(⟨$beforeSyntax, $afterSyntax, rfl, by decide +kernel, $positionsSyntax, rfl⟩)) projectionType
          Term.synthesizeSyntheticMVarsNoPostponing
          let constructor ← mkAppOptM ``ConnectionCertificate.Derivation.projectionHelper
            ((args.extract 0 12).map some ++ #[some selected, some projection,
              some sourceParts[sourceParts.size - 2]!, some sourceParts.back!, some target])
          let mut tails := []
          for pending in ← goal.apply constructor do
            if (← instantiateMVars (← pending.getType)).isAppOf ``ConnectionCertificate.Derivation then
              tails := tails ++ [pending]
            else staticGoal pending
          for tail in tails do derive tail
          return
  if !(source.isAppOf ``NormalForm.Form.math) then refuseSource source
  let saved ← saveState
  let mut returnFailure : MessageData := "not a return"
  try
    let [readback, historyRead] ← goal.apply (← mkConstWithFreshMVarLevels ``ConnectionCertificate.Derivation.done)
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
    let pending ← applyRule goal ``ConnectionCertificate.Derivation.halt
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
          let constructor ← mkAppOptM ``ConnectionCertificate.Derivation.compute
            ((args.extract 0 12).map some ++
              #[some operation, some terms, some sourceParts.back!, some rest, some references, some yes, some yes])
          goal.apply constructor
          catch _ => throwError "alignment-compute-operation-or-view-mismatch"
        let [readback, tail] := pending | throwError "alignment-compute-shape"
        setGoals [readback]
        evalTactic (← `(tactic| derive_source_readback))
        derive tail
        return
      -- Normalization removes total source instructions before a compute node.
      -- Retain their real target checkpoints and extend the symbolic frame
      -- before proposing the partial step; never treat that step as total.
      let pending ← try
        let terms ← operandTerms scope layout references
        let yes ← mkEqRefl (mkConst ``Bool.true)
        let supplied := (args.extract 0 13).map some ++
          #[some operation, some yes, some terms, some references, some yes, some yes]
        let constructor ← mkAppOptM ``ConnectionCertificate.Derivation.calculation supplied
        goal.apply constructor
      catch exception =>
        if computing then throwError "alignment-compute-operation-or-view-mismatch"
        else throw exception
      setGoals pending
      let [readback, tail] ← getUnsolvedGoals | throwError "alignment-calculation-shape"
      setGoals [readback]
      evalTactic (← `(tactic| derive_source_readback))
      derive tail
      return
    if [``Domain.View.receive, ``Domain.View.send, ``Domain.View.observe, ``Domain.View.challenge,
        ``Domain.View.localService, ``Domain.View.indicesEmpty, ``Domain.View.indicesAppend].any first.isAppOf then
      let rules := if first.isAppOf ``Domain.View.receive then
          [``ConnectionCertificate.Derivation.receive, ``ConnectionCertificate.Derivation.observedReceive]
        else if first.isAppOf ``Domain.View.send then
          [``ConnectionCertificate.Derivation.send, ``ConnectionCertificate.Derivation.observedSend]
        else if first.isAppOf ``Domain.View.observe then [``ConnectionCertificate.Derivation.observedSend]
        else if first.isAppOf ``Domain.View.challenge then
          [``ConnectionCertificate.Derivation.publicQuery, ``ConnectionCertificate.Derivation.delivery]
        else if first.isAppOf ``Domain.View.localService then [``ConnectionCertificate.Derivation.localQuery]
        else if first.isAppOf ``Domain.View.indicesEmpty then [``ConnectionCertificate.Derivation.indicesEmpty]
        else [``ConnectionCertificate.Derivation.indicesAppend]
      let mut selected : Option (List MVarId) := none
      let mut failure : MessageData := "no applicable action rule"
      for rule in rules do
        let saved ← saveState
        try
          let pending ← if [``ConnectionCertificate.Derivation.observedSend,
              ``ConnectionCertificate.Derivation.observedReceive, ``ConnectionCertificate.Derivation.delivery].contains rule then
              preparedAction goal rule args model block first
            else applyRule goal rule
          let mut tails := []
          for remaining in pending do
            let type ← instantiateMVars (← remaining.getType)
            if type.isAppOf ``ConnectionCertificate.Derivation then tails := tails ++ [remaining]
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
      for tail in tails do derive tail
      return
    if first.isAppOf ``Domain.View.guard then
      let mut selected : Option (List MVarId) := none
      for rule in [``ConnectionCertificate.Derivation.guard,
          ``ConnectionCertificate.Derivation.trueGuard, ``ConnectionCertificate.Derivation.falseGuard] do
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
            else if type.isAppOf ``ConnectionCertificate.Derivation then
              tails := pendingGoal :: tails
            else staticGoal pendingGoal
          selected := some tails
          break
        catch _ => saved.restore
      let some tails := selected | throwError "alignment-guard-mismatch"
      for tail in tails do derive tail
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
      let rule := if strict then ``ConnectionCertificate.Derivation.strictHelper
        else if owned then ``ConnectionCertificate.Derivation.ownedHelper
        else ``ConnectionCertificate.Derivation.mathHelper
      let fields := (if owned then #[some sourceParts[sourceParts.size - 4]!] else #[]) ++
        #[some program, some helper] ++ (if strict || owned then #[] else #[some math])
      let constructor ← mkAppOptM rule
        ((args.extract 0 12).map some ++ fields ++ #[some binding,
          some arguments, some sourceParts.back!, some rest, some references, some yes, some yes])
      let pending ← try goal.apply constructor
        catch exception => throwError "alignment-helper-static-mismatch: {exception.toMessageData}"
      let pending ← tryReflexivity pending
      let [readback, tail] := pending | throwError "alignment-helper-static-mismatch: remaining={pending.length}"
      setGoals [readback]
      try evalTactic (← `(tactic| derive_source_readback))
      catch _ => throwError "alignment-helper-operand-readback-mismatch-or-optional"
      derive tail
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
      let distinct ← mkAppM ``ConnectionFrame.rosterCheck_sound #[args[1]!, args[5]!, roster,
        ← mkEqRefl (mkConst ``Bool.true)]
      let body ← mkLambdaFVars #[model] viewParts[6]!
      let rest ← mkLambdaFVars #[model] block.getAppArgs[2]!
      let visible ← whnf (← mkAppM ``ConnectionFrame.visibleState
        #[args[5]!, ← mkAppM ``RepeatSpec.stateScopes #[spec], ← mkAppM ``RepeatSpec.state #[spec]])
      let constructor ← if visible.isConstOf ``Bool.true then
        finiteApplication ``ConnectionCertificate.Derivation.repeat
          ((args.extract 0 12).map some ++ #[some spec, some site, some callback, some count.getAppArgs.back!,
            some parts[parts.size - 3]!, some parts[parts.size - 2]!, some parts.back!, some body, some rest,
            some roster, some distinct, none, none, none, some viewParts[3]!, none,
            some stateReferences, some initial, some yieldData, some yielded, some initialHistory, some bodyHistory])
      else do
        let scopes ← mkAppM ``RepeatSpec.stateScopes #[spec]
        let initialLocations ← whnf (← mkAppM ``ConnectionInstallation.returnLocations #[args[5]!, scopes, stateReferences])
        let yieldLocations ← whnf (← mkAppM ``ConnectionInstallation.returnLocations #[args[5]!, scopes, yieldData])
        unless initialLocations.isAppOf ``Option.some && yieldLocations.isAppOf ``Option.some do
          throwError "alignment-loop-projected-location-arity"
        let mappedRole ← mkAppM ``ProtocolContext.roles #[args[1]!, args[5]!]
        let mappedScopes ← mkAppM ``ProtocolContext.mapScopes #[args[1]!, scopes]
        let schema ← whnf (← mkAppM ``Original.roleOutputSorts
          #[mappedRole, mappedScopes, ← mkAppM ``RepeatSpec.state #[spec]])
        unless schema.isAppOf ``Option.some do throwError "alignment-loop-projected-schema"
        finiteApplication ``ConnectionCertificate.Derivation.projectedRepeat
          ((args.extract 0 12).map some ++ #[some spec, some site, some callback, some count.getAppArgs.back!,
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
        if type.isAppOf ``ConnectionCertificate.Derivation then tails := tails ++ [remaining]
        else if type.isAppOf ``ConnectionFrame.Readback then
          setGoals [remaining]
          try evalTactic (← `(tactic| derive_source_readback))
          catch _ => throwError "alignment-loop-state-readback-mismatch"
        else
          try staticGoal remaining
          catch _ => throwError "alignment-loop-count-scope-profile-or-return-mismatch"
      for tail in tails do derive tail
      return
    throwError "alignment-unsupported-target"

/-- Propose a source Certificate, or a finite Derivation for a fixed normal
form. This is not an executable verified checker: failure diagnostics and
search are untrusted; successful output is data checked by the Lean kernel. -/
elab "derive_connection_alignment" : tactic => withMainContext do
  let goal ← getMainGoal
  let pending := (← getGoals).tail
  derive goal
  setGoals pending

end ZkcTools.ConstructionBindings.Alignment
