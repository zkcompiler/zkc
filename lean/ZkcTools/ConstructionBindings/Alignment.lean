module

public import Zkc.Construction.ConnectionCertificate
public import Zkc.Construction.ConnectionInstallation
public import ZkcTools.ConstructionBindings.Readback
public meta import ZkcTools.ConstructionBindings.TargetPlacement
public meta import ZkcTools.ConstructionBindings.Family
public meta import ZkcTools.ConstructionBindings.TargetEquality
public meta import ZkcTools.ConstructionBindings.StructuralFacts
public meta import ZkcTools.ConstructionBindings.Syntax
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
    let heartbeats ← IO.getNumHeartbeats
    let destination := (← getOptions).get `zkc.connection.traceFile ("" : String)
    if destination.isEmpty then logInfo m!"{now} {message}"
    else IO.FS.withFile destination .append fun handle => handle.putStrLn s!"{now} hb={heartbeats} {message}"

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

private def operandTerms (scope layout references types : Expr) : MetaM Expr := do
  if ← Family.collecting then
    let laws ← mkListLit (mkConst ``NormalForm.LawKey) []
    let mut terms := #[]
    for ty in ← listEntries types do
      terms := terms.push (← mkFreshExprMVar (← mkAppM ``NormalForm.Term #[laws, scope, ty]))
    let mut result ← mkAppOptM ``NormalForm.Terms.nil #[some laws, some scope]
    for term in terms.reverse do result ← mkAppM ``NormalForm.Terms.cons #[term, result]
    return result
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
  let expected ← whnf (← instantiateMVars (← goal.getType))
  let constructor ← mkConstWithFreshMVarLevels rule
  let constructor := if expected.isAppOf ``ConnectionCertificate.Alignment then
      mkAppN constructor (expected.getAppArgs.extract 0 13) else constructor
  let pending ← goal.apply constructor
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

/-- Match a proposed target through primitive congruence. Fresh physical
references remain finite length equalities, checked at every concrete use. -/
private def applyWithLengths (goal : MVarId) (term : Expr) : TacticM (List MVarId) := do
  unless ← Family.collecting do
    let saved ← saveState
    try return ← goal.apply term {newGoals := .all}
    catch _ => saved.restore
  let expected ← whnf (← goal.getType)
  let mut term := term
  let mut inferred ← whnf (← inferType term)
  unless inferred.isAppOf ``ConnectionCertificate.Alignment do
    throwError "connection-family-target-derivation"
  for index in [:13] do
    tracePhase s!"family target source index {index}"
    unless ← isDefEq inferred.getAppArgs[index]! expected.getAppArgs[index]! do
      throwError "connection-family-target-source-index: {index}"
  if ← Family.collecting then
    -- This is equality of finite typed source syntax, not of its process
    -- meaning. It lets optional component shapes remain interface data.
    let saved ← saveState
    unless ← isDefEq inferred.getAppArgs[13]! expected.getAppArgs[13]! do
      saved.restore
      let equality ← mkFreshExprMVar (← mkEq inferred.getAppArgs[13]! expected.getAppArgs[13]!)
      let sourceFunction ← withLocalDeclD `source (← inferType inferred.getAppArgs[13]!) fun source =>
        mkLambdaFVars #[source] (mkAppN inferred.getAppFn (inferred.getAppArgs.set! 13 source))
      term ← mkEqMP (← mkCongrArg sourceFunction equality) term
      inferred ← whnf (← inferType term)
  else
    unless ← isDefEq inferred.getAppArgs[13]! expected.getAppArgs[13]! do
      throwError "connection-family-target-source-index: 13"
  tracePhase "family target congruence start"
  let equality ← TargetEquality.propose inferred.getAppArgs[14]! expected.getAppArgs[14]!
  tracePhase "family target congruence done"
  let typeFunction ← withLocalDeclD `target (mkConst ``ConnectionCertificate.Block) fun target =>
    mkLambdaFVars #[target] (mkAppN inferred.getAppFn (inferred.getAppArgs.set! 14 target))
  let transport ← mkCongrArg typeFunction equality
  goal.assign (← mkEqMP transport term)
  return (← getMVars (← instantiateMVars (mkMVar goal))).toList

private def viewHead (expression : Expr) : MetaM Expr := do
  let mut current := expression
  repeat
    current := (← instantiateMVars current).consumeMData
    while current.isHeadBetaTarget do current := current.headBeta.consumeMData
    if let .letE _ _ value body _ := current then
      current := body.instantiate1 value
      continue
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
      if ← Family.collecting then
        let termType ← mkAppOptM ``NormalForm.Term
          #[some (← mkListLit (mkConst ``NormalForm.LawKey) []), some scope, some (mkConst ``Ty.index)]
        -- Internal prefix cells are already fixed by the current target.
        -- Only unresolved caller cells become family parameters.
        let coordinate ← LayoutLookup.select? layout coordinateRef
        let coordinate ← match coordinate with
          | some selected => do
            let cell ← whnf selected.cell
            pure <| if cell.isAppOf ``ConnectionFrame.Cell.coordinates then
              some (cell.getAppArgs.back!, selected.proof) else none
          | none => pure none
        let index ← LayoutLookup.select? layout indexRef
        let index ← match index with
          | some selected => do
            let cell ← whnf selected.cell
            if !cell.isAppOf ``ConnectionFrame.Cell.data then pure none else do
              let component ← whnf cell.getAppArgs.back!
              pure <| if component.isAppOf ``NormalForm.Comp.present then
                some (component.getAppArgs.back!, selected.proof) else none
          | none => pure none
        let terms ← match coordinate with
          | some (value, _) => pure value
          | none => mkFreshExprMVar (← mkAppM ``List #[termType])
        let term ← match index with
          | some (value, _) => pure value
          | none => mkFreshExprMVar termType
        let extended ← mkAppM ``List.append #[terms, ← mkListLit termType [term]]
        let cell ← mkAppM ``ConnectionFrame.Cell.coordinates #[extended]
        let next ← mkAppM ``List.append #[layout, ← mkListLit (← inferType cell) [cell]]
        let (prepared, tail, suffix) ← coordinatePrefix next view.getAppArgs[2]! model
        let certificate ← finiteApplication ``ConnectionFrame.CoordinatePrefix.indicesAppend
          #[some scope, some layout, none, none, some terms, some term, some coordinateRef,
            some indexRef, coordinate.map (·.2), index.map (·.2), some tail]
        return (prepared, certificate, suffix)
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

/-- Reuse a field from the current source only at its checked constructor type. -/
private def sourceField? (fields : Array (Name × Expr)) (name : Name)
    (domain : Expr) : MetaM (Option Expr) := do
  let some (_, value) := fields.find? (·.1 == name) | return none
  let saved ← saveState
  if ← isDefEq (← inferType value) domain then return some value
  saved.restore
  return none

/-- An open substitution can be blocked on a finite operand metavariable.
Use named fields only after its source constructor is exposed. The guide can
still propose constructor choices; the unchanged indexed goal checks them. -/
private def exposedSourceFields (source : Expr) : MetaM (Array (Name × Expr)) := do
  match source.getAppFn.constName?.bind (← getEnv).find? with
  | some (.ctorInfo _) => Family.constructorFields source
  | _ => pure #[]

/-- Supply the prepared frame before matching an observation rule; higher-order
unification is never asked to invent an instruction schedule. -/
private def preparedAction (goal : MVarId) (rule : Name) (args : Array Expr)
    (model block first : Expr) (fixed : Array (Name × Expr) := #[]) : TacticM (List MVarId) := do
  tracePhase "family observation prepare"
  let source ← whnf args[13]!
  let sourceParts := source.getAppArgs
  let sourceFields ← exposedSourceFields source
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
  tracePhase "family observation prefix"
  unless suffix.isAppOf ``Domain.View.sequence do throwError "alignment-observation-suffix"
  let observation ← viewHead suffix.getAppArgs[1]!
  unless observation.isAppOf ``Domain.View.observe do throwError "alignment-observation-prefix"
  let rest ← mkLambdaFVars #[model] suffix.getAppArgs[2]!
  let observationParts := observation.getAppArgs
  let certificateType ← whnf (← inferType certificate)
  let certificateArgs := certificateType.getAppArgs
  unless certificateArgs.size == 4 do throwError "alignment-prefix-certificate-type: {certificateType}"
  unless observationParts.size > 6 do throwError "alignment-observation-arity: {observation}"
  let mut supplied : Array (Name × Expr) := fixed ++ #[( `prepared, certificateArgs[2]!),
    (`preparation, certificateArgs[3]!), (`preparationProof, certificate), (`rest, rest)]
  if rule == ``ConnectionCertificate.Alignment.delivery then
    let ty ← whnf sourceParts[sourceParts.size - 4]!
    supplied := supplied ++ #[(`field, ty.getAppArgs.back!),
      (`observeStateRef, observationParts[4]!), (`observePathRef, observationParts[6]!)]
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
      | none => match ← sourceField? sourceFields name domain with
        | some value => pure value
        | none => mkFreshExprMVar domain
    unless ← isDefEq (← inferType value) domain do throwError "alignment-observation-field {name}"
    fields := fields.push value
    type := body.instantiate1 value
  let pending ← applyWithLengths goal (mkAppN constructor fields)
  tracePhase "family observation applied"
  if ← Family.collecting then pure pending else tryReflexivity pending

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

mutual
private partial def staticGoal (goal : MVarId) : TacticM Unit := do
  let start ← IO.monoMsNow
  let head := (← goal.getType).getAppFn.constName?
  if ← Family.collecting then
    tracePhase s!"family static start {head}"
    let type ← goal.withContext <| whnf (← instantiateMVars (← goal.getType))
    -- A data hole is an unknown interface operand, not a proposition to prove.
    -- In particular assumption must never choose an unrelated local Nat,
    -- output list or history value merely because its type matches.
    if ← Interface.finiteData type then return
    if !(type.isAppOf ``Eq) && (← Interface.structural type) then
      -- Readback and route certificates check the instantiated finite
      -- boundary. Expanding them against unknown caller data duplicates work
      -- and may split every output-selection Boolean during discovery.
      return
    if type.isAppOf ``Eq && (← Interface.structural type) then
      -- Use proof-producing finite queries first. Open normalization and
      -- projection equations are checked after their concrete interface data
      -- is fixed; unrestricted conversion here performs speculative search.
      -- Keep source normalization at the finite interface during discovery.
      -- Matching whole open bodies here specializes the family too early;
      -- application checks these equations after fixing actual operands.
      if ← StructuralFacts.propose goal (sourceSyntax := false) then return
      let left := type.getAppArgs[1]!
      let right := type.getAppArgs[2]!
      if left == right || left.isMVar || right.isMVar ||
          (!type.hasFVar && !type.hasExprMVar) then
        let saved ← saveState
        try goal.withContext goal.refl
        catch error =>
          if error.isRuntime || error.isInterrupt then throw error
          saved.restore
      return
  let saved ← saveState
  try staticStep goal
  catch error =>
    if error.isRuntime || error.isInterrupt then throw error
    saved.restore
    let type ← goal.withContext <| whnf (← instantiateMVars (← goal.getType))
    unless (← Family.collecting) && ((← Interface.structural type) || (← Interface.finiteData type)) do
      throw error
  let elapsed := (← IO.monoMsNow) - start
  if elapsed > 1000 then tracePhase s!"static {head} ms={elapsed}"

private partial def staticStep (goal : MVarId) : TacticM Unit := goal.withContext do
  if ← goal.isAssigned then return
  let original ← instantiateMVars (← goal.getType)
  if original.hasExprMVar then
    goal.setType (← StructuralFacts.reduceRecordProjections original)
  -- Query a known finite layout without expanding its inherited prefix.
  if ← StructuralFacts.propose goal then return
  let boundary ← instantiateMVars (← goal.getType)
  if boundary.isAppOfArity ``Eq 3 && boundary.hasExprMVar then
    -- Keep the effectful operand read inside the shape check: do-notation
    -- lifts `(← ...)` out of Boolean conjunction before evaluating its guard.
    if (← whnf boundary.getAppArgs[0]!).isAppOf ``NormalForm.Form then
      -- Source substitution may mention unused fields of a placement record.
      -- Normalize only the syntax equation, not layout/readback operands.
      let arguments ← boundary.getAppArgs.mapM fun argument =>
        withTransparency .all <| reduce argument (explicitOnly := false) (skipTypes := false)
      goal.setType (mkAppN boundary.getAppFn arguments)
  let saved ← saveState
  try
    if boundary.isAppOfArity ``Eq 3 && boundary.hasExprMVar &&
        (boundary.getAppArgs[1]!.isAppOf ``List.get?Internal ||
          boundary.getAppArgs[1]!.isAppOf ``GetElem?.getElem?) then
      withReducible goal.refl
    else goal.refl
    return
  catch _ => saved.restore
  let saved ← saveState
  try
    goal.assumption
    return
  catch _ => saved.restore
  let type ← whnf (← instantiateMVars (← goal.getType))
  if ← Family.collecting then
    -- Congruence under the unused model binder may lift a finite operand
    -- equation. Family.install hoists it back before auditing the interface.
    if let .forallE _ _ body _ := type then
      if !body.hasLooseBVars && (← Interface.structural body) then return
  if (← Family.collecting) && (← Interface.finiteData type) then return
  if type.hasExprMVar && type.isAppOf ``Eq then
    -- Determining data may come from a later readback or routing fact. Broad
    -- conversion here unfolds entire inherited layouts before that data is
    -- available. The caller retries after finite interface progress.
    if type.getAppArgs[1]!.isAppOf ``List.get?Internal ||
        type.getAppArgs[1]!.isAppOf ``GetElem?.getElem? then
      throwError "alignment-undetermined-layout-query"
    let saved ← saveState
    try
      withTransparency .all goal.refl
      return
    catch _ => saved.restore
  if type.isAppOf ``ConnectionFrame.Readback then
    setGoals [goal]
    evalTactic (← `(tactic| derive_source_readback))
    return
  if type.isAppOf ``ConnectionCertificate.GuardReadback then
    for rule in [``ConnectionCertificate.GuardReadback.boolean,
        ``ConnectionCertificate.GuardReadback.comparison] do
      let saved ← saveState
      try
        for pending in ← applyRule goal rule do staticGoal pending
        return
      catch error =>
        if error.isRuntime || error.isInterrupt then throw error
        saved.restore
    throwError "alignment-guard-placement-readback"
  if type.isAppOf ``ConnectionCertificate.HistoryReadback then
    let args := type.getAppArgs
    let selector ← whnf args[3]!
    if selector.isAppOf ``Option.none then
      for pending in ← applyRule goal ``ConnectionCertificate.HistoryReadback.plain do staticGoal pending
      return
    if selector.isAppOf ``Option.some then
      -- The profile has already fixed the transcript location. Query that
      -- cell compositionally; scanning the inherited frame would inspect
      -- unrelated, possibly unresolved guard and presence substitutions.
      let reference := selector.getAppArgs.back!
      if let some selected ← LayoutLookup.select? args[1]! reference then
        let expected ← mkAppOptM ``ConnectionFrame.Cell.history #[some args[0]!, some args[2]!]
        unless ← isDefEq selected.cell expected do
          throwError "alignment-history-cell-mismatch"
        let certificate ← mkAppOptM ``ConnectionCertificate.HistoryReadback.transcript
          #[some args[0]!, some args[1]!, some args[2]!, some reference, some selected.proof]
        goal.assign certificate
      else
        -- Fully determined compound frames (including application returns)
        -- can check this one fixed location by conversion. No other slot is
        -- searched, and an open predecessor remains deferred.
        if (← instantiateMVars args[1]!).hasExprMVar then
          throwError "alignment-history-cell-undetermined"
        let constructor ← mkAppOptM ``ConnectionCertificate.HistoryReadback.transcript
          #[some args[0]!, some args[1]!, some args[2]!, some reference]
        for checked in ← goal.apply constructor do staticGoal checked
      return
    if (← instantiateMVars args[1]!).hasExprMVar then
      throwError "alignment-history-selector-undetermined"
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

end

/-- The finite interface solver never constructs an alignment. -/
def solveStructural (goal : MVarId) : TacticM Unit := staticGoal goal

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

/-- Account for an actual total target calculation whose source instruction
has normalized into an operand. The source form remains fixed. -/
private def applyAuxiliaryCalculation (goal : MVarId) (args : Array Expr)
    (operation references : Expr) : TacticM (MVarId × MVarId) := do
  let terms ← operandTerms args[10]! args[12]! references
    (← mkAppM ``Op.arguments #[← mkAppM ``Calculation.op #[operation]])
  let yes ← mkEqRefl (mkConst ``Bool.true)
  let supplied := (args.extract 0 14).map some ++
    #[some operation, some yes, some terms, some references, some yes, some yes]
  let constructor ← mkAppOptM ``ConnectionCertificate.Alignment.calculation supplied
  let [readback, tail] ← tryReflexivity (← goal.apply constructor)
    | throwError "alignment-calculation-shape"
  return (readback, tail)

private partial def openForm (guide expected : Expr) : MetaM Expr := do
  let guide ← whnf guide
  let constructor := guide.getAppFn
  let mut type ← inferType constructor
  let mut fields := #[]
  for original in guide.getAppArgs, index in [:guide.getAppArgs.size] do
    let .forallE _ domain body _ := type | throwError "connection-family-form-arity"
    let domainHead ← whnf domain
    let value ← if index < 4 then pure expected.getAppArgs[index]!
      else if domainHead.isAppOf ``NormalForm.Form then openForm original domainHead
      else if !domain.hasFVar && !domain.hasExprMVar then pure original
      else mkFreshExprMVar domain
    fields := fields.push value
    type := body.instantiate1 value
  return mkAppN constructor fields

/-- Replay constructor choices as an untrusted proposal at the open family
interface. Closed source declarations and nominal sorts are retained; scope,
operands, physical references and all structural facts are inferred afresh.
The guide is never installed as evidence for the new placement. -/
private partial def replayBody (goal : MVarId) (guide : Expr) : TacticM Unit := goal.withContext do
  let expected ← whnf (← instantiateMVars (← goal.getType))
  let mut indices := expected.getAppArgs
  for index in [:13] do
    if indices[index]!.getAppFn.constName?.any (fun name =>
        "Zkc.Construction.ConnectionTargetPlacement.Placement.".isPrefixOf name.toString) then
      indices := indices.set! index (← whnf indices[index]!)
  let expected := mkAppN expected.getAppFn indices
  let guide ← whnf guide
  let name := guide.getAppFn.constName!
  tracePhase s!"family replay {name}"
  if [``ConnectionCertificate.Alignment.observedReceive,
      ``ConnectionCertificate.Alignment.observedSend, ``ConnectionCertificate.Alignment.delivery].contains name then
    let mut guideType := (← getConstInfo name).type
    let mut fixed := #[]
    for argument in guide.getAppArgs do
      let .forallE field _ body _ := guideType | throwError "connection-family-observation-guide"
      if field == `replacement then fixed := fixed.push (field, argument)
      guideType := body.instantiate1 argument
    let children ← guide.getAppArgs.zipIdx.filterM fun (argument, _) => do
      return (← whnf (← inferType argument)).isAppOf ``ConnectionCertificate.Alignment
    withLocalDeclD `replayModel (mkConst ``DomainModel) fun model => do
      let block ← viewHead (mkApp expected.getAppArgs[14]! model)
      unless block.isAppOf ``Domain.View.sequence do
        throwError "connection-family-observation-target"
      let first ← viewHead block.getAppArgs[1]!
      let pending ← preparedAction goal name expected.getAppArgs model block first fixed
      let mut index := 0
      for next in pending do
        if ← next.isAssigned then continue
        if (← whnf (← next.getType)).isAppOf ``ConnectionCertificate.Alignment then
          let some child := children[index]?
            | throwError "connection-family-observation-child-missing"
          replayBody next child.1
          index := index + 1
        else staticGoal next
      unless index == children.size do
        throwError "connection-family-observation-child-unused"
    return
  let constructor ← mkConstWithFreshMVarLevels name
  let mut type ← inferType constructor
  let mut fields := #[]
  let mut guided := #[]
  let mut namedFields : Array (Name × Expr) := #[]
  let indexNames : Array Name := #[`routing, `context, `definitions, `callees, `selection,
    `out, `role, `scopes, `outputs, `history, `scope, `frames, `layout]
  let indexed := indexNames.zip expected.getAppArgs
  let source ← whnf expected.getAppArgs[13]!
  let sourceFields ← exposedSourceFields source
  let application := name == ``ConnectionCertificate.Alignment.application ||
    name == ``ConnectionCertificate.Alignment.applicationRetainedHistory
  let mut supplied : Array (Name × Expr) := #[]
  if name == ``ConnectionCertificate.Alignment.split ||
      name == ``ConnectionCertificate.Alignment.splitPresent then
    unless source.isAppOf ``NormalForm.Form.split do throwError "connection-family-split-source"
    -- A symbolic optional argument need not expose input/read yet. Recover
    -- a determined subject directly; otherwise the finite source equation
    -- retains that boundary parameter until the actual placement fixes it.
    let saved ← saveState
    try
      supplied := #[(`subject, ← splitSubject source.getAppArgs[source.getAppArgs.size - 3]!)]
    catch error =>
      if error.isRuntime || error.isInterrupt then throw error
      saved.restore
  if application then
    let source ← whnf expected.getAppArgs[13]!
    unless source.isAppOf ``NormalForm.Form.apply do throwError "connection-family-application-source"
    let selection ← whnf expected.getAppArgs[4]!
    unless selection.isAppOf ``ConnectionLibrary.Selection.selected do
      throwError "connection-family-application-library"
    let selected := selection.getAppArgs
    let parts := source.getAppArgs
    let originalFields ← Family.constructorFields guide
    let some (_, originalSpine) := originalFields.find? (·.1 == `spine)
      | throwError "connection-family-application-spine"
    let some (_, returns) := originalFields.find? (·.1 == `returnSelection)
      | throwError "connection-family-application-returns"
    let (spine, rest) ← Family.splitTarget originalSpine expected.getAppArgs[14]!
    supplied := #[(`payload, selected[selected.size - 3]!), (`same, selected[selected.size - 2]!),
      (`library, selected.back!), (`callee, parts[parts.size - 6]!),
      (`signature, parts[parts.size - 5]!), (`roles, parts[parts.size - 4]!),
      (`site, parts[parts.size - 3]!), (`arguments, parts[parts.size - 2]!),
      (`next, parts.back!), (`returnSelection, returns), (`spine, spine), (`rest, rest)]
  for original in guide.getAppArgs do
    let .forallE field domain body _ := type | throwError "connection-family-guide-arity"
    let domainHead ← whnf domain
    let fromSource ← if indexed.any (·.1 == field) || supplied.any (·.1 == field) then pure none
      else sourceField? sourceFields field domain
    let value ← if let some (_, value) := indexed.find? (·.1 == field) then pure value
      else if let some (_, value) := supplied.find? (·.1 == field) then pure value
      else if let some value := fromSource then pure value
      else if domainHead.isAppOf ``NormalForm.Form then openForm original domainHead
      else if domainHead.isAppOf ``NormalForm.Terms then
        operandTerms domainHead.getAppArgs[1]! expected.getAppArgs[12]!
          (← mkListLit (mkConst ``Nat) []) domainHead.getAppArgs[2]!
      else if [``Helper, ``CheckedDefinition, ``Zkc.Source.Structured.Program, ``Calculation, ``RepeatSpec,
          ``Region, ``NormalForm.Equality, ``Ty, ``Replacement, ``ConnectionHelpers.Binding,
          ``ConnectionHelpers.Projection, ``ConnectionHelpers.CalculationBody].any domainHead.isAppOf ||
          field == `roster || field == `stateSorts || field == `site then
        pure original
      else if (← isProp domain) && !domain.hasFVar && !domain.hasExprMVar then pure original
      else if field == `distinct then do
        let roster := (fields.back!)
        let check ← mkAppM ``ConnectionFrame.rosterCheck
          #[expected.getAppArgs[1]!, expected.getAppArgs[6]!, roster]
        let proof ← mkFreshExprMVar (← mkEq check (mkConst ``Bool.true))
        mkAppM ``ConnectionFrame.rosterCheck_sound
          #[expected.getAppArgs[1]!, expected.getAppArgs[6]!, roster, proof]
      else mkFreshExprMVar domain
    unless ← isDefEq (← inferType value) domain do
      throwError "connection-family-guide-field: {field}"
    fields := fields.push value
    namedFields := namedFields.push (field, value)
    if domainHead.isAppOf ``ConnectionCertificate.Alignment then
      guided := guided.push (field, value.mvarId!, original)
    type := body.instantiate1 value
  let pending ← try applyWithLengths goal (mkAppN constructor fields)
    catch error =>
      if error.isRuntime || error.isInterrupt then throw error
      throwError "connection-family-guide-apply: {name}: {error.toMessageData}"
  -- Congruence can reorder metavariables in the proof term. Follow the
  -- constructor's own child fields, never the traversal order of getMVars.
  for (field, child, original) in guided do
    if application && field == `bodyCertificate then
      let input ← Family.application (mkAppN constructor fields)
      let some placed ← TargetPlacement.propose child input.entry input.placement staticGoal
        | throwError "connection-family-nested-body-refused"
      let some (_, extent) := namedFields.find? (·.1 == `physicalExtent)
        | throwError "connection-family-nested-extent"
      let physical ← mkAppM ``ConnectionTargetPlacement.CheckedBody.physicalExtent #[placed.body]
      unless ← isDefEq (← inferType physical) (← inferType extent) do
        throwError "connection-family-nested-extent-type"
      extent.mvarId!.assign physical
      continue
    unless ← child.isAssigned do replayBody child original
  if application then
    -- These existing constructor checks are decidable finite admission and
    -- history separation. Reflect them into Bool equations, rather than
    -- abstracting arbitrary propositions or another body derivation.
    for (field, value) in namedFields do
      if field == `admission || field == `separate then
        unless ← value.mvarId!.isAssigned do
          let rule ← if field == `admission then mkConstWithFreshMVarLevels ``of_decide_eq_true
            else do
              let get := fun name => (namedFields.find? (·.1 == name)).get!.2
              mkAppM ``ConnectionTargetPlacement.historySeparationCheck_sound
                #[get `calleeOutputs, get `calleeHistory]
          for fact in ← value.mvarId!.apply rule do
            staticGoal fact
  for next in pending do
    if ← next.isAssigned then continue
    let pendingType ← whnf (← instantiateMVars (← next.getType))
    if pendingType.isAppOf ``ConnectionCertificate.Alignment then
      throwError "connection-family-unguided-child"
    else if pendingType.isAppOf ``ConnectionTargetExtent.Extent then deriveExtent next
    else staticGoal next
    -- Close internal finite facts once. Only genuine boundary facts remain
    -- as parameters of the installed family.

/-- Install an open body from untrusted constructor choices discovered at one
actual call. Only the newly checked family becomes reusable evidence. -/
def installDiscoveredBody (entry routing selection placement guide : Expr) : TacticM Name :=
  Family.install entry routing selection placement fun generated => do
    let [alignment, extent] ← generated.apply (← mkConstWithFreshMVarLevels
        ``ConnectionTargetPlacement.CheckedBody.mk)
      | throwError "connection-family-fields"
    replayBody alignment guide
    deriveExtent extent

structure PlacementCost where
  name : Name
  proposalNanos : Nat
  kernelNanos : Nat
  deriving Inhabited, Repr

initialize placementCosts : IO.Ref (Array PlacementCost) ← IO.mkRef #[]

private def indexAlignment (state : Std.HashMap UInt64 (Array Name))
    (entry : UInt64 × Name) : Std.HashMap UInt64 (Array Name) :=
  state.insert entry.1 (((state[entry.1]?).getD #[]).push entry.2)

initialize checkedAlignments :
    SimplePersistentEnvExtension (UInt64 × Name) (Std.HashMap UInt64 (Array Name)) ←
  registerSimplePersistentEnvExtension {
    -- Local asynchronous additions do not synchronize theorem tasks. Hashes
    -- select exact-placement candidates only; neither a hash nor a cache hit
    -- supplies evidence without checking the declaration's complete type.
    asyncMode := .local
    addEntryFn := indexAlignment
    addImportedFn := fun imported => imported.foldl
      (fun state entries => entries.foldl indexAlignment state) {}
  }

/-- Close an exact retained placement behind a checked declaration. This is
an exact-placement boundary: it does not assert relocation invariance. -/
private def checkedBody (goal : MVarId) (build : MVarId → TacticM Unit) : TacticM Unit :=
  goal.withContext do
    let expected ← instantiateMVars (← goal.getType)
    let candidates := ((checkedAlignments.getState (← getEnv))[expected.hash]?).getD #[]
    for name in candidates do
      unless (← getEnv).contains name do continue
      let candidate := mkConst name
      let type ← inferType candidate
      if type.isForall || type != expected then continue
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
    modifyEnv fun environment => addNoncomputable (checkedAlignments.addEntry environment (closedType.hash, name)) name
    placementCosts.modify (·.push ⟨name, proposed - start, checked - proposed⟩)
    tracePhase s!"checked body {name}: proposal_ns={proposed-start}; kernel_ns={checked-proposed}"
    let reference := mkAppN (mkConst name closed.levelArgs.toList) closed.exprArgs
    goal.assign reference

/-- A proposal-local cache of closed syntax reductions. Backtracking across
candidate target cuts does not change these finite source/layout expressions.
It contains no evidence and is discarded after one root proposal. -/
private abbrev SyntaxCache := Syntax.Cache

private def reducedSyntax (cache : SyntaxCache) (expression : Expr) : TacticM Expr :=
  Syntax.normalize cache expression

/-- Propose liveness by finite typed substitutions. Each attempted omission
is accepted only when the actual continuation is definitionally unchanged.
The application constructor checks that equality again; this cache contains
syntax only and supplies no semantic evidence. -/
private def returnSelection (cache : SyntaxCache) (types next : Expr) : TacticM Expr := do
  let entries ← listEntries types
  let expected ← mkAppM ``ConnectionReturnProjection.Selection #[types]
  let literal := fun (flags : Array Bool) => do
    let mut literalSyntax ← `(term| Zkc.Source.Values.nil)
    for keep in flags.reverse do
      literalSyntax ← `(term| Zkc.Source.Values.cons $(quote keep) $literalSyntax)
    Term.elabTerm literalSyntax (some expected)
  let mut flags := Array.replicate entries.size true
  let mut selected ← literal flags
  for index in [:entries.size] do
    let candidate ← literal (flags.set! index false)
    let projected ← reducedSyntax cache (← mkAppM ``ConnectionReturnProjection.continuation #[candidate, next])
    if ← isDefEq projected next then
      flags := flags.set! index false
      selected := candidate
  return ← Syntax.freeze cache selected

private structure CutDiscovery where
  suffixes : Array Expr
  found : IO.Ref (Option Nat)

initialize discoveredCutException : InternalExceptionId ←
  registerInternalExceptionId `ZkcTools.ConstructionBindings.discoveredCut

/-- Discover a caller suffix by checked selected-return readback, without
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
  -- Canonicalize the dependent indices too. Leaving a computed scope or
  -- library key row here makes every constructor compare that computation
  -- against the compact indices of the cached source and frame.
  for index in [3, 5, 7, 8, 9, 10, 11, 12, 13] do
    -- A family's symbolic interface is already shared by its binders. Eagerly
    -- expanding it destroys layout constructors needed by their generic laws
    -- and duplicates open substitutions without creating cacheable syntax.
    if args[index]!.hasFVar then continue
    let start ← IO.monoMsNow
    args := args.set! index (← Syntax.freeze cache (← reducedSyntax cache args[index]!))
    let elapsed := (← IO.monoMsNow) - start
    if elapsed > 1000 then tracePhase s!"index {index} ms={elapsed}"
  for index in [1, 2, 14] do
    args := args.set! index (← Syntax.freeze cache args[index]!)
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
    let key ← mkAppM ``NormalForm.calleeAt #[args[3]!, callee]
    let declared ← mkAppM ``NormalForm.CalleeKey.signature #[key]
    let types ← reducedSyntax cache (← mkAppM ``ProtocolSignature.outputs #[declared])
    let selection ← returnSelection cache types next
    let continuationChecked ← mkEqRefl next
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
    let candidatesFor := fun index =>
      [(index, ``ConnectionCertificate.Alignment.application),
       (index, ``ConnectionCertificate.Alignment.applicationRetainedHistory)]
    let mut candidates := if slices.isEmpty then [] else
      ((slices.size - 1) :: List.range (slices.size - 1)).flatMap candidatesFor
    let mut visited : List (Nat × Name) := []
    let mut failure : MessageData := "no finite target slice"
    while !candidates.isEmpty do
      let (index, rule) := candidates.head!
      candidates := candidates.tail!
      if visited.contains (index, rule) then continue
      visited := (index, rule) :: visited
      let (spine, rest) := slices[index]!
      let entry ← mkAppM ``ConnectionLibrary.Library.entry #[library, callee]
      unless ← TargetPlacement.compatiblePrefix entry spine do
        failure := "alignment-reusable-body-refused: target instruction schedule"
        continue
      search.found.set none
      tracePhase s!"application slice {index}/{slices.size} {rule}"

      let saved ← saveState
      let installingFamily ← IO.mkRef false
      try
        let supplied := [( `payload, payload), (`same, same), (`library, library), (`callee, callee),
          (`signature, signature), (`roles, roles), (`site, site), (`arguments, arguments),
          (`spine, spine), (`next, next), (`rest, rest),
          (`returnSelection, selection), (`continuationChecked, continuationChecked)]
        let constructor ← mkConstWithFreshMVarLevels rule
        let mut type ← inferType constructor
        let mut fields := #[]
        let mut namedFields : Array (Name × Expr) := #[]
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
          namedFields := namedFields.push (name, value)
          type := body.instantiate1 value
        tracePhase "application assemble"
        let pending ← goal.apply (mkAppN constructor fields) {newGoals := .all}
        tracePhase "application assembled"
        let mut alignments := []
        let mut extents := []
        let mut statics := []
        for pending in pending do
          let pendingType ← whnf (← instantiateMVars (← pending.getType))
          if pendingType.isAppOf ``ConnectionTargetExtent.Extent then
            extents := extents ++ [pending]
          else if pendingType.isAppOf ``ConnectionCertificate.Alignment then alignments := alignments ++ [pending]
          else statics := statics ++ [pending]
        match alignments with
        | body :: tails =>
          let field := fun name => (namedFields.find? (·.1 == name)).get!.2
          let entered ← mkAppM ``ProtocolContext.enter #[args[1]!, site, roles]
          let placement ← mkAppOptM ``ConnectionTargetPlacement.Placement.mk
            #[some key, some entered, some scope, some arguments, some args[11]!, some layout,
              some (field `calleeOutputs), some (field `calleeHistory), some selection, some spine,
              some (field `extent)]
          match ← TargetPlacement.propose body entry placement staticGoal with
          | some placed =>
            let extent ← mkAppM ``ConnectionTargetPlacement.CheckedBody.physicalExtent #[placed.body]
            for pending in extents do
              unless ← isDefEq (← inferType extent) (← pending.getType) do
                throwError "alignment-reusable-body-extent"
              pending.assign extent
            tracePhase s!"reused body {placed.family}: proposal_ns={placed.proposalNanos}"
          | none =>
            if (← getOptions).getBool `zkc.connection.generateReusableBodies false &&
                !(← Family.collecting) && !(← TargetPlacement.hasEntry entry) then
              -- Discover the finite boundary once, without installing this
              -- concrete proposal as a per-placement proof declaration.
              for pending in extents do
                -- Infer the finite extent for discovery, but keep the actual
                -- root field open for the installed family's projection.
                let trialExtent ← mkFreshExprSyntheticOpaqueMVar (← pending.getType)
                deriveExtent trialExtent.mvarId!
              let trial ← mkFreshExprSyntheticOpaqueMVar (← body.getType)
              derive cache (some search) trial.mvarId!
              let placement ← instantiateMVars placement
              let earlierSelection := (← whnf (← body.getType)).getAppArgs[4]!
              installingFamily.set true
              let _ ← installDiscoveredBody entry args[0]! earlierSelection placement
                (← instantiateMVars trial)
              let some placed ← TargetPlacement.propose body entry placement staticGoal
                | throwError "alignment-generated-family-refused"
              let extent ← mkAppM ``ConnectionTargetPlacement.CheckedBody.physicalExtent #[placed.body]
              for pending in extents do
                unless ← isDefEq (← inferType extent) (← pending.getType) do
                  throwError "alignment-generated-family-extent"
                pending.assign extent
              installingFamily.set false
            else if (← getOptions).getBool `zkc.connection.requireReusableBodies false ||
                (← TargetPlacement.hasEntry entry) then
              throwError "alignment-reusable-body-refused"
            else
              for pending in extents do deriveExtent pending
              checkedBody body (derive cache (some search))
          for pending in statics do unless ← pending.isAssigned do staticGoal pending
          for alignment in tails do derive cache discovery alignment
        | [] => throwError "alignment-application-body-missing"
        return
      catch error =>
        if error.isRuntime || error.isInterrupt then throw error
        -- Discovery already checked this exact source/target boundary. A
        -- failure to generalize it is not evidence for another, longer slice.
        -- Preserve the useful failure instead of rederiving unrelated bodies.
        if ← installingFamily.get then
          throwError "connection-family-installation-failed: {error.toMessageData}"
        saved.restore
        if let .internal id _ := error then
          if id == discoveredCutException then
            if let some cut ← search.found.get then
              tracePhase s!"application discovered prefix {cut}"
              candidates := candidatesFor cut ++ candidates
              continue
            throw error
        trace[zkc.connection.placement] "application slice {index}: {error.toMessageData}"
        failure := error.toMessageData
        -- Formatting a dependent failure can traverse an entire root proof,
        -- even when tracePhase is disabled. Keep the original diagnostic for
        -- the final error; the search trace records only the failed choice.
        tracePhase s!"application slice {index} refused by {rule}"
    -- Total source computations can normalize into the arguments of the next
    -- application. First try every checked callee slice, then account for an
    -- auxiliary calculation in the caller before reusing the callee family.
    let auxiliary ← withLocalDeclD `applicationModel (mkConst ``DomainModel) fun model => do
      let block ← viewHead (mkApp target model)
      unless block.isAppOf ``Domain.View.sequence do return false
      let first ← viewHead block.getAppArgs[1]!
      unless first.isAppOf ``Domain.View.calculation do return false
      let (readback, tail) ← applyAuxiliaryCalculation goal args first.getAppArgs[1]! first.getAppArgs[2]!
      staticGoal readback
      derive cache discovery tail
      return true
    if auxiliary then return
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
      if cell.isAppOf ``ConnectionFrame.Cell.data then
        if ← isDefEq cell.getAppArgs.back! component then
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
    staticGoal readback
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
    tracePhase s!"target {first.getAppFn.constName?}"
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
        staticGoal readback
        derive cache discovery tail
        return
      -- Normalization removes total source instructions before a compute node.
      -- Retain their real target checkpoints and extend the symbolic frame
      -- before proposing the partial step; never treat that step as total.
      let (readback, tail) ← try applyAuxiliaryCalculation goal args operation references
      catch exception =>
        if computing then throwError "alignment-compute-operation-or-view-mismatch"
        else throw exception
      staticGoal readback
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
            if type.isAppOf ``ConnectionCertificate.Alignment then
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
      try staticGoal readback
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
      tracePhase "loop profile parsed"
      let roster ← mkAppM ``List.length #[← mkAppM ``ContextIdentity.roles #[← mkAppM ``Context.toContextIdentity #[context]]]
      let rosterCheck ← mkAppM ``ConnectionFrame.rosterCheck #[args[1]!, args[6]!, roster]
      let rosterProof ← mkFreshExprMVar (← mkEq rosterCheck (mkConst ``Bool.true))
      staticGoal rosterProof.mvarId!
      let distinct ← mkAppM ``ConnectionFrame.rosterCheck_sound #[args[1]!, args[6]!, roster, rosterProof]
      let body ← mkLambdaFVars #[model] viewParts[6]!
      let rest ← mkLambdaFVars #[model] block.getAppArgs[2]!
      let visible ← whnf (← mkAppM ``ConnectionFrame.visibleState
        #[args[6]!, ← mkAppM ``RepeatSpec.stateScopes #[spec], ← mkAppM ``RepeatSpec.state #[spec]])
      tracePhase "loop interface prepared"
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
        let stateSorts ← if schema.isAppOf ``Option.some then pure schema.getAppArgs.back!
          else if ← Family.collecting then do
            let declared ← listEntries viewParts[5]!
            let mut dataSorts := #[]
            for sort in declared do
              if (← whnf sort).isAppOf ``ValueSort.data then dataSorts := dataSorts.push sort
            mkListLit (mkConst ``ValueSort) dataSorts.toList
          else throwError "alignment-loop-projected-schema"
        tracePhase "loop projected schema proposed"
        finiteApplication ``ConnectionCertificate.Alignment.projectedRepeat
          ((args.extract 0 13).map some ++ #[some spec, some site, some callback, some count.getAppArgs.back!,
            some parts[parts.size - 3]!, some parts[parts.size - 2]!, some parts.back!, some body, some rest,
            some roster, some distinct, none, none, some stateSorts, none, some viewParts[3]!, none,
            some initialLocations.getAppArgs.back!, some yieldLocations.getAppArgs.back!,
            some stateReferences, some initial, some yieldData, some yielded, some initialHistory, some bodyHistory])
      tracePhase "loop constructor assembled"
      let pending ← try goal.apply constructor catch _ => throwError "alignment-loop-bound-schema-or-layout-mismatch"
      tracePhase "loop constructor applied"
      let pending ← tryReflexivity pending
      tracePhase "loop finite reflexivity complete"
      let mut tails := []
      for remaining in pending do
        if ← remaining.isAssigned then continue
        let type ← instantiateMVars (← remaining.getType)
        if type.isAppOf ``ConnectionCertificate.Alignment then tails := tails ++ [remaining]
        else if type.isAppOf ``ConnectionFrame.Readback then
          try staticGoal remaining
          catch _ => throwError "alignment-loop-state-readback-mismatch"
        else
          try staticGoal remaining
          catch error => throwError "alignment-loop-count-scope-profile-or-return-mismatch: {error.toMessageData}"
      for tail in tails do derive cache discovery tail
      return
    throwError "alignment-unsupported-target"

/-- Propose a source Certificate, or a finite Derivation for a fixed normal
form. This is not an executable verified checker: failure diagnostics and
search are untrusted; successful output is data checked by the Lean kernel. -/
elab "derive_connection_alignment" : tactic => withMainContext do
  let goal ← getMainGoal
  let pending := (← getGoals).tail
  let cache ← Syntax.newCache
  let start ← IO.monoNanosNow
  derive cache none goal
  let elapsed := (← IO.monoNanosNow) - start
  tracePhase s!"alignment proposal total_ns={elapsed}; syntax_kernel_ns={← cache.kernelNanos.get}; syntax_declarations={(← cache.declarations.get).size}"
  let result ← instantiateMVars (mkMVar goal)
  if result.hasExprMVar then throwError "alignment-unresolved-finite-admission"
  setGoals pending

/-- Construct a family at its symbolic interface, once. All parameters and
premises are ordinary Lean binders; no transport theorem or semantic callback
is assumed. Applications subsequently reference this checked declaration. -/
elab "derive_connection_target_body" : tactic => withMainContext do
  let goal ← getMainGoal
  let pending := (← getGoals).tail
  let expected ← whnf (← goal.getType)
  unless expected.isAppOf ``ConnectionTargetPlacement.CheckedBody do
    throwError "connection-target-body-expected-checked-body"
  let [alignment, extent] ← goal.apply (← mkConstWithFreshMVarLevels
      ``ConnectionTargetPlacement.CheckedBody.mk)
    | throwError "connection-target-body-fields"
  let cache ← Syntax.newCache
  derive cache none alignment
  deriveExtent extent
  Term.synthesizeSyntheticMVarsNoPostponing
  let result ← instantiateMVars (mkMVar goal)
  if result.hasExprMVar then
    let mut missing : MessageData := ""
    for hole in ← getMVars result do
      missing := m!"{missing}\n{← hole.getType}"
    throwError "connection-target-body-unresolved-interface: {missing}"
  setGoals pending

/-- Install a named parameterized family using the ordinary typed proposer.
The caller specifies the exact Entry and supported placement interface; the
generated declaration supplies the structural derivations and registration. -/
syntax "install_connection_target_body " ident bracketedBinder* " : " term : command
macro_rules
  | `(install_connection_target_body $name:ident $binders:bracketedBinder* : $type:term) =>
    `(command| @[connection_target_body] noncomputable def $name $binders* : $type := by
      derive_connection_target_body)

end ZkcTools.ConstructionBindings.Alignment
