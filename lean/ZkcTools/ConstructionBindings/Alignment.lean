module

public import Zkc.Construction.ConnectionCertificate
public import ZkcTools.ConstructionBindings.Readback
public meta import Lean.Elab.Tactic

public meta section

/-! Untrusted proposal for finite plain alignment derivations. Search reads
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
  let mut terms := #[]
  for reference in refs do
    let some index ← getNatValue? reference | throwError "alignment-nonstatic-reference"
    let some proposed := frame[index]? | throwError "alignment-reference-out-of-range"
    let cell ← whnf proposed
    unless cell.isAppOf ``ConnectionFrame.Cell.data do throwError "alignment-operand-not-data"
    let component ← whnf cell.getAppArgs.back!
    unless component.isAppOf ``NormalForm.Comp.present do throwError "alignment-operand-not-present"
    terms := terms.push component.getAppArgs.back!
  let laws ← mkListLit (mkConst ``NormalForm.LawKey) []
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

private def viewHead (expression : Expr) : MetaM Expr := do
  let mut current := expression
  repeat
    current := current.headBeta
    if [``Domain.View.sequence, ``Domain.View.calculation, ``Domain.View.receive,
        ``Domain.View.send, ``Domain.View.guard, ``Domain.View.helper, ``Domain.View.loop,
        ``Domain.View.empty].any current.isAppOf then return current
    let some unfolded ← unfoldDefinition? current | return current
    current := unfolded
  return current

private def refuseSource (source : Expr) : TacticM Unit := do
  let source ← whnf source
  if source.isAppOf ``NormalForm.Form.strict || source.isAppOf ``NormalForm.Form.math ||
      source.isAppOf ``NormalForm.Form.owned then throwError "alignment-unsupported-helper"
  if source.isAppOf ``NormalForm.Form.repeat then throwError "alignment-unsupported-loop"
  if source.isAppOf ``NormalForm.Form.apply then throwError "alignment-unsupported-callee"
  if source.isAppOf ``NormalForm.Form.query then throwError "alignment-unsupported-query"

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
  let scope := args[7]!
  let layout := args[8]!
  let source ← whnf args[9]!
  let target := args[10]!
  if source.isAppOf ``NormalForm.Form.split then
    let parts := source.getAppArgs
    let component := parts[parts.size - 3]!
    let subject ← splitSubject component
    let frame ← listEntries layout
    for cell in frame, index in [:frame.size] do
      let cell ← whnf cell
      if cell.isAppOf ``ConnectionFrame.Cell.data && (← isDefEq cell.getAppArgs.back! component) then
        let constructor ← mkAppOptM ``ConnectionCertificate.Derivation.splitPresent
          ((args.extract 0 9).map some ++ #[none, some subject, some parts[parts.size - 2]!, some parts.back!, some target, some (mkNatLit index)])
        let [tail] ← tryReflexivity (← goal.apply constructor)
          | throwError "alignment-presence-static-mismatch"
        derive tail
        return
    let constructor ← mkAppOptM ``ConnectionCertificate.Derivation.split
      ((args.extract 0 9).map some ++ #[none, some subject, some parts[parts.size - 2]!, some parts.back!, some target])
    let [absent, present] ← goal.apply constructor | throwError "alignment-split-shape"
    derive absent
    derive present
    return
  if !(source.isAppOf ``NormalForm.Form.math) then refuseSource source
  let saved ← saveState
  try
    let [readback] ← goal.apply (← mkConstWithFreshMVarLevels ``ConnectionCertificate.Derivation.done)
      | throwError "alignment-not-return"
    setGoals [readback]
    evalTactic (← `(tactic| derive_source_readback))
    return
  catch _ => saved.restore
  let saved ← saveState
  try
    let pending ← applyRule goal ``ConnectionCertificate.Derivation.halt
    unless pending.isEmpty do throwError "alignment-not-stop"
    return
  catch _ => saved.restore
  withLocalDeclD `model (mkConst ``DomainModel) fun model => do
    let block ← viewHead (mkApp target model)
    unless block.isAppOf ``Domain.View.sequence do
      if source.isAppOf ``NormalForm.Form.compute then throwError "alignment-compute-view-mismatch"
      if source.isAppOf ``NormalForm.Form.math then throwError "alignment-helper-view-mismatch"
      throwError "alignment-return-or-view-mismatch"
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
            ((args.extract 0 9).map some ++
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
        let supplied := (args.extract 0 10).map some ++
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
    if first.isAppOf ``Domain.View.receive || first.isAppOf ``Domain.View.send then
      let rule := if first.isAppOf ``Domain.View.receive then
        ``ConnectionCertificate.Derivation.receive else ``ConnectionCertificate.Derivation.send
      let pending ← applyRule goal rule
      let [tail] := pending | throwError "alignment-route-or-operand-mismatch"
      unless (← tail.getType).isAppOf ``ConnectionCertificate.Derivation do
        throwError "alignment-route-or-operand-mismatch"
      derive tail
      return
    if first.isAppOf ``Domain.View.guard then
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
                let [] ← applyRule pendingGoal ``ConnectionCertificate.GuardReadback.comparison
                  | throwError "comparison-readback"
              catch _ =>
                saved.restore
                let [] ← applyRule pendingGoal ``ConnectionCertificate.GuardReadback.boolean
                  | throwError "boolean-readback"
            else if type.isAppOf ``ConnectionCertificate.Derivation then
              tails := pendingGoal :: tails
            else throwError "alignment-guard-static-mismatch"
          for tail in tails do derive tail
          return
        catch _ => saved.restore
      throwError "alignment-guard-mismatch"
    if first.isAppOf ``Domain.View.helper then
      unless source.isAppOf ``NormalForm.Form.math do throwError "alignment-helper-source-mismatch"
      let sourceParts := source.getAppArgs
      let helper := sourceParts[sourceParts.size - 3]!
      let arguments := sourceParts[sourceParts.size - 2]!
      let parts := first.getAppArgs
      let program := parts[1]!
      let references := parts[3]!
      let binding ← helperBinding args[3]! helper program
      let math ← mkEqRefl (mkConst ``HelperKind.math)
      let yes ← mkEqRefl (mkConst ``Bool.true)
      let rest ← mkLambdaFVars #[model] block.getAppArgs[2]!
      let constructor ← mkAppOptM ``ConnectionCertificate.Derivation.mathHelper
        ((args.extract 0 9).map some ++ #[some program, some helper, some math, some binding,
          some arguments, some sourceParts.back!, some rest, some references, some yes, some yes])
      let pending ← try goal.apply constructor catch _ => throwError "alignment-helper-static-mismatch"
      let [readback, tail] ← tryReflexivity pending | throwError "alignment-helper-static-mismatch"
      setGoals [readback]
      try evalTactic (← `(tactic| derive_source_readback))
      catch _ => throwError "alignment-helper-operand-readback-mismatch-or-optional"
      derive tail
      return
    if first.isAppOf ``Domain.View.loop then throwError "alignment-unsupported-loop"
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
