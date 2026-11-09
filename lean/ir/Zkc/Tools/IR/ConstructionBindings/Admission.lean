module

public import Zkc.IR.Construction.ConnectionCertificateAdmission
public import Zkc.Tools.IR.ConstructionBindings.Root
public meta import Zkc.Tools.IR.ConstructionBindings.ViewSyntax
public meta import Lean.Elab.Tactic

public meta section

/-! Default proof production for the method-independent connection obligation.
Small roots need no separately authored or generated view selection. The same
untrusted action table proposes the exact constructed view and its ordinary
correspondence proof; the existing typed root engine checks the source arrow.
Large roots may instead reuse an imported checked certificate. -/
set_option autoImplicit false
namespace ZkcTools.ConstructionBindings.Admission
open Lean Meta Elab Tactic
open Zkc.Source Zkc.Source.Structured Zkc.Construction

private def parseTerm (text : String) : TacticM (TSyntax `term) := do
  match Parser.runParserCategory (← getEnv) `term text with
  | .ok parsed => return ⟨parsed⟩
  | .error reason => throwError "connection-view-proposal: {reason}"

/-- Evaluation here only proposes syntax. No native result is a proof premise;
the returned structural proof is checked against the original instruction list. -/
private unsafe def closedInstructions (artifact : Expr) : MetaM (List Zkc.Construction.Instruction) := do
  let instructions ← mkAppM ``Participant.instructions #[artifact]
  let instructions ← instantiateMVars instructions
  if instructions.hasFVar || instructions.hasMVar then
    throwError "connection-view-proposal: the instruction tree must be closed"
  -- Reflect the exposed data before evaluation so ordinary logical imports
  -- suffice; authors need not meta-import the artifact's runtime code. This
  -- reads instruction syntax, never executes the participant.
  let literal ← withTransparency .all <| reduce instructions
  evalExpr (List Zkc.Construction.Instruction)
    (← mkAppM ``List #[mkConst ``Zkc.Construction.Instruction]) literal

private def deriveConnection (selectedLibrary : Option (TSyntax `term)) : TacticM Unit := withMainContext do
  Term.withoutErrToSorry <| withoutRecover do
    let goal ← getMainGoal
    let remaining := (← getGoals).tail
    let expected := (← instantiateMVars (← goal.getType)).headBeta.consumeMData
    unless expected.isAppOf ``ConnectionAdmission.Required do
      throwError "derive_source_connection: expected the fixed connection requirement"
    let args := expected.getAppArgs
    let program ← Term.exprToSyntax args[0]!
    let context ← Term.exprToSyntax args[1]!
    let mode ← Term.exprToSyntax args[2]!
    let artifact ← Term.exprToSyntax args[3]!
    -- The final ofRootCertificate application checks the complete selection
    -- equation. Do not evaluate a second discarded Boundary here: it would
    -- duplicate the same finite admission before any reusable-body search.
    -- Keep fixed source/context fields outside the computed discovery record,
    -- so routine root projections do not evaluate the whole selection again.
    let routing ← Term.elabTerm (← `(
      ConnectionRootRoutes.routing ($program).snapshot $context $mode
        (ConnectionRootInputs.serviceCapabilities ($program).payload.entry.inputs)
        $artifact (by decide +kernel))) (some (mkConst ``Original.Routing))
    Term.synthesizeSyntheticMVarsNoPostponing
    let routingExpr := routing
    Alignment.tracePhase "admission instruction reflection start"
    let instructions ← unsafe closedInstructions args[3]!
    Alignment.tracePhase "admission instructions reflected"
    let .ok (viewText, proofText) := StructuredSource.Constructed.blockTerms 1024 instructions
      | throwError "connection-view-proposal: unsupported constructed instruction shape"
    Alignment.tracePhase "admission view syntax printed"
    let view ← parseTerm viewText
    let proof ← parseTerm proofText
    let modelName := mkIdent `model
    let programName := mkIdent `program
    let contextName := mkIdent `context
    let target ← `(open Zkc.Construction.Domain in
      fun ($modelName : Zkc.Source.Structured.DomainModel) =>
        let $programName := $program
        let $contextName := $context
        $view)
    let correspondence ← `(open Zkc.Construction.Domain in
      fun ($modelName : Zkc.Source.Structured.DomainModel) =>
        let $programName := $program
        let $contextName := $context
        $proof)
    let library ← match selectedLibrary with
      | some selected => pure selected
      | none => `(by derive_connection_library roles [ConnectionAdmission.role $context $mode])
    -- Let the root builder check the library at its expected type directly.
    -- An extra local alias would make otherwise closed source indices open
    -- during normalization and prevent their syntax from being shared.
    let rootType := mkAppN (mkConst ``ConnectionRoot.RootCertificate)
      #[args[0]!, routingExpr,
        mkApp2 (mkConst ``ConnectionAdmission.role) args[1]! args[2]!, args[3]!]
    let root ← Term.elabTerm (← `(by
      derive_root_connection_with_library target $target correspondence $correspondence
        services (ConnectionRootInputs.serviceCapabilities ($program).payload.entry.inputs)
        library $library)) (some rootType)
    Term.synthesizeSyntheticMVarsNoPostponing
    let root ← instantiateMVars root
    Alignment.tracePhase "admission root assigned"
    -- All indices are already fixed by the original obligation. Construct the
    -- explicit theorem application without asking elaborator unification to
    -- recover them again through the source's checked payload. The ordinary
    -- kernel checks this application, including the complete selection proof.
    let supplied :=  #[args[0]!, args[1]!, args[2]!, args[3]!, routingExpr, root]
    let mut selectedType := (← getConstInfo ``ConnectionAdmission.ofRootCertificate).type
    for argument in supplied do
      let .forallE _ _ body _ := selectedType
        | throwError "connection-admission-theorem-shape"
      selectedType := body.instantiate1 argument
    let .forallE _ selectionEquation _ _ := selectedType
      | throwError "connection-admission-selection-shape"
    let selected ← mkFreshExprMVar selectionEquation
    setGoals [selected.mvarId!]
    Alignment.tracePhase "admission selection check"
    evalTactic (← `(tactic| kernel_rfl))
    Alignment.tracePhase "admission selection checked"
    let proof := mkAppN (mkConst ``ConnectionAdmission.ofRootCertificate)
      (supplied.push (← instantiateMVars selected))
    goal.assign proof
    setGoals remaining
    Alignment.tracePhase "admission complete"

elab "derive_source_connection" : tactic => deriveConnection none

/-- Reuse a checked source library while deriving a fresh artifact connection.
The supplied library is checked against the actual source payload. -/
elab "derive_source_connection" "with_library" library:term : tactic =>
  deriveConnection (some library)

/-- Imported certificates share their first derivation; selection is still
checked against the same request-owned boundary, with no certificate identity
in that boundary's meaning. -/
macro "derive_source_connection" "using" root:term : tactic =>
  `(tactic| exact ConnectionAdmission.ofRootCertificate $root (by kernel_rfl))

end ZkcTools.ConstructionBindings.Admission
