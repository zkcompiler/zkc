module

public import ZkcTools.ProofAccount
public import ZkcTools.ConstructionBindings.Analysis
public meta import ZkcTools.ConstructionBindings.Analysis
public import ZkcSecurityExamples.RootProperties.SmallSumcheck.Soundness
public import ZkcSecurityExamples.RootProperties.TwoSums.Soundness
public import ZkcSecurityExamples.Generation.Roots.Catalogue
public meta import ZkcSecurityExamples.Generation.Roots.Catalogue

/-! The Sumcheck family owns its source-property checkpoint vocabulary once.
The shared inspector reads actual applications in checked declaration bodies.
Source selection checks complete snapshots and typed template associations;
nominal occurrences come from source/artifact analysis, not handwritten routes.
Missing attribution is explicit measurement data and never changes a receipt.
-/
public meta section
namespace ZkcSecurity.Generation.SumcheckAccounts
open Lean Meta Elab Term
open ZkcTools.ProofAccount
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Realizations.Sumcheck
open ZkcExamples.Structured
open Zkc.Source Zkc.Source.Structured

/-- Shared family mathematics and property rules, independent of root names. -/
def checkpoints : List Checkpoint := [
  { identifier := "initialization", phase := "initialization", responsibility := "M"
    owner := ``SourceRootProperties.one_no, callee := ``SourceIteration.initial_no
    route := .familyPackage },
  { identifier := "preservation", phase := "preservation", responsibility := "M"
    owner := ``SourceRound.adversarial, callee := ``false_round, route := .familyPackage },
  { identifier := "exit", phase := "exit", responsibility := "I"
    owner := ``SourceIteration.reduction_no, callee := ``Zkc.Obligations.Derivation.done
    selection := .lastArgument, route := .generalRule },
  { identifier := "frame", phase := "frame", responsibility := "I"
    owner := ``SourceIteration.reduction_frame, callee := ``Zkc.Obligations.RepeatedComponent.frame_repeatN
    route := .generalRule },
  { identifier := "terminal", phase := "terminal", responsibility := "M"
    owner := ``SourceRootProperties.one_no, callee := ``SourceIteration.terminal_check
    route := .familyPackage },
  { identifier := "repeat", phase := "preservation", responsibility := "I"
    owner := ``SourceIteration.no_repeat, callee := ``Zkc.Obligations.RepeatedComponent.no_repeatN
    proofObjectHeads := [``Zkc.Obligations.Derivation], route := .generalRule },
  { identifier := "conditional-sampling", phase := "preservation", responsibility := "D"
    owner := ``SourcePublicInstallations.no_steps, callee := ``SourceIteration.no_contract
    selection := .lastArgument, route := .familyPackage },
  { identifier := "template", phase := "association", responsibility := "I"
    owner := ``SourceFamily.validator_invoke, callee := ``Zkc.Source.Structured.Template.Association.invoke
    expectedUses := some 1, route := .generalRule }]

private def dataTerm (stx : Syntax) : TermElabM Expr := do
  let term ← elabTerm stx none
  synthesizeSyntheticMVarsNoPostponing
  return ← instantiateMVars term

def requireSame (actual expected : Expr) : MetaM Unit := do
  unless ← withTransparency .all (isDefEq actual expected) do
    throwError "proof-account: typed association mismatch"

/-- Complete source bytes, not diagnostic names, select the family instance. -/
unsafe def sourceAssociation (root : Roots.Selection) : TermElabM Expr := do
  let actual := mkIdent ((root.subjectNamespace ++ ".original").toName)
  let expected := mkIdent ((root.sourceModule ++ ".program").toName)
  let lhs ← dataTerm (← `($actual))
  let rhs ← dataTerm (← `(($expected).snapshot))
  requireSame lhs rhs
  let snapshot ← evalExpr Snapshot (mkConst ``Snapshot) (← withTransparency .all (reduce rhs))
  unless reprStr snapshot == reprStr root.snapshot do
    throwError "proof-account: catalogue snapshot differs from the checked source"
  for candidate in [``SumcheckSourceSelections.Selection.small, ``SumcheckSourceSelections.Selection.twoSums] do
    let selected := mkIdent candidate
    let source ← dataTerm (← `((SumcheckSourceSelections.source $selected).snapshot))
    if ← withTransparency .all (isDefEq rhs source) then return mkConst candidate
  throwError "proof-account: source has no checked Sumcheck property association"

private def declarationRecord (graph : Reachability) (name : Name) : MetaM Json := do
  let path ← graph.require name
  let info ← getConstInfo name
  return Json.mkObj [("declaration", toJson name.toString),
    ("root_path", toJson (path.map Name.toString)), ("type", toJson (← ppExpr info.type).pretty)]

/-- Compare the full typed template including payload, signature and bound.
The shared invocation law must be reached by this receipt's proof body; the
selection wrapper is data and need not occur in the proof after reduction. -/
def templateAssociation (graph : Reachability) (selection : Expr) (maximum : Nat) : TermElabM Json := do
  let record ← declarationRecord graph ``SourceFamily.validator_invoke
  let actual ← mkAppM ``SourceRootReference.reductionAssociation #[selection]
  let selected ← exprToSyntax selection
  let expected ← dataTerm (← `(Zkc.Source.Structured.Template.Association
    (SumcheckSourceSelections.source $selected).payload
    (SourceRootReference.reductionSignature $selected)
    (SumcheckVerifierBodies.reduceBody $(quote maximum))))
  requireSame (← inferType actual) expected
  return record

/-- Exact nominal paths distinguish sibling occurrences even with identical
field carriers, static bounds and shared mathematical proof applications. -/
def occurrenceAssociation (actual expected : ZkcTools.ConstructionBindings.Call) : MetaM Unit := do
  unless actual.application == expected.application && actual.library == expected.library &&
      actual.query == expected.query && actual.delivery == expected.delivery && actual.messages == expected.messages do
    throwError "proof-account: nominal source occurrence mismatch"

private def measured (graph : Reachability) (checkpoint : Checkpoint) : MetaM Json := do
  try
    account graph checkpoint
  catch error =>
    return Json.mkObj [("id", toJson checkpoint.identifier), ("phase", toJson checkpoint.phase),
      ("expected_layer", toJson checkpoint.responsibility), ("route", toJson checkpoint.route.label),
      ("owner", toJson checkpoint.owner.toString), ("callee", toJson checkpoint.callee.toString),
      ("proof_status", "unattributed"), ("reason", toJson (← error.toMessageData.toString))]

unsafe def measure (root : Roots.Selection) (receipt : Name) : TermElabM Json := do
  let selection ← sourceAssociation root
  let program ← ofExcept (Zkc.Source.Structured.check root.snapshot)
  let layout ← ofExcept (ZkcTools.ConstructionBindings.analyze program root.artifacts.validator)
  let sourceCalls ← ofExcept (ZkcTools.ConstructionBindings.sourceCalls program layout.context)
  let maximumExpr ← mkAppM ``SumcheckSourceSelections.maximum #[selection]
  let maximum ← evalExpr Nat (mkConst ``Nat) (← withTransparency .all (reduce maximumExpr))
  let graph ← reachable receipt
  let _ ← graph.require ((root.subjectNamespace ++ ".validatorSubject").toName)
  let connection := "ZkcExamples.Structured.Generated.Connections." ++ root.name
  let rootBinding ← declarationRecord graph ((connection ++ ".validator").toName)
  let sourceBinding ← declarationRecord graph ``SourceRootReference.actual_reference
  let template ← templateAssociation graph selection maximum
  let requestName := (root.subjectNamespace ++ "SoundnessClaims.request1Data").toName
  let requestRecord ← declarationRecord graph requestName
  let request ← evalExpr Zkc.Claims.Wire.Request (mkConst ``Zkc.Claims.Wire.Request)
    (← withTransparency .all (reduce (mkConst requestName)))
  let rootCheckpoints : List Checkpoint := [
    { identifier := "target-mathematics", phase := "initialization", responsibility := "M"
      owner := (root.securityNamespace ++ ".Soundness.false_inputs").toName
      callee := (root.formulaNamespace ++ ".equation").toName, route := .authorLemma },
    { identifier := "root-instantiation", phase := "composition", responsibility := "I"
      owner := (root.securityNamespace ++ ".Soundness.rejectedInputs").toName
      callee := ``ZkcSecurity.Source.Installation.rejected, expectedUses := some 1
      proofObjectHeads := [``Zkc.Obligations.Derivation], route := .generalRule },
    { identifier := "distribution", phase := "preservation", responsibility := "D"
      owner := (root.securityNamespace ++ ".Soundness.rejectedInputs").toName
      callee := ``SourcePublicPrimeField.polynomial_agreement, expectedUses := some 1, route := .familyPackage },
    { identifier := "cost", phase := "cost", responsibility := "I"
      owner := (root.securityNamespace ++ ".Soundness.inputCosts").toName
      callee := ``ZkcSecurity.Source.RootPublic.cost_inputFrame, expectedUses := some 1, route := .generalRule },
    { identifier := "connection", phase := "association", responsibility := "I"
      owner := ``ZkcSecurity.FiatShamir.RootConnection.publicBridge_inputFrame
      callee := ``Zkc.Construction.ConnectionRoot.RootCertificate.simulation
      proofObjectHeads := [``Zkc.Construction.Original.Simulation], route := .generalRule }]
  let proofBindings ← (checkpoints ++ rootCheckpoints).toArray.mapM (fun checkpoint => measured graph checkpoint)
  let mut occurrences := #[]
  let mut obligations := #[]
  for invocation in layout.calls do
    let [sourceCall] := sourceCalls.filter (·.application == invocation.application)
      | throwError "proof-account: ambiguous source occurrence"
    occurrenceAssociation invocation sourceCall
    let [loop] := layout.loops.filter (·.call.application == invocation.application)
      | throwError "proof-account: missing occurrence loop"
    unless loop.maximum == maximum do throwError "proof-account: changed static bound"
    let occurrenceId := root.snapshot.entry ++ "/" ++ invocation.application
    occurrences := occurrences.push <| Json.mkObj [
      ("id", toJson occurrenceId), ("application", toJson invocation.application),
      ("library", toJson invocation.library), ("query_template", toJson (reprStr invocation.query)),
      ("delivery_template", toJson (reprStr invocation.delivery)),
      ("messages", toJson (invocation.messages.map reprStr)), ("maximum", toJson loop.maximum),
      ("source_equation", sourceBinding), ("template_association", template),
      ("root_certificate", rootBinding), ("instantiation", "root-instantiation")]
    for checkpoint in checkpoints do
      obligations := obligations.push <| Json.mkObj [
        ("id", toJson (occurrenceId ++ "/" ++ checkpoint.identifier)),
        ("occurrence", toJson occurrenceId), ("phase", toJson checkpoint.phase),
        ("expected_layer", toJson checkpoint.responsibility), ("route", toJson checkpoint.route.label),
        ("proof_binding", toJson checkpoint.identifier)]
  return Json.mkObj [
    ("format", "zkc.derivation-discharge-account/1"), ("root", toJson receipt.toString),
    ("original_source", toJson root.snapshot.source), ("entry", toJson root.snapshot.entry),
    ("method", "checked-source-properties"), ("attribution_is_proof_status", false),
    ("root_binding", rootBinding), ("source_binding", sourceBinding),
    ("request", requestRecord), ("request_value", toJson (reprStr request)),
    ("source_occurrences", Json.arr occurrences), ("obligations", Json.arr obligations),
    ("proof_bindings", Json.arr proofBindings),
    ("scope", "Actual checked applications shared by nominal occurrences; not receipt status, a minimal dependency set or author effort.")]

end ZkcSecurity.Generation.SumcheckAccounts
