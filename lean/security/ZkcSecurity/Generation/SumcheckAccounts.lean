module

public import ZkcTools.ProofAccount
public import ZkcSecurity.Realizations.Sumcheck.ArtifactBinding
public import ZkcSecurity.Realizations.Sumcheck.OriginalRawComposition
public import ZkcSecurity.Families.Sumcheck.TableComponentPrimeField
public import ZkcSecurity.Generation.OriginalSecurityBindings
public meta import ZkcSecurity.Generation.OriginalSecurityBindings
public import ZkcSecurity.Generation.Roots.Catalogue
public meta import ZkcSecurity.Generation.Roots.Catalogue

/-! The installed table method's measurement vocabulary. These selections do
not prove anything: the inspector must find each application in an actual
receipt's dependency graph. Shared proof uses are counted once and associated
with generated source occurrences, not counted as newly authored proofs.
-/

public meta section
namespace ZkcSecurity.Generation.SumcheckAccounts
open Lean Meta Elab Term
open ZkcTools.ProofAccount
open ZkcSecurity.Families.Sumcheck
open ZkcSecurity.Realizations.Sumcheck

def checkpoints : List Checkpoint := [
  { identifier := "initialization", phase := "initialization", responsibility := "M"
    owner := ``TableComponent.Execution.run_residual, callee := ``Consumers.residual
    selection := .lastArgument, route := .familyPackage },
  { identifier := "preservation", phase := "preservation", responsibility := "M"
    owner := ``Consumers.residual, callee := ``false_round, route := .familyPackage },
  { identifier := "exit", phase := "exit", responsibility := "I"
    owner := ``Consumers.residual, callee := ``Zkc.Obligations.Derivation.done
    selection := .lastArgument, route := .generalRule },
  { identifier := "frame", phase := "frame", responsibility := "I"
    owner := ``TableComponent.Execution.run_residual
    callee := ``Zkc.Obligations.Derivation.frameReturns
    proofObjectHeads := [``Zkc.Obligations.Derivation], route := .generalRule },
  { identifier := "terminal", phase := "terminal", responsibility := "M"
    owner := ``OriginalRaw.root_rejected, callee := ``OriginalRaw.terminal_rejected
    proofObjectHeads := [``Zkc.Obligations.Derivation], route := .familyPackage }]

private def dataTerm (stx : Syntax) : TermElabM Expr := do
  let term ← elabTerm stx none
  synthesizeSyntheticMVarsNoPostponing
  return ← instantiateMVars term

private unsafe def stringValue (stx : Syntax) : TermElabM String := do
  let term ← dataTerm stx
  evalExpr String (mkConst ``String) (← withTransparency .all (reduce term))

def requireSame (actual expected : Expr) : MetaM Unit := do
  unless ← withTransparency .all (isDefEq actual expected) do
    throwError "proof-account: typed association mismatch"

/-- Both the complete imported snapshot and its diagnostic source identity
must agree with the catalogue selection. No digest grants proof authority. -/
unsafe def sourceAssociation (root : Roots.Selection) : TermElabM Unit := do
  let actual := mkIdent ((root.subjectModule ++ ".original").toName)
  let expected := mkIdent ((root.sourceModule ++ ".program").toName)
  let lhs ← dataTerm (← `($actual))
  let rhs ← dataTerm (← `(($expected).snapshot))
  requireSame lhs rhs
  let snapshot ← evalExpr Zkc.Source.Structured.Snapshot
    (mkConst ``Zkc.Source.Structured.Snapshot)
    (← withTransparency .all (reduce rhs))
  unless reprStr snapshot == reprStr root.snapshot do
    throwError "proof-account: catalogue snapshot differs from the checked source"
  let source ← stringValue (← `(($actual).source))
  let entry ← stringValue (← `(($actual).entry))
  unless source == root.snapshot.source && entry == root.snapshot.entry do
    throwError "proof-account: stale source identity or entry"

private def declarationRecord (graph : Reachability) (name : Name) : MetaM Json := do
  let path ← graph.require name
  let info ← getConstInfo name
  return Json.mkObj [
    ("declaration", toJson name.toString),
    ("root_path", toJson (path.map Name.toString)),
    ("type", toJson (← ppExpr info.type).pretty)]

/-- Check the full call equation, including its telescope, operands, bound and
nominal occurrence. Merely mentioning these declarations is not an association.
This is the installed method's expected equation, not a new semantic authority. -/
def occurrenceAssociation (graph : Reachability) (proof step occurrence : Name)
    (maximum : Nat) : TermElabM Json := do
  let record ← declarationRecord graph proof
  let info ← getConstInfo proof
  let step := mkIdent step
  let occurrence := mkIdent occurrence
  let expected ← dataTerm (← `(∀ {F G : Type} [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] [DecidableEq G] (scalar : F) (count handle : Nat),
    $step (F := F) (G := G) (some scalar) (some count) (some handle) =
      if count ≤ $(quote maximum) then
        (OriginalRaw.run (G := G) ⟨($occurrence).protocol, handle⟩
          (List.range count) ⟨[], scalar⟩).bind
          (fun result => .done (OriginalRaw.output result))
      else .halt .refused))
  requireSame info.type expected
  return record

/-- Measure the installed method on the actual receipt. Root occurrences come
from admission and the existing ABI analyzer; no second protocol list or
handwritten occurrence numbering is maintained here. -/
unsafe def measure (root : Roots.Selection) (receipt : Name) : TermElabM Json := do
  sourceAssociation root
  let program ← match Zkc.Source.Structured.check root.snapshot with
    | .ok program => pure program
    | .error reason => throwError "proof-account: {reason}"
  let binding ← match OriginalSecurityBindings.analyze program root.artifacts.validator root.artifacts.producer with
    | .ok binding => pure binding
    | .error reason => throwError "proof-account: {reason}"
  let layout ← match ZkcTools.ConstructionBindings.analyze program root.artifacts.validator with
    | .ok layout => pure layout
    | .error reason => throwError "proof-account: {reason}"
  let graph ← reachable receipt
  let _ ← graph.require ((root.subjectModule ++ ".validatorSubject").toName)
  let rootBinding ← declarationRecord graph ((root.securityModule ++ ".Sources.source_root").toName)
  let actualBridge ← declarationRecord graph ((root.securityModule ++ ".Sources.bridge").toName)
  let requestName := (root.subjectModule ++ "SoundnessClaims.request1Data").toName
  let requestRecord ← declarationRecord graph requestName
  let request ← evalExpr Zkc.Claims.Wire.Request (mkConst ``Zkc.Claims.Wire.Request)
    (← withTransparency .all (reduce (mkConst requestName)))
  let requestValue := reprStr request
  let dischargers ← checkpoints.toArray.mapM (fun checkpoint => account graph checkpoint)
  let authored ← account graph {
    identifier := "target-mathematics", phase := "initialization", responsibility := "M"
    owner := (root.securityModule ++ ".Soundness.rejectedInputs").toName
    callee := (root.formulaNamespace ++ ".equation").toName, route := .authorLemma }
  let schedule (index : Nat) := (root.securityModule ++ ".Sources.schedule" ++ toString index).toName
  let input (index : Nat) := ArgumentValue.binder ("input" ++ toString index).toName
  let some first := binding.calls.head? | throwError "proof-account: missing call"
  let common : List ArgumentBinding := [⟨`maximum, .natural binding.maximum⟩, ⟨`count, input binding.count⟩]
  let (rootCallee, arguments) := if binding.calls.length == 1 then
    (``OriginalRaw.root_rejected, common ++ [⟨`schedule, .declaration (schedule 0)⟩,
      ⟨`raw, input first.raw⟩, ⟨`scalar, input first.claim⟩])
    else
      let second := binding.calls[1]?.getD first
      (``OriginalRaw.twoRoots_rejected, common ++ [
        ⟨`leftSchedule, .declaration (schedule 0)⟩, ⟨`rightSchedule, .declaration (schedule 1)⟩,
        ⟨`left, input first.raw⟩, ⟨`right, input second.raw⟩,
        ⟨`leftClaim, input first.claim⟩, ⟨`rightClaim, input second.claim⟩])
  let instantiation ← account graph {
    identifier := "root-instantiation", phase := "composition", responsibility := "I"
    owner := (root.securityModule ++ ".Soundness.rejectedInputs").toName, callee := rootCallee
    arguments, expectedUses := some 1, proofObjectHeads := [``Zkc.Obligations.Derivation], route := .familyPackage }
  let sampling ← account graph {
    identifier := "conditional-sampling", phase := "preservation", responsibility := "D"
    owner := (root.securityModule ++ ".Soundness.rejectedInputs").toName
    callee := ``TableComponent.PrimeField.conditionalWithFrame, expectedUses := some 1, route := .familyPackage }
  let cost ← account graph {
    identifier := "cost", phase := "cost", responsibility := "I"
    owner := (root.securityModule ++ ".Soundness.inputCosts").toName
    callee := if binding.calls.length == 1 then ``OriginalRaw.root_cost else ``OriginalRaw.twoRoots_cost
    expectedUses := some 1, route := .familyPackage }
  let mut proofBindings := dischargers ++ #[authored, instantiation, sampling, cost]
  let mut occurrences := #[]
  let mut obligations := #[]
  for invocation in binding.calls do
    let index := invocation.occurrence
    let some nominal := layout.calls[index]?
      | throwError "proof-account: missing nominal occurrence"
    let occurrence := ("ZkcSecurity.Examples.Generated.OriginalArtifacts." ++ root.name ++
      ".occurrence" ++ toString index).toName
    let step := ("ZkcExamples.Structured.Generated.Original." ++ root.name ++ "." ++
      invocation.call.name ++ "Realized").toName
    let proof := (root.securityModule ++ ".Sources.call" ++ toString index ++ "_raw").toName
    let sourceProof ← occurrenceAssociation graph proof step occurrence binding.maximum
    let occurrenceIdent := mkIdent occurrence
    let nominalValue ← mkAppM ``ArtifactBinding.Occurrence.mk
      #[mkStrLit root.snapshot.entry, mkStrLit nominal.library, mkStrLit nominal.application]
    requireSame (← dataTerm (← `($occurrenceIdent))) nominalValue
    let branchId := "branch-" ++ toString index
    if binding.calls.length == 2 then
      proofBindings := proofBindings.push (← account graph {
        identifier := branchId, phase := "composition", responsibility := "I"
        owner := ``OriginalRaw.twoRoots_rejected, callee := ``OriginalRaw.root_rejected
        arguments := [⟨`schedule, .binder (if index == 0 then `leftSchedule else `rightSchedule)⟩]
        expectedUses := some 1, proofObjectHeads := [``Zkc.Obligations.Derivation], route := .generalRule })
    let occurrenceId := root.snapshot.entry ++ "/" ++ nominal.application
    occurrences := occurrences.push <| Json.mkObj [
      ("id", toJson occurrenceId), ("application", toJson nominal.application),
      ("library", toJson nominal.library), ("source_step", toJson step.toString),
      ("nominal_occurrence", toJson occurrence.toString),
      ("context", toJson invocation.call.context), ("equation", sourceProof),
      ("instantiation", "root-instantiation"),
      ("branch_binding", if binding.calls.length == 2 then toJson branchId else Json.null)]
    for checkpoint in checkpoints do
      obligations := obligations.push <| Json.mkObj [
        ("id", toJson (occurrenceId ++ "/" ++ checkpoint.identifier)),
        ("occurrence", toJson occurrenceId), ("phase", toJson checkpoint.phase),
        ("expected_layer", toJson checkpoint.responsibility),
        ("route", toJson checkpoint.route.label),
        ("proof_binding", toJson checkpoint.identifier)]
  return Json.mkObj [
    ("format", "zkc.derivation-discharge-account/0"), ("root", toJson receipt.toString),
    ("original_source", toJson root.snapshot.source), ("entry", toJson root.snapshot.entry),
    ("method", "installed-table-residual"), ("attribution_is_proof_status", false),
    ("root_binding", rootBinding), ("bridge", actualBridge),
    ("request", requestRecord), ("request_value", toJson requestValue),
    ("source_occurrences", Json.arr occurrences), ("obligations", Json.arr obligations),
    ("proof_bindings", Json.arr proofBindings),
    ("inventory_policy", "Structural/helper proposal inventories are separate; no open row is promoted by this account."),
    ("scope", "Conditional checked library applications, shared by source invocations; not a minimal dependency or author-effort count.")]

end ZkcSecurity.Generation.SumcheckAccounts
