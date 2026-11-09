module

public import Zkc.Tests.IR.IndexServiceCertificateControls
public meta import Lean.Elab.Command

/-! Rejected proposals retain structural diagnostics. Resource failures do not
count as refusal, and no proof of a mutated connection is installed. -/
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 12000000
namespace Tests.IndexServiceCertificateRefusals
open Zkc.Source Zkc.Source.Structured Zkc.Construction Tests.IndexServices
open Tests.IndexServiceCertificateControls

-- A refusal must be a structural error, never resource exhaustion. Keep the
-- actual diagnostic as evidence instead of accepting any failed tactic run.
public meta section
open Lean Meta Elab Command
-- Keep literal diagnostic text without forcing expression/goal pretty
-- printing, which can unfold the entire rejected dependent derivation.
partial def diagnosticText : MessageData → String
  | .ofFormatWithInfos formatted => formatted.fmt.pretty
  | .compose left right => diagnosticText left ++ diagnosticText right
  | .withContext _ message | .withNamingContext _ message | .nest _ message
  | .group message | .tagged _ message | .ofWidget _ message
  | .ofOriginatingSyntax _ message => diagnosticText message
  | .trace _ message children => diagnosticText message ++
      String.join (children.toList.map diagnosticText)
  | .ofGoal _ => "<goal>"
  | .ofLazy .. => "<expression>"

syntax "refused_service_connection " str " : " term : command
elab_rules : command
  | `(refused_service_connection $label:str : $type:term) => liftTermElabM do
    ZkcTools.ConstructionBindings.Alignment.tracePhase s!"refusal start {label.getString}"
    let saved ← saveState
    let failure ← try
      Term.withoutErrToSorry do
        let expected ← Term.elabType type
        let _ ← Term.elabTerm (← `(by derive_source_connection)) (some expected)
        Term.synthesizeSyntheticMVarsNoPostponing
        pure none
      catch error =>
        if error.isRuntime || error.isInterrupt || error.isMaxRecDepth then throw error
        ZkcTools.ConstructionBindings.Alignment.tracePhase s!"refusal caught {label.getString}"
        pure (some (diagnosticText error.toMessageData))
    saved.restore
    ZkcTools.ConstructionBindings.Alignment.tracePhase s!"refusal restored {label.getString}"
    let some reason := failure | throwError "mutation was unexpectedly proposed: {label.getString}"
    for forbidden in ["heartbeat", "recursion", "timeout", "interrupted", "memory"] do
      if (reason.splitOn forbidden).length > 1 then
        throwError "mutation refused only by resource failure: {reason}"
    unless ["alignment-", "connection-view-proposal:", "root-"].any
        (fun code => (reason.splitOn code).length > 1) do
      throwError "mutation lacked a structural refusal diagnostic: {reason}"
    logInfo m!"SERVICE-CERTIFICATE-REFUSAL {label.getString}: {reason}"
end

refused_service_connection "request" :
  ConnectionAdmission.Required Scalar.program Scalar.context .validator wrongRequest
refused_service_connection "reference" :
  ConnectionAdmission.Required Scalar.program Scalar.context .validator wrongReference
refused_service_connection "reference-count" :
  ConnectionAdmission.Required Scalar.program Scalar.context .validator wrongArity
refused_service_connection "count" :
  ConnectionAdmission.Required Block.program Block.context .validator wrongCount
refused_service_connection "ancestry" :
  ConnectionAdmission.Required Repeated.program Repeated.context .validator wrongAncestry
refused_service_connection "role" :
  ConnectionAdmission.Required Scalar.program Scalar.context .producer Scalar.Validator.participant

end Tests.IndexServiceCertificateRefusals
