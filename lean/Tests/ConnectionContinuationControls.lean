import Tests.ConnectionRetainedRoots
import Tests.ConnectionNestedApplications
import Tests.ConnectionContinuationMutation

/-! Controls change complete actual roots. Refusing source folds do not supply
coverage, and target output selection never weakens the nominal return row. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
set_option linter.unusedTactic false
noncomputable section
namespace Tests.ConnectionContinuationControls
open Zkc.Source Zkc.Source.Structured Zkc.Construction ConnectionRoot
open ZkcTools.ConstructionBindings
open Tests.ConnectionRetainedRoots
open Tests.ConnectionContinuationMutation

meta section
open Lean in
private partial def staticFailureText : MessageData → String
  | .ofFormatWithInfos format => format.fmt.pretty
  | .withContext _ message | .withNamingContext _ message | .ofWidget _ message
  | .nest _ message | .group message | .tagged _ message | .ofOriginatingSyntax _ message =>
      staticFailureText message
  | .compose left right => staticFailureText left ++ staticFailureText right
  | .trace _ message children => staticFailureText message ++
      String.join (children.toList.map staticFailureText)
  | _ => ""

open Lean Elab Tactic in
elab "expect_connection_refusal" label:str " because " expected:str body:tacticSeq : tactic => do
  let trace ← IO.getEnv "ZKC_CONNECTION_CONTROL_TRACE"
  if let some path := trace then
    IO.FS.withFile path .append fun file => file.putStrLn s!"begin: {label.getString}"
  let saved ← saveState
  let failure ← try
    Term.withoutErrToSorry <| withoutRecover <| evalTactic body
    pure none
  catch exception =>
    if exception.isRuntime || exception.isInterrupt then throw exception
    pure (some exception.toMessageData)
  saved.restore
  let some failure := failure | throwError "expected refusal: {label.getString}"
  if failure.hasTag (fun name => (`runtime).isPrefixOf name) then
    throwError "resource exhaustion is not a checked refusal: {label.getString}"
  -- Do not delaborate expression/goal holes: their diagnostic trees can dwarf
  -- the checked proof. Runtime tags and static error text retain refusal causes.
  let text := staticFailureText failure
  for limit in ["maximum number of heartbeats", "deterministic timeout", "recursion depth", "out of memory"] do
    if (text.splitOn limit).length > 1 then
      throwError "resource exhaustion is not a checked refusal: {label.getString}"
  unless (text.splitOn expected.getString).length > 1 do
    throwError "wrong refusal cause for {label.getString}: expected {expected.getString}, got {text}"
  let reason := String.ofList (text.toList.take 700)
  logInfo m!"checked_refusal: {label.getString}; reason={reason}"
  if let some path := trace then
    IO.FS.withFile path .append fun file => file.putStrLn s!"checked: {label.getString}; reason={reason}"

end

def missingRoutes : Original.Routing := {Small.validatorRouting with messages := []}
example : True := by
  expect_connection_refusal "missing retained routes" because "alignment-route-request-history-coordinate-or-operand-mismatch"
    have refused : RootCertificate Small.program missingRoutes 1 Small.validatorArtifact := by
      derive_root_connection_with_library
        target (fun model => ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.body model Small.program Small.context)
        correspondence (fun model => ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.body_eq model Small.program Small.context)
        services Small.capabilities library Small.library
  trivial

-- The old physical transcript has the right nominal sort but the wrong history.
def staleHistory : Participant := {Small.validatorArtifact with returned :=
  Small.validatorArtifact.returned.dropLast ++ [Small.validatorArtifact.inputs.findIdx
    (fun | .transcript _ => true | _ => false)]}
example : True := by
  expect_connection_refusal "stale retained history selector" because "alignment-"
    have refused : RootCertificate Small.program Small.validatorRouting 1 staleHistory := by
      derive_root_connection_with_library
        target (fun model => ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.body model Small.program Small.context)
        correspondence (fun model => ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.body_eq model Small.program Small.context)
        services Small.capabilities library Small.library
  trivial

def lostResult : Participant := {Small.validatorArtifact with returned := Small.validatorArtifact.returned.tail}
example : (ConnectionInstallation.ReturnLayout.build Small.program.payload.entry.signature
    Small.validatorRouting.context 1 lostResult).isOk = false := by decide +kernel
-- This finite refusal is checked directly. An arbitrary tactic error (for
-- example an unrelated elaboration error) is not additional refusal evidence.

example : True := by
  expect_connection_refusal "stale source library" because "Type mismatch"
    have staleLibrary : ConnectionLibrary.Bundle changedProgram.payload := Tests.ConnectionNestedApplications.library
  trivial
example : True := by
  expect_connection_refusal "changed admitted callee body" because "alignment-guard-mismatch"
    have refused : RootCertificate changedProgram changedRouting 1 Tests.ConnectionNestedApplications.artifact := by
      derive_root_connection_with_library
        target Tests.SourceConnectionPilot.rootView
        correspondence changedCorrespondence
        services Tests.ConnectionNestedApplications.capabilities library changedLibrary
  trivial

private def changeSignature (entry : String) : Definition → Definition
  | .function source => if source.kind == .protocol && source.name != entry then
      .function {source with inputs := source.inputs.tail}
    else .function source
  | other => other
example : (Structured.check {Small.program.snapshot with definitions := (
    Small.program.snapshot.definitions.map (changeSignature Small.program.snapshot.entry))}).isOk = false :=
  by decide +kernel

private def dropCalleeResult (entry : String) : Definition → Definition
  | .function source => if source.kind == .protocol && source.name != entry then
      .function {source with outputs := source.outputs.tail}
    else .function source
  | other => other
example : (Structured.check {Small.program.snapshot with definitions := (
    Small.program.snapshot.definitions.map (dropCalleeResult Small.program.snapshot.entry))}).isOk = false :=
  by decide +kernel

private def shortenCall : Zkc.Source.Structured.Instruction → Zkc.Source.Structured.Instruction
  | .instruction (.protocolApply name roles) operands results regions site =>
      .instruction (.protocolApply name roles) operands.tail results regions site
  | instruction => instruction

private def malformedEntry (entry : String) : Definition → Definition
  | .function source => if source.name == entry then
      match source.body with
      | .block instructions terminator =>
          .function {source with body := .block (instructions.map shortenCall) terminator}
    else .function source
  | other => other

example : (Structured.check {Small.program.snapshot with definitions := (
    Small.program.snapshot.definitions.map (malformedEntry Small.program.snapshot.entry))}).isOk = false :=
  by decide +kernel

namespace Nested
abbrev original := Tests.ConnectionNestedApplications.routing
def reordered : Original.Routing := {original with messages := (original.messages.map
  (fun template => {template with steps := template.steps.reverse}))}
example : True := by
  expect_connection_refusal "nested occurrence order" because "alignment-route-request-history-coordinate-or-operand-mismatch"
    have refused : RootCertificate Tests.ConnectionNestedApplications.program reordered 1
        Tests.ConnectionNestedApplications.artifact := by
      derive_root_connection_with_library
        target Tests.SourceConnectionPilot.rootView
        correspondence Tests.SourceConnectionPilot.body_view
        services Tests.ConnectionNestedApplications.capabilities library Tests.ConnectionNestedApplications.library
  trivial
end Nested
end Tests.ConnectionContinuationControls
