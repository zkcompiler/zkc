import Tests.ConnectionNestedApplications
import Zkc.Source.Structured.UnitViews

/-! A changed actual admitted callee with a frozen checked payload. The target
instruction correspondence is checked separately before testing source refusal. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
noncomputable section
namespace Tests.ConnectionContinuationMutation
open Zkc.Source Zkc.Source.Structured Zkc.Construction ConnectionRoot
open ZkcTools.ConstructionBindings
private def changeGuard : Zkc.Source.Structured.Instruction → Zkc.Source.Structured.Instruction
  | .instruction (.guard "V") operands results regions site =>
      .instruction (.guard "P") operands results regions site
  | instruction => instruction

private def changeCallee (entry : String) : Definition → Definition
  | .function source => if source.kind == .protocol && source.name != entry then
      match source.body with
      | .block instructions terminator =>
          .function {source with body := .block (instructions.map changeGuard) terminator}
    else .function source
  | other => other

def changedSnapshot : Snapshot := {Tests.ConnectionNestedApplications.program.snapshot with definitions := (
  Tests.ConnectionNestedApplications.program.snapshot.definitions.map
    (changeCallee Tests.ConnectionNestedApplications.program.snapshot.entry))}
namespace Checked
private def changedStepBody : Region protocolDialect Tests.SourceConnectionPilot.stepInputs
    Tests.SourceConnectionPilot.stateTypes :=
  .letOp (.mark "guard") .nil .nil <|
  .letOp (.guard 0 "guard") (.cons .here .nil) .nil <|
  .letOp (.mark "helper") .nil .nil <|
  .letOp (.localCall Tests.SourceConnectionPilot.gateHelper rfl 1 "helper")
    (.cons (.there .here) (.cons (.there (.there .here)) .nil)) .nil <|
  .letOp (.mark "message") .nil .nil <|
  .letOp (.exchange .index 0 1 "message") (.cons (.there (.there (.there .here))) .nil) .nil <|
  .ret (.cons .here .nil)
structured_views changedSnapshot
  helpers [gate := Tests.SourceConnectionPilot.gate]
  protocols [step := (Tests.SourceConnectionPilot.stepSignature, changedStepBody),
    run := Tests.SourceConnectionPilot.run]
end Checked
abbrev changedProgram := Checked.program
example : Structured.check changedSnapshot = .ok changedProgram := Checked.kernel_admission
def changedLibrary : ConnectionLibrary.Bundle changedProgram.payload := by derive_connection_library

def changedRouting : Original.Routing :=
  ConnectionRootRoutes.routing changedSnapshot Tests.ConnectionNestedApplications.context .validator
    Tests.ConnectionNestedApplications.capabilities Tests.ConnectionNestedApplications.artifact (by decide +kernel)

-- The actual original target still has a checked instruction correspondence.
-- Refusal below therefore tests the changed source alignment.
theorem changedCorrespondence (model : DomainModel) :
    Domain.Correspondence.Block (program := changedProgram)
      (context := Tests.ConnectionNestedApplications.context)
      Tests.ConnectionNestedApplications.artifact.instructions
      (Tests.SourceConnectionPilot.rootView model) := by
  repeat first
    | exact Domain.Correspondence.empty
    | apply Domain.Correspondence.sequence
    | apply Domain.Correspondence.loop
    | exact Domain.Correspondence.guard _ _ _
    | exact Domain.Correspondence.helper _ _ _
    | exact Domain.Correspondence.receive _ _ _ _ _

#print axioms Checked.kernel_admission
end Tests.ConnectionContinuationMutation
