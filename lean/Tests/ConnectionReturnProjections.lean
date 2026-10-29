import Tests.SourceConnectionPilot
import ZkcTools.ConstructionBindings.Root
import Zkc.Construction.ConnectionRootRoutes
import Zkc.Construction.ConnectionRouteCoverageRoot
import Zkc.Construction.ConnectionCertificateAdmission

/-! A partial live return from an effectful callee. The unused Boolean is a
pure expression with no physical cell. The index return, receive occurrence,
and stopping helper remain mandatory, including the helper's abort path. -/
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
noncomputable section
namespace Tests.ConnectionReturnProjections
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction ConnectionRoot
open ZkcTools.ConstructionBindings

abbrev gateHelper := Tests.SourceConnectionPilot.gateHelper
abbrev gateBody := Tests.SourceConnectionPilot.gateBody

def workSignature : ProtocolSignature :=
  ⟨"work", ["P", "V"], [.boolean, .index], [.boolean, .index],
    [[0,1], [0,1]], [[0,1], [0,1]]⟩
def runSignature : ProtocolSignature :=
  { workSignature with name := "main", outputs := [.index], outputScopes := [[0,1]] }
def workBody : Region protocolDialect workSignature.inputs workSignature.outputs :=
  .letOp (.mark "helper") .nil .nil <|
  .letOp (.localCall Tests.SourceConnectionPilot.gateHelper rfl 1 "helper")
    (.cons .here (.cons (.there .here) .nil)) .nil <|
  .letOp (.mark "message") .nil .nil <|
  .letOp (.exchange .index 0 1 "message") (.cons (.there (.there .here)) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate .booleanXor rfl)
    (.cons (.there (.there .here)) (.cons (.there (.there .here)) .nil)) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))
def runBody : Region protocolDialect runSignature.inputs runSignature.outputs :=
  .letOp (.mark "work") .nil .nil <|
  .letOp (.protocolApply workSignature [0,1] "work") (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons (.there .here) .nil)

private def protocol (signature : ProtocolSignature) (body : Block) : Definition :=
  .function ⟨signature.name, .protocol, .publicDef, signature.inputs, signature.outputs,
    some ⟨["P", "V"], signature.inputScopes.map (List.map fun i => ["P", "V"].getD i ""),
      signature.outputScopes.map (List.map fun i => ["P", "V"].getD i "")⟩,
    [], some (.protocol ⟨signature.name, []⟩), body⟩

def snapshot : Snapshot := { Tests.SourceConnectionPilot.snapshot with
  definitions := Tests.SourceConnectionPilot.snapshot.definitions.take 1 ++ [
    protocol workSignature (.block [
      .instruction (.localCall "gate" "V") [0,1] [.index] [] "helper",
      .instruction (.exchange "P" "V") [2] [.index] [] "message",
      .instruction .booleanXor [2,2] [.boolean] [] ""] (.ret [0,1])),
    protocol runSignature (.block [
      .instruction (.protocolApply "work" ["P", "V"]) [0,1] [.boolean, .index] [] "work"] (.ret [1]))]
  contracts := [⟨"work", []⟩, ⟨"main", []⟩] }
structured_views snapshot helpers [gate] protocols [work, run]
example : Structured.check snapshot = .ok program := kernel_admission

def context : Context := .plain "main" ["P", "V"] 0 1
def policy : Policy := ⟨"main", "P", "V", 0, "", [], [0,1], [], "zkc.framed/0", ""⟩
def messageSite := qualifyProtocolSite (some "work") "message"
def artifact : Participant :=
  ⟨snapshot.source, snapshot.source, policy, "main.V", [.data .boolean, .data .index], [.data .index],
    [⟨.call "gate", [0,1], [.data .index], []⟩,
      ⟨.receive messageSite messageSite "P" .index, [], [.data .index], []⟩], [3], []⟩
def routing : Original.Routing :=
  ConnectionRootRoutes.routing program.snapshot context .validator [] artifact (by decide +kernel)
def target : ConnectionCertificate.Block := fun model =>
  Domain.View.sequence (Domain.View.helper model program "gate" [0,1] [.data .index]) <|
  Domain.View.sequence (Domain.View.receive messageSite messageSite "P" .index [.data .index]) Domain.View.empty
theorem target_eq (model : DomainModel) : Domain.Correspondence.Block
    (model := model) (program := program) (context := context) artifact.instructions (target model) := by
  apply Domain.Correspondence.sequence (Domain.Correspondence.helper _ _ _)
  exact Domain.Correspondence.sequence (Domain.Correspondence.receive _ _ _ _ _) Domain.Correspondence.empty
def library : ConnectionLibrary.Bundle program.payload := by derive_connection_library roles [1]
def root : RootCertificate program routing 1 artifact := by
  derive_root_connection_with_library target target correspondence target_eq services [] library library
example (model : DomainModel) (seed : Nat) :
    root.source model [.data (.boolean false), .data (.index seed)] = .halt .abort := by kernel_rfl

def facts := root.facts
theorem connected : SourceConnection.Connected program routing 1 root.inputs.abi artifact :=
  SourceConnection.ofRootCertificate root (by rfl)

-- The checked finite data can omit the first result, but cannot omit the
-- index that this caller returns. No semantic simplifier discharges this check.
def partialSelection : ConnectionReturnProjection.Selection [.boolean, .index] := .cons false (.cons true .nil)
def noneSelected : ConnectionReturnProjection.Selection [.boolean, .index] := .cons false (.cons false .nil)
def next : Form [] [] [.tuple [.boolean, .index]] [.index] :=
  .done (.cons (.read .here (.there .here)) .nil)
example : ConnectionReturnProjection.continuation partialSelection next = next := by kernel_rfl
example : ConnectionReturnProjection.continuation noneSelected next ≠ next := by
  intro same
  cases same

abbrev Candidate (view : ConnectionCertificate.Block) :=
  ConnectionCertificate.Derivation routing {} program.payload.definitions library.keys
    program.payload.entry.outputs 1 program.payload.entry.outputScopes root.output.locations
    root.output.historyReference [] root.inputs.layout root.alignment.form view
    (selection := .selected program.payload rfl library.library)

-- The projection cannot omit a reached partial helper, change the occurrence,
-- invent the selected live value, or erase the root's complete return.
def omittedHelper : ConnectionCertificate.Block := fun _ =>
  Domain.View.sequence (Domain.View.receive messageSite messageSite "P" .index [.data .index]) Domain.View.empty
def changedOccurrence : ConnectionCertificate.Block := fun model =>
  Domain.View.sequence (Domain.View.helper model program "gate" [0,1] [.data .index]) <|
  Domain.View.sequence (Domain.View.receive "changed" "changed" "P" .index [.data .index]) Domain.View.empty
/-- error: alignment-callee-slice-refused: alignment-return-or-view-mismatch -/
#guard_msgs (substring := true) in
example : Candidate omittedHelper := by derive_connection_alignment
/-- error: alignment-callee-slice-refused: alignment-return-or-view-mismatch -/
#guard_msgs (substring := true) in
example : Candidate changedOccurrence := by derive_connection_alignment
/-- error: alignment-callee-slice-refused: alignment-return-or-view-mismatch -/
#guard_msgs (substring := true) in
example : RootCertificate program routing 1 { artifact with returned := [1] } := by
  derive_root_connection_with_library target target correspondence target_eq services [] library library

-- A completely ignored return keeps the same helper, receive and stop spine.
def ignoredNext : Form [] [] [.tuple [.boolean, .index]] [] := .done .nil
example : ConnectionReturnProjection.continuation noneSelected ignoredNext = ignoredNext := by kernel_rfl
example : ConnectionReturnProjection.form noneSelected
    (.halt .abort : Form [] [] [] [.boolean, .index]) = .halt .abort := rfl

#print axioms ConnectionReturnProjection.form_denote
#print axioms ConnectionReturnProjection.bind_continuation
#print axioms root
#print axioms facts
#print axioms connected
end Tests.ConnectionReturnProjections
