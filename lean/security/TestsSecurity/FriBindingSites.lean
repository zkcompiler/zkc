import Tests.FriBindingSites
import TestsSecurity.FriSourceExecution

/-! Both applications must be reached and return. They share a sampler with
repeated positions but create separate nominal publication histories. -/
namespace TestsSecurity.FriBindingSites
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured.FriSource
open TestsSecurity.FriSourceExecution
open ZkcSecurity.Domains.KoalaBearModel (model)

def controls : IO Unit := do
  let .ok subject := Tests.FriBindingSitesView.imported.oracleSubject
    | throw (IO.userError "two-call oracle subject")
  let arguments := inputs (model := model) 1 [] 1 3 8 0
  if same : ZkcExamples.Structured.FriSourceBodies.runSignature.inputs = subject.imported.program.payload.entry.inputs then
    let .ok start := subject.start model 1 (same ▸ arguments) [] (⟨[], {}⟩ : PublishedWords.State model History)
      | throw (IO.userError "two-call root ingress")
    let result := PublishedWords.sourceRunM (m := Id) start (ordinaryWith (positions ++ positions) 0 false) (chooser false)
    let .returned outputs := result.outcome | throw (IO.userError "two-call root stopped")
    let read := fun index ↦ do
      let ref ← Var.decode subject.imported.program.payload.entry.outputs .boolean index
      (outputs.get ref).bind ProtocolValue.toConcrete
    let words := result.state.oracle.provider.words
    let anchors := words.map fun word ↦ word.2.anchor
    unless read 0 == some true && read 1 == some true && result.state.parents.isEmpty &&
        result.state.oracle.queries == 192 && result.state.oracle.provider.auxiliary.samples == 16 &&
        words.map (·.2.rows) == [8, 16, 32, 8, 16, 32] && anchors.eraseDups.length == 6 do
      throw (IO.userError ("two-call execution: reads " ++ toString result.state.oracle.queries ++
        ", draws " ++ toString result.state.oracle.provider.auxiliary.samples ++
        ", word rows " ++ toString (words.map (·.2.rows))))
  else throw (IO.userError "two-call input layout")
  IO.println "FRI binding: both sites returned, 16 samples, six distinct publications"

#eval controls
end TestsSecurity.FriBindingSites
