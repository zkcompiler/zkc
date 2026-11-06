import Tests.FriBindingSites
import TestsSecurity.FriSourceExecution

/-! Both applications must be reached and return. They share a sampler with
two different schedules, both with duplicates, and separate publications. -/
namespace TestsSecurity.FriBindingSites
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured.FriSource
open TestsSecurity.FriSourceExecution
open ZkcSecurity.Domains.KoalaBearModel (model)

/-- A virtual Fold's children read this same word at other positions. Only
the direct query records the position supplied to Check for this sample. -/
def directPositions (anchor : OracleAnchor) (events : List (OracleProtocol.Event String)) : List Nat :=
  events.filterMap fun event ↦ match event with
    | .logical (.query request) =>
      if request.anchor == anchor && request.expansion.isEmpty then some request.position else none
    | _ => none

def controls : IO Unit := do
  let .ok subject := Tests.FriBindingSitesView.imported.oracleSubject
    | throw (IO.userError "two-call oracle subject")
  let arguments := inputs (model := model) 1 [] 1 3 8 0
  if same : ZkcExamples.Structured.FriSourceBodies.runSignature.inputs = subject.imported.program.payload.entry.inputs then
    let .ok start := subject.start model 1 (same ▸ arguments) [] (⟨[], {}⟩ : PublishedWords.State model History)
      | throw (IO.userError "two-call root ingress")
    let secondPositions := [0, 0, 31, 24, 6, 6, 2, 29]
    let result := PublishedWords.sourceRunM (m := Id) start (ordinaryWith (positions ++ secondPositions) 0 false)
      (chooser false)
    let .returned outputs := result.outcome | throw (IO.userError "two-call root stopped")
    let read := fun index ↦ do
      let ref ← Var.decode subject.imported.program.payload.entry.outputs .boolean index
      (outputs.get ref).bind ProtocolValue.toConcrete
    let words := result.state.oracle.provider.words
    let anchors := words.map fun word ↦ word.2.anchor
    let [left, right] := (words.filter (·.2.rows == 32)).reverse
      | throw (IO.userError "expected one initial word per call site")
    let firstReads := directPositions left.2.anchor result.events
    let secondReads := directPositions right.2.anchor result.events
    unless firstReads == positions && secondReads == secondPositions do
      throw (IO.userError ("per-site initial queries: " ++ reprStr firstReads ++ ", " ++ reprStr secondReads))
    unless read 0 == some true && read 1 == some true && result.state.parents.isEmpty &&
        result.state.oracle.queries == 192 && result.state.oracle.provider.auxiliary.samples == 16 &&
        words.map (·.2.rows) == [8, 16, 32, 8, 16, 32] && anchors.eraseDups.length == 6 do
      throw (IO.userError ("two-call execution: reads " ++ toString result.state.oracle.queries ++
        ", draws " ++ toString result.state.oracle.provider.auxiliary.samples ++
        ", word rows " ++ toString (words.map (·.2.rows))))
  else throw (IO.userError "two-call input layout")
  IO.println "FRI binding: both sites returned, two distinct sampled schedules, six distinct publications"

#eval controls
end TestsSecurity.FriBindingSites
