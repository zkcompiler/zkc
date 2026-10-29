module

public import ZkcSecurity.Source.PairRouting
public import ZkcSecurity.FiatShamir.RootConnectionExecution
public import Zkc.Construction.ConnectionRouteCoverageRoot

@[expose] public section

/-! Install source-pair mathematics through the stable generated root API.
Each root contributes its independent reached-source coverage and full return
simulation. No authored route coverage or whole-program equality is accepted.
-/
set_option autoImplicit false
namespace ZkcSecurity.Source.RootPair
open Zkc.Source Zkc.Source.Structured Zkc.Construction ConnectionRoot ConnectionInputs
open ZkcSecurity.FiatShamir

variable {program : Program} {routingP routingV : Original.Routing} {roleP roleV : Nat}
  {artifactP artifactV : Participant}

/-- Keep source-body evaluation opaque when installing a decoded source row.
Only the input ABI is evaluated by an instance; no source equation is assumed. -/
theorem occurrence_of_read
    (root : RootCertificate program routingP roleP artifactP)
    (model : DomainModel) (physical : Domain.Environment model.toCarriers)
    (values : Values (Component model.Value) program.payload.entry.inputs)
    (read : root.inputs.abi.read physical program.payload.entry.inputs = some values) :
    root.occurrenceSource model physical = Occurrence.participant model program roleP values := by
  simp only [RootCertificate.occurrenceSource, read]

theorem sourceReadback
    (producer : RootCertificate program routingP roleP artifactP)
    (validator : RootCertificate program routingV roleV artifactV)
    (model : DomainModel) (inputsP inputsV : Domain.Environment model.toCarriers)
    (scope : PairScope)
    (laws : Pair.FoldLaws (carriers := model.toCarriers) scope routingP routingV)
    (Post : Values (Component model.Value) program.payload.entry.outputs →
      Values (Component model.Value) program.payload.entry.outputs → Prop)
    (paired : Pair scope Post (producer.occurrenceSource model inputsP)
      (validator.occurrenceSource model inputsV))
    (initial : producer.inputs.initial inputsP = validator.inputs.initial inputsV) :
    Readback (fun p v => Post p.1 v.1 ∧ p.2 = v.2)
      (producer.source model inputsP) (validator.source model inputsV) := by
  rw [producer.source_eq_fold, validator.source_eq_fold, initial]
  exact paired.fold laws _ [] []
    (by simpa only [InputLayout.initial] using producer.routeCoverage model inputsP)
    (by simpa only [InputLayout.initial] using validator.routeCoverage model inputsV)

theorem artifacts
    (producer : RootCertificate program routingP roleP artifactP)
    (validator : RootCertificate program routingV roleV artifactV)
    (model : DomainModel) (inputsP inputsV : Domain.Environment model.toCarriers)
    (scope : PairScope)
    (laws : Pair.FoldLaws (carriers := model.toCarriers) scope routingP routingV)
    (Post : Values (Component model.Value) program.payload.entry.outputs →
      Values (Component model.Value) program.payload.entry.outputs → Prop)
    (paired : Pair scope Post (producer.occurrenceSource model inputsP)
      (validator.occurrenceSource model inputsV))
    (initial : producer.inputs.initial inputsP = validator.inputs.initial inputsV) :
    Readback (fun actualP actualV => ∃ sourceP sourceV,
      (Post sourceP.1 sourceV.1 ∧ sourceP.2 = sourceV.2) ∧
      Original.CompleteReturns program.payload.entry.signature routingP.context roleP artifactP sourceP actualP ∧
      Original.CompleteReturns program.payload.entry.signature routingV.context roleV artifactV sourceV actualV)
      (Domain.participant model program routingP.context artifactP inputsP)
      (Domain.participant model program routingV.context artifactV inputsV) :=
  RootConnection.honestReadback producer validator model inputsP inputsV _
    (sourceReadback producer validator model inputsP inputsV scope laws Post paired initial)

end ZkcSecurity.Source.RootPair
