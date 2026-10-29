module

public import ZkcSecurity.Source.RootPair
public import ZkcSecurity.Source.RootPublic
public import ZkcSecurity.FiatShamir.RootConnectionEndpoint

@[expose] public section

/-! Complete installation at generated roots. Only input ABI reads and the
mathematical terminal predicate are client obligations. Coverage, routing,
source reading, histories and full returned rows remain root-owned facts. -/
set_option autoImplicit false
namespace ZkcSecurity.Source.Installation
open Zkc.Source Zkc.Source.Structured Zkc.Construction ConnectionRoot
open ZkcSecurity.FiatShamir Zkc.Transcript Zkc.Obligations

theorem accepted {art : ZkcSecurity.Endpoint.Domain.Artifacts}
    (compiled : ZkcSecurity.Endpoint.Domain.Compiled art)
    {routingP routingV : Original.Routing} {roleP : Nat} {artifactP : Participant}
    (producer : RootCertificate compiled.imported.program routingP roleP artifactP)
    (validator : RootCertificate compiled.imported.program routingV compiled.selection.context.validator art.participant)
    (contextV : routingV.context = compiled.selection.context)
    (model : DomainModel) (inputsP inputsV : Domain.Environment model.toCarriers)
    (valuesP valuesV : Values (Component model.Value) compiled.imported.program.payload.entry.inputs)
    (readP : producer.inputs.abi.read inputsP compiled.imported.program.payload.entry.inputs = some valuesP)
    (readV : validator.inputs.abi.read inputsV compiled.imported.program.payload.entry.inputs = some valuesV)
    (scope : PairScope) (laws : Pair.FoldLaws (carriers := model.toCarriers) scope routingP routingV)
    (Post : Values (Component model.Value) compiled.imported.program.payload.entry.outputs →
      Values (Component model.Value) compiled.imported.program.payload.entry.outputs → Prop)
    (paired : Pair scope Post
      (Occurrence.participant model compiled.imported.program roleP valuesP)
      (Occurrence.participant model compiled.imported.program compiled.selection.context.validator valuesV))
    (initial : producer.inputs.initial inputsP = validator.inputs.initial inputsV)
    (terminal : ∀ p v, Post p v → v.get compiled.selection.output = some true) :
    Readback (fun _ result => compiled.acceptance result = some true)
      (Domain.participant model compiled.imported.program routingP.context artifactP inputsP)
      (Domain.participant model compiled.imported.program routingV.context art.participant inputsV) := by
  have sourcePair : Pair scope Post (producer.occurrenceSource model inputsP)
      (validator.occurrenceSource model inputsV) := by
    rw [RootPair.occurrence_of_read producer model inputsP valuesP readP,
      RootPair.occurrence_of_read validator model inputsV valuesV readV]
    exact paired
  apply (RootPair.artifacts producer validator model inputsP inputsV scope laws Post sourcePair initial).mono
  intro p v result
  obtain ⟨sourceP, sourceV, ⟨holds, _⟩, _, related⟩ := result
  rw [contextV] at related
  exact (RootConnection.compiledAcceptance_agree compiled related).symm.trans
    (terminal sourceP.1 sourceV.1 holds)

variable {program : Program} {routing : Original.Routing} {role : Nat} {artifact : Participant}
  (root : RootCertificate program routing role artifact) (mode : routing.mode = .validator)
  (model : DomainModel) (values : Values (Component model.Value) program.payload.entry.inputs)
  (price : ENNReal) [∀ event : Domain.Event model.toCarriers, SampleableType (Domain.Raw event)]

noncomputable def rejected (data : Domain.Environment model.toCarriers)
    (initial : Domain.History model.toCarriers) (replacement : Replacement)
    (profile : routing.context.profile = .fiatShamir replacement)
    (read : root.inputs.abi.read (Domain.inputFrame routing.context data initial)
      program.payload.entry.inputs = some values)
    (output : Var program.payload.entry.outputs .boolean)
    (failed : Values (Component model.Value) program.payload.entry.outputs)
    (terminal : failed.get output ≠ some true)
    (history : List (PublicProperties.Event model.toCarriers))
    (source : Derivation PublicProperties.interface (PublicProperties.escape price)
      (fun _ out => out = failed) history (Occurrence.participant model program role values)) :
    Derivation NominalDomain.interface (ZkcSecurity.Obligations.boundedEscape (fun _ _ => price))
      (fun _ result => result.1.get output ≠ some true) initial
      (RootConnection.publicPresentation root model (Domain.inputFrame routing.context data initial)) :=
  RootPublic.rejects_inputFrame root mode model values price data initial replacement profile read
    _ history (source.consequence (fun _ _ same => same ▸ terminal))

end ZkcSecurity.Source.Installation
