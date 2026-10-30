module

public import ZkcSecurity.Bindings.Transcript.OriginalTransport
public import ZkcSecurity.Claims.CompiledSoundness

@[expose] public section

/-! A source installation binds one family presentation to the full actual
artifact. LosslessPresentationClaims transports its derivations into the existing
charged export; the existing Claims consumers own every probability meaning.
-/
set_option autoImplicit false
noncomputable section
namespace ZkcSecurity.FiatShamir.Original.Claims
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript
open ZkcSecurity.Claims ZkcSecurity.Obligations OracleComp OracleSpec

variable {model : DomainModel} {art : ZkcSecurity.Endpoint.Domain.Artifacts}
  {subject : ZkcSecurity.Claims.Domain.Subject model art}

/-- The installed source and its complete return type are shared by all
statements. The artifact relation remains a separate full simulation. -/
structure Installation (subject : ZkcSecurity.Claims.Domain.Subject model art) where
  result : Type
  signature : PIR.Signature
  absorb : Interface signature (Domain.Event model.toCarriers) (Domain.Payload model.toCarriers) Domain.Raw
  inputs : art.Statement model → Domain.Environment model.toCarriers
  encoded : ∀ statement, Domain.encodeValues statement = some (inputs statement)
  source : art.Statement model → Domain.History model.toCarriers →
    PIR.Process (Domain.effects model.toCarriers) result
  presented : art.Statement model → Domain.History model.toCarriers → PIR.Process signature result
  Post : Domain.History model.toCarriers → result → Prop
  returns : result → Domain.Result model.toCarriers → Prop
  live : art.Statement model → Domain.History model.toCarriers →
    PIR.Process (Domain.effects model.toCarriers) result → Domain.Environment model.toCarriers → Prop
  acceptance : result → Option Bool
  bridge : ∀ statement initial, Original.Bridge absorb Post initial (source statement initial)
    (Domain.participant model subject.compiled.imported.program subject.compiled.selection.context
      art.participant (Domain.inputFrame subject.compiled.selection.context (inputs statement) initial))
    (presented statement initial) returns (live statement initial)
  agrees : ∀ source actual, returns source actual → acceptance source = subject.compiled.acceptance actual


end ZkcSecurity.FiatShamir.Original.Claims
