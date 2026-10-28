module

public import ZkcSecurity.FiatShamir.RootConnectionExecution
public import ZkcSecurity.FiatShamir.OriginalSampledReadback

@[expose] public section

/-! Install sampled honest-pair readback on both actual root artifacts. -/
set_option autoImplicit false

namespace ZkcSecurity.FiatShamir.RootConnection
open Zkc.Source Zkc.Source.Structured Zkc.Construction ConnectionRoot

attribute [local implicit_reducible] CheckedProtocol.signature

/-- Install the existing sampled honest-pair property on the actual two
artifacts. Authorization and the source pair's successful readback remain
property premises; neither follows from public transcript reading. -/
theorem sampledReadback {program : Program} {routingP routingV : Original.Routing} {roleP roleV : Nat}
    {artifactP artifactV : Participant}
    (producer : RootCertificate program routingP roleP artifactP)
    (validator : RootCertificate program routingV roleV artifactV)
    (model : DomainModel) (inputsP inputsV : Domain.Environment model.toCarriers)
    (Allowed : ServicePort → Origin → Prop)
    (Post : (Values (Component model.Value) program.payload.entry.outputs × Original.State model.toCarriers) →
      (Values (Component model.Value) program.payload.entry.outputs × Original.State model.toCarriers) → Prop)
    (sourceReadback : SampledReadback Allowed Post
      (producer.source model inputsP) (validator.source model inputsV)) :
    SampledReadback Allowed (fun actualP actualV => ∃ sourceP sourceV, Post sourceP sourceV ∧
      Original.CompleteReturns program.payload.entry.signature routingP.context roleP artifactP sourceP actualP ∧
      Original.CompleteReturns program.payload.entry.signature routingV.context roleV artifactV sourceV actualV)
      (Domain.participant model program routingP.context artifactP inputsP)
      (Domain.participant model program routingV.context artifactV inputsV) :=
  SampledReadback.original (producer.simulation model inputsP) (validator.simulation model inputsV) sourceReadback

end ZkcSecurity.FiatShamir.RootConnection
