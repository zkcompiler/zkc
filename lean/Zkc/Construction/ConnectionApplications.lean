module

public import Zkc.Source.Structured.DomainProtocolLinking
public import Zkc.Construction.OriginalFrameRelations
public import Zkc.Construction.OriginalLoop

@[expose] public section

/-! Reuse a callee derivation at an actual linked declaration. The body proof
uses the payload's closed/component helper tables and complete protocol table.
Declaration linking discharges the change from the stored prefix. -/
set_option autoImplicit false
namespace Zkc.Construction.Original
open Zkc.Source Zkc.Source.Structured

noncomputable def Simulation.linkedApplication
    (model : DomainModel) (payload : UnitPayload) (routing : Routing)
    (definition : CheckedProtocol) (member : definition ∈ payload.protocols)
    (context : ProtocolContext) (self : Nat)
    (inputs : Values (Component model.Value) definition.inputs) (state : State model.toCarriers)
    {B : Type}
    (returns : (Values (Component model.Value) definition.outputs × State model.toCarriers) → B → Prop)
    (live : PIR.Process (Domain.effects model.toCarriers)
      (Values (Component model.Value) definition.outputs × State model.toCarriers) →
      Domain.Environment model.toCarriers → Prop)
    (target : PIR.Process (Domain.effects model.toCarriers) B)
    (certificate : Simulation returns live
      (fold routing (definition.denoteWithOn model (.silent _) Occurrence.actions
        (Occurrence.helpers model payload) (Occurrence.table model payload) Occurrence.iterations
        context self inputs) state) target) :
    Simulation returns live
      (fold routing (invokeProtocol (Occurrence.table model payload) definition.signature context self inputs) state)
      target := by
  rw [Occurrence.invoke_body model payload definition member]
  exact certificate

end Zkc.Construction.Original
