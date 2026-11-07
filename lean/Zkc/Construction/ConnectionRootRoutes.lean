module

public import Zkc.Construction.OriginalRouting

@[expose] public section

/-! Untrusted route discovery for actual constructed roots. Public occurrences
come from the source; local service candidates retain their exported port and
source template. The connection derivation rechecks every association against
the admitted source. Discovery is not an admission or coverage theorem.
-/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionRootRoutes
open Zkc.Source Zkc.Source.Structured Zkc.Construction

mutual
/-- Local routes retain runtime capability identity from the explicit root ABI. -/
def localRoutes (capabilities : List (Nat × Nat)) :
    List Zkc.Construction.Instruction → Except String (List Original.LocalRoute)
  | [] => .ok []
  | instruction :: rest => do
      return (← instructionRoutes capabilities instruction) ++ (← localRoutes capabilities rest)

def instructionRoutes (capabilities : List (Nat × Nat)) :
    Zkc.Construction.Instruction → Except String (List Original.LocalRoute)
  | ⟨operation, _, _, regions⟩ => do
      let nested ← regionRoutes capabilities regions
      match operation with
      | .localService port _ template _ =>
          let some handle := capabilities.lookup port.root | throw "connection-missing-local-capability"
          return ⟨handle, port, template⟩ :: nested
      | _ => return nested

def regionRoutes (capabilities : List (Nat × Nat)) :
    List InstructionRegion → Except String (List Original.LocalRoute)
  | [] => .ok []
  | ⟨_, body, _⟩ :: rest => do
      return (← localRoutes capabilities body) ++ (← regionRoutes capabilities rest)
end

/-- Discovery data carries no source/context identity authority. -/
structure Proposal where
  selectedHandle : Nat
  messages : List Template
  draws : List Template
  deliveries : List Original.Delivery
  locals : List Original.LocalRoute

/-- Original public routes are shared by the source experiment and the constructed
participant. Physical instructions only contribute local capability routes. -/
def publicRouting (snapshot : Snapshot) (context : Context) (mode : Domain.Mode)
    (selectedHandle : Nat) : Except String Original.Routing := do
  let all := SourceDelivery.templates snapshot context
  let deliveries ← context.draws.mapM fun (query, message) =>
    match SourceDelivery.resolve snapshot context query message with
    | some (draw, sent) => pure (⟨draw, sent⟩ : Original.Delivery)
    | none => throw "connection-source-delivery-refused"
  return { snapshot, context, mode, selectedHandle
           messages := all.filter (·.messageSite?.isSome)
           draws := all.filter (·.querySite?.isSome)
           deliveries, locals := [] }

/-- The same finite proposal supports producer and validator. The selected
public handle is required only when the validator actually calls that service;
producer delivery is justified by the source draw-to-exchange association. -/
def propose (snapshot : Snapshot) (context : Context) (mode : Domain.Mode)
    (capabilities : List (Nat × Nat)) (artifact : Participant) : Except String Proposal := do
  unless (capabilities.map Prod.fst).Nodup do throw "connection-duplicate-service-capability"
  let selected ← match mode, context.service with
    | .validator, some input =>
        match capabilities.lookup input with
        | some handle => pure handle
        | none => throw "connection-missing-selected-capability"
    | _, _ => pure 0
  let publicRoutes ← publicRouting snapshot context mode selected
  return {
    selectedHandle := selected
    messages := publicRoutes.messages
    draws := publicRoutes.draws
    deliveries := publicRoutes.deliveries
    locals := (← localRoutes capabilities artifact.instructions).eraseDups
  }

/-- Source identity, profile and role are fixed outside discovery. These record
projections stay definitionally available even when discovery data is shared as
a checked declaration. Successful discovery alone does not establish coverage. -/
def routing (snapshot : Snapshot) (context : Context) (mode : Domain.Mode)
    (capabilities : List (Nat × Nat)) (artifact : Participant)
    (found : (propose snapshot context mode capabilities artifact).toOption.isSome) : Original.Routing :=
  let proposal := (propose snapshot context mode capabilities artifact).toOption.get found
  { snapshot, context, mode
    selectedHandle := proposal.selectedHandle
    messages := proposal.messages
    draws := proposal.draws
    deliveries := proposal.deliveries
    locals := proposal.locals }

end Zkc.Construction.ConnectionRootRoutes
