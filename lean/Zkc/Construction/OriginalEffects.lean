module

public import Zkc.Construction.OriginalFold

@[expose] public section

/-! Primitive construction laws, indexed by checked original routing facts.
These equations expose the actual nominal effects and reply-dependent history.
Public query/delivery and owner-local service construction are distinct laws. -/
set_option autoImplicit false
namespace Zkc.Construction.Original
open Zkc.Source
variable {carriers : Structured.Carriers}

/-- Decode at the nominal request's field, independently of host carrier
coincidences. The proof only transports the request-indexed reply type. -/
def fieldReply (origin : Origin) (field : String) (request : origin.request = some (.draw field))
    (reply : Domain.Raw (.challenge origin : Domain.Event carriers)) : carriers.Field field :=
  by simpa only [Domain.Raw, request, Request.draw] using reply

theorem queryField_eq (state : State carriers) (origin : Origin) (field : String)
    (request : origin.request = some (.draw field)) :
    queryField state origin field =
      .call (.query state.history origin) (fun reply =>
        .done (fieldReply origin field request reply,
          { state with history := state.history ++ [.challenge origin] })) := by
  simp only [queryField, request, ↓reduceDIte]
  rfl

/-- A verifier's public draw uses the exact nominal origin resolved from its
original action and reached frames. All typed oracle replies are quantified. -/
theorem public_query (routing : Routing) (state : State carriers)
    (site field : String) (handle : Nat) (origin : Origin)
    (mode : routing.mode = .validator)
    (route : routing.draw state.frames site field handle = some origin) :
    query routing state site field handle =
      .call (.query state.history origin) (fun reply =>
        .done (fieldReply origin field (Routing.draw_request route) reply,
          { state with history := state.history ++ [.challenge origin] })) := by
  simp only [query, mode, route]
  exact queryField_eq _ _ _ _

/-- Owner-local queries keep the entire original construction state. Their
replies never become public challenges or transcript observations. -/
theorem private_query_producer (routing : Routing) (state : State carriers)
    (site field : String) (handle : Nat) (port : ServicePort) (origin : Origin)
    (mode : routing.mode = .producer)
    (route : routing.local state.frames site field handle = some (port, origin))
    (request : origin.request = some (.draw field)) :
    query routing state site field handle =
      .call (.localService port origin) (fun reply =>
        .done (fieldReply origin field request reply, state)) := by
  simp only [query, mode, route, request, ↓reduceDIte]
  rfl

theorem private_query_validator (routing : Routing) (state : State carriers)
    (site field : String) (handle : Nat) (port : ServicePort) (origin : Origin)
    (mode : routing.mode = .validator)
    (notPublic : routing.draw state.frames site field handle = none)
    (route : routing.local state.frames site field handle = some (port, origin))
    (request : origin.request = some (.draw field)) :
    query routing state site field handle =
      .call (.localService port origin) (fun reply =>
        .done (fieldReply origin field request reply, state)) := by
  simp only [query, mode, notPublic, route, request, ↓reduceDIte]
  rfl

/-- The producer replaces this particular original delivery receive by its
associated original draw, then records the delivered value. A query failure
halts before recording a delivered message. -/
theorem producer_delivery (routing : Routing) (state : State carriers)
    (site field : String) (sender : Nat) (draw message : Origin)
    (mode : routing.mode = .producer)
    (route : routing.delivery state.frames site field sender = some (draw, message))
    (request : draw.request = some (.draw field)) :
    receive routing state (.field field) site sender =
      .call (.query state.history draw) (fun reply =>
        let value := fieldReply draw field request reply
        .call (.observe (.message message (.field field value))) (fun _ =>
          .done (value, { state with history := state.history ++
            [.challenge draw, .message message (.field field value)] }))) := by
  simp only [receive, mode, route, queryField, request, ↓reduceDIte,
    PIR.Process.bind, record, List.append_assoc]
  rfl

/-- A proof receive records exactly the decoded original message. The runtime
handler retains an unread or malformed proof suffix on a failed receive. -/
theorem validator_receive (routing : Routing) (state : State carriers)
    (site field : String) (sender : Nat) (origin : Origin)
    (mode : routing.mode = .validator)
    (route : routing.message state.frames site sender routing.context.validator = some origin) :
    receive routing state (.field field) site sender =
      .call (.receive (.field field) site site (routing.context.role sender)) (fun value =>
        .call (.observe (.message origin (.field field value))) (fun _ =>
          .done (value, { state with history := state.history ++ [.message origin (.field field value)] }))) := by
  simp only [receive, mode, route, Domain.Payload.ofValue, record, PIR.Process.bind]

end Zkc.Construction.Original
