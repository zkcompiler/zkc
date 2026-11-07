module

public import ZkcSecurity.Bindings.Transcript.QueryTreeSource.Reading
public import Zkc.Construction.ConnectionServiceRoutes

@[expose] public section

/-! Install a scalar tree on a source draw and its direct delivery. Static
selection checks the original capability, constant bound, def-use edge and
repeat stack once. The source equalities apply at every reached coordinate. -/

set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.QueryTreeSource
open Zkc.Source Zkc.Construction ConnectionServiceRequests

namespace Placement

/-- A client can distinguish different segments with the same scalar bound.
Ambiguous selections do not yield a placement. -/
def select (routing : Original.Routing) (bound : Nat) (keep : Original.Delivery → Bool) :
    Option Original.Delivery :=
  match routing.deliveries.filter (fun edge => keep edge &&
    SourceOccurrences.requestAt routing.snapshot routing.context edge.draw == some (.sampleIndex bound)) with
  | [edge] => some edge
  | _ => none

def querySite (edge : Original.Delivery) := edge.draw.qualify (edge.draw.event[2]?.getD "")

def messageSite (edge : Original.Delivery) := edge.message.qualify (edge.message.event[2]?.getD "")

def service (routing : Original.Routing) (bound : Nat) :=
  Service.index routing.context.contract routing.selectedHandle bound

def segment (routing : Original.Routing) (bound : Nat) (edge : Original.Delivery)
    (outer : List Nat) : Segment :=
  let context := (service routing bound).routeContext routing.context
  ⟨context.query (querySite edge) (.sampleIndex bound),
    context.message (messageSite edge) routing.context.validator routing.context.producer, outer⟩

end Placement

open Placement in
structure Placement (routing : Original.Routing) (bound : Nat) (edge : Original.Delivery) where
  request : Public routing (SourceOccurrences.repeatSites edge.draw) (querySite edge)
    (service routing bound) edge.draw
  receive : Delivery routing (SourceOccurrences.repeatSites edge.draw) (messageSite edge)
    (service routing bound) routing.context.validator edge.draw edge.message
  send : OccurrenceResolution.resolveStatic routing.snapshot routing.context
    (routing.context.message (messageSite edge) routing.context.validator routing.context.producer)
    (SourceOccurrences.repeatSites edge.draw) routing.messages = some edge.message

namespace Placement
variable {carriers : Structured.Carriers} {routing : Original.Routing}
  {bound : Nat} {edge : Original.Delivery}

/-- The static placement authenticates an original port. Changing the runtime
handle and the executing role preserves that placement when the source
invocation uses the newly supplied handle. -/
theorem rebind (placement : Placement routing bound edge) (mode : Domain.Mode) (handle : Nat) :
    Placement { routing with mode, selectedHandle := handle } bound edge :=
  ⟨⟨rfl, placement.request.publicService, placement.request.valid, rfl, placement.request.route⟩,
   ⟨placement.receive.distinctQueries, placement.receive.distinctMessages,
    placement.receive.selected, placement.receive.sourceRequest, placement.receive.valid,
    placement.receive.messageRoute, placement.receive.typedMessageRoute, placement.receive.queryRoute⟩,
   placement.send⟩

theorem query (placement : Placement routing bound edge) (state : Original.State carriers)
    (outer : List Nat) (ordinal : Nat)
    (stack : state.frames.map (·.site) = SourceOccurrences.repeatSites edge.draw)
    (indices : state.frames.map (·.index) = outer ++ [ordinal])
    (mode : routing.mode = .validator) :
    Original.service routing state (querySite edge) routing.context.contract (.sampleIndex bound)
      routing.selectedHandle = Original.queryRequest state
        ((segment routing bound edge outer).queryAt ordinal) (.sampleIndex bound) := by
  simpa only [segment, Segment.queryAt, indices, service, Service.action, Service.request] using placement.request.source state stack mode

theorem receiveRoute (placement : Placement routing bound edge) (frames : Original.Frames)
    (outer : List Nat) (ordinal : Nat)
    (stack : frames.map (·.site) = SourceOccurrences.repeatSites edge.draw)
    (indices : frames.map (·.index) = outer ++ [ordinal]) :
    routing.typedDelivery frames (messageSite edge) .index routing.context.validator =
      some (.sampleIndex bound, (segment routing bound edge outer).queryAt ordinal,
        (segment routing bound edge outer).deliveryAt ordinal) := by
  simpa only [segment, Segment.queryAt, Segment.deliveryAt, service, Service.request, indices, querySite, Request.sampleIndex] using placement.receive.typedSource frames stack rfl

theorem sendRoute (placement : Placement routing bound edge) (frames : Original.Frames)
    (outer : List Nat) (ordinal : Nat)
    (stack : frames.map (·.site) = SourceOccurrences.repeatSites edge.draw)
    (indices : frames.map (·.index) = outer ++ [ordinal]) :
    routing.message frames (messageSite edge) routing.context.validator routing.context.producer =
      some ((segment routing bound edge outer).deliveryAt ordinal) := by
  have found := routing.message_of_static placement.send frames stack
  rw [indices] at found
  simpa only [segment, Segment.deliveryAt, service, Service.routeContext, Context.message, Context.role,
    Context.mapReplacement] using found

end Placement
end ZkcSecurity.FiatShamir.QueryTreeSource
