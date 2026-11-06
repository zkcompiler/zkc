module

public import ZkcSecurity.Bindings.Transcript.QueryTreeSource.Keys
public import ZkcSecurity.Bindings.Transcript.ServiceReading

@[expose] public section

/-! Local consumers of authenticated source routing and the existing service reading.
No source evaluator or whole-source equality premise is introduced. Every lemma is at a reached
source action; source admission, guard failures and occurrence frames remain in the original fold.
-/
set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.QueryTreeSource
open Zkc.Source Zkc.Construction QueryTree
variable {carriers : Structured.Carriers}

/-- Actual source resolution supplies its checked candidate and full static ancestry. A raw
origin equality alone is insufficient evidence that a source action may use the segment. -/
theorem resolved_ancestry {snapshot : Structured.Snapshot} {context : Context}
    {segment : Segment} {frames : OccurrenceResolution.Frames} {candidates : List Template}
    {ordinal : Nat} {origin : Origin}
    (coordinates : frames.map (·.index) = segment.outer ++ [ordinal])
    (resolved : OccurrenceResolution.resolve snapshot context segment.query frames candidates =
      some origin) :
    origin = segment.queryAt ordinal ∧
      ∃ template ∈ candidates,
        SourceOccurrences.expected snapshot context template = some template.event ∧
        SourceOccurrences.repeatSites template = frames.map (·.site) ∧
        template.origin context = some segment.query ∧
        Domain.templateOrigin context template (frames.map (·.index)) = some origin := by
  exact ⟨by simpa only [Segment.queryAt, coordinates] using
    OccurrenceResolution.resolved_origin resolved, OccurrenceResolution.resolved_source resolved⟩

/-- The source's actual service route checks the capability, request and occurrence candidates
before returning this origin. Its exact nominal base and reached coordinates are retained. -/
theorem service_route_origin (routing : Original.Routing) (frames : Original.Frames)
    (site : String) (request : Request) (handle : Nat) (origin : Origin)
    (route : routing.serviceRequest frames site request handle = some origin) :
    origin = Domain.atCoordinates
      ((routing.context.mapReplacement fun replacement ↦
        { replacement with request := some request }).query site request)
      (frames.map (·.index)) := by
  unfold Original.Routing.serviceRequest at route
  split at route
  · exact OccurrenceResolution.resolved_origin route
  · cases route

/-- The key read by an actual routed public scalar action is precisely the encoded node.
The route premise is the existing executable source check, not an assumed encoding law. -/
theorem public_service (routing : Original.Routing) (state : Original.State carriers)
    (site contract : String) (bound handle height : Nat)
    (segment : Segment) (root : Domain.History carriers) (node : Node (Fin bound) height)
    (mode : routing.mode = .validator) (nominal : contract = routing.context.contract)
    (base : segment.query = (routing.context.mapReplacement fun replacement ↦
      { replacement with request := some (.sampleIndex bound) }).query site (.sampleIndex bound))
    (coordinates : state.frames.map (·.index) = segment.outer ++ [(nodePrefix node).length])
    (history : state.history = (encode segment (root, node)).1)
    (origin : Origin)
    (route : routing.serviceRequest state.frames site (.sampleIndex bound) handle = some origin) :
    Original.service routing state site contract (.sampleIndex bound) handle =
      Original.queryRequest { state with history := (encode segment (root, node)).1 }
        (encode segment (root, node)).2 (.sampleIndex bound) := by
  rw [Original.service_public routing state site contract (.sampleIndex bound) handle origin
    mode nominal route]
  have reached := service_route_origin routing state.frames site (.sampleIndex bound) handle
    origin route
  rw [coordinates, ← base] at reached
  change origin = segment.queryAt (nodePrefix node).length at reached
  rw [reached]
  congr 1
  cases state
  simp_all

/-- This is the existing exact reading/coherence bridge at the parsed source key. It retains
all decoded continuations and frames; no probability or source success is assumed. -/
theorem original_reading (segment : Segment) (bound height : Nat)
    (request : segment.query.request = some (.sampleIndex bound))
    (valid : (Request.sampleIndex bound).valid = true)
    (root : Domain.History carriers) (node : Node (Fin bound) height)
    (frames : Original.Frames) :
    let state : Original.State carriers := ⟨frames, (encode segment (root, node)).1⟩
    DomainReduction.Bridge DomainReduction.Service.interface
      (fun reached result ↦ reached = result.2.history ∧ result.2.frames = frames)
      state.history
      (Original.queryRequest state (encode segment (root, node)).2 (.sampleIndex bound))
      (Original.queryRequest state (encode segment (root, node)).2 (.sampleIndex bound)) := by
  exact DomainReduction.Service.original ⟨frames, (encode segment (root, node)).1⟩
    (encode segment (root, node)).2 (.sampleIndex bound) valid
    ((segment.queryAt_request _).trans request)

/-- The reply type at every encoded node is the actual service raw type, specialized to a
positive bound. This is an equality of typed logical carriers, with no provider-byte premise. -/
def rawEquiv (segment : Segment) {bound : Nat}
    (request : segment.query.request = some (.sampleIndex bound)) (positive : 0 < bound)
    (ordinal : Nat) :
    Domain.Raw (.challenge (segment.queryAt ordinal) : Domain.Event carriers) ≃ Fin bound := by
  have same := (segment.queryAt_request ordinal).trans request
  simpa only [Domain.Raw, same, Request.Raw, Request.sampleIndex, List.headD_cons,
    Request.replyBound_of_positive positive] using Equiv.refl (Fin bound)

/-- Complete source delivery follows the query and contains its actual scalar payload.
The actual def-use route is required by receiveRequest_of_route; a payload-free successor
key cannot replace this history. -/
theorem producer_delivery (routing : Original.Routing) (state : Original.State carriers)
    (site : String) (sender bound : Nat) (query message : Origin)
    (route : routing.typedDelivery state.frames site .index sender =
      some (.sampleIndex bound, query, message)) :
    Original.receiveRequest routing state .index site sender =
      (Domain.requestValue query (.sampleIndex bound) (.query state.history query)).bind
        (fun value ↦ .call (.observe (.message message (.index value))) fun _ ↦
          .done (value, { state with history := state.history ++
            [.challenge query, .message message (.index value)] })) := by
  simpa only [Request.sampleIndex, Domain.Payload.ofValue, Structured.Ty.isHandle,
    ↓reduceDIte] using Original.receiveRequest_of_route routing state site sender
      (.sampleIndex bound) query message route

/-- Appending one successful delivery advances precisely to the next scalar prefix. A failure
before this delivery has no such successor; the original Process retains that stopped prefix. -/
theorem events_append {bound : Nat} (segment : Segment) (ordinal : Nat)
    (positions : List (Fin bound)) (position : Fin bound) :
    events (carriers := carriers) segment ordinal (positions ++ [position]) =
      events segment ordinal positions ++
        [.challenge (segment.queryAt (ordinal + positions.length)),
          .message (segment.deliveryAt (ordinal + positions.length)) (.index position.val)] := by
  induction positions generalizing ordinal with
  | nil => simp [events]
  | cons first rest ih =>
    simp [events, ih, Nat.add_comm, Nat.add_left_comm]

/-- The verifier's original send records the same complete delivered payload in its history. -/
theorem validator_delivery (routing : Original.Routing) (state : Original.State carriers)
    (site : String) (receiver position : Nat) (message : Origin)
    (mode : routing.mode = .validator)
    (route : routing.message state.frames site routing.context.validator receiver = some message) :
    Original.send routing state .index site receiver position =
      .call (.observe (.message message (.index position))) (fun _ ↦
        .done ((), { state with
          history := state.history ++ [.message message (.index position)] })) := by
  simp only [Original.send, mode, route, Domain.Payload.ofValue, Structured.Ty.isHandle,
    ↓reduceDIte, Original.record]

/-- Every successor-key-relevant observation is in the scalar Step: the delivered value is
present, with the exact query/message origins and ordered history. This local extension law
does not presume that a failed source action reached a successor. -/
theorem successor_key {bound height : Nat} (segment : Segment)
    (root : Domain.History carriers) (before after : Node (Fin bound) height)
    (position : Fin bound) (next : nodePrefix after = nodePrefix before ++ [position]) :
    encode segment (root, after) =
      ((encode segment (root, before)).1 ++
        [.challenge (encode segment (root, before)).2,
          .message (segment.deliveryAt (nodePrefix before).length) (.index position.val)],
        segment.queryAt ((nodePrefix before).length + 1)) := by
  simp only [encode, next, events_append, Nat.zero_add, List.length_append,
    List.length_singleton, List.append_assoc]

end ZkcSecurity.FiatShamir.QueryTreeSource
