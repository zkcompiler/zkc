module

public import Zkc.Construction.OccurrenceResolution
public import Zkc.Construction.DomainProducer
public import Zkc.Construction.SourceDelivery

@[expose] public section

/-! Source-owned routes for constructing the original participant process.
Discovery supplies candidates only. Resolution checks the admitted source,
ordered repeat frames and request. A challenge delivery additionally checks
that the original exchange uses the result of that particular original draw.
-/
set_option autoImplicit false
namespace Zkc.Construction.Original
open Zkc.Source

/-- Reuse the source-owned def-use checker. The original exchange must send
that draw result (possibly with a visibility restriction), not a same-typed
value. Discovery and source metadata remain with SourceDelivery. -/
abbrev deliveryValid := SourceDelivery.checked

structure Delivery where
  draw : Template
  message : Template
  deriving DecidableEq, Repr

structure LocalRoute where
  handle : Nat
  port : ServicePort
  template : Template
  deriving DecidableEq, Repr

/-- Actual service handles are supplied by the root ABI association; a numeric
source input position is not implicitly used as a runtime capability. -/
structure Routing where
  snapshot : Structured.Snapshot
  context : Context
  mode : Domain.Mode
  selectedHandle : Nat
  messages : List Template
  draws : List Template
  deliveries : List Delivery
  locals : List LocalRoute := []

abbrev Frames := List Structured.Occurrence.Frame

/-- Source message identity is checked at the actual role endpoints. -/
def Routing.message (routing : Routing) (frames : Frames) (site : String)
    (sender receiver : Nat) : Option Origin :=
  OccurrenceResolution.resolve routing.snapshot routing.context
    (routing.context.message site sender receiver) frames routing.messages

/-- Only the selected public service may use this route. -/
def Routing.draw (routing : Routing) (frames : Frames) (site field : String)
    (handle : Nat) : Option Origin :=
  if handle = routing.selectedHandle ∧ routing.context.service.isSome = true then
    OccurrenceResolution.resolve routing.snapshot routing.context
      (routing.context.query site (.draw field)) frames routing.draws
  else none

/-- A plain source has no selected public draw, for any handle or frames. -/
theorem Routing.draw_plain (routing : Routing) (plain : routing.context.profile = .plain)
    (frames : Frames) (site field : String) (handle : Nat) :
    routing.draw frames site field handle = none := by
  simp [Routing.draw, Context.service, Context.replacement?, plain]

/-- The producer can replace only a receive backed by a checked original
public draw and its direct def-use delivery. Ambiguity refuses. -/
def Routing.delivery (routing : Routing) (frames : Frames) (site field : String)
    (sender : Nat) : Option (Origin × Origin) := do
  if !(routing.context.draws.map Prod.fst).Nodup ||
      !(routing.context.draws.map Prod.snd).Nodup then none
  else pure ()
  let candidates := routing.deliveries.filter fun candidate =>
    deliveryValid routing.snapshot routing.context candidate.draw candidate.message &&
      candidate.message.qualify (candidate.message.event[2]?.getD "") == site &&
      (routing.context.draws.contains
        (candidate.draw.qualify (candidate.draw.event[2]?.getD ""), site))
  let [candidate] := candidates | none
  let message ← OccurrenceResolution.resolve routing.snapshot routing.context
    (routing.context.message site sender routing.context.producer) frames [candidate.message]
  let querySite := candidate.draw.qualify (candidate.draw.event[2]?.getD "")
  let draw ← OccurrenceResolution.resolve routing.snapshot routing.context
    (routing.context.query querySite (.draw field)) frames [candidate.draw]
  return (draw, message)

/-- A resolved selected query certifies that a public replacement exists. -/
theorem Routing.draw_profile {routing : Routing} {frames : Frames} {site field : String}
    {handle : Nat} {origin : Origin}
    (found : routing.draw frames site field handle = some origin) :
    ∃ replacement, routing.context.profile = .fiatShamir replacement := by
  cases profile : routing.context.profile with
  | fiatShamir replacement => exact ⟨replacement, rfl⟩
  | plain => rw [routing.draw_plain profile] at found; cases found

/-- The producer delivery policy cannot select an exchange in the plain profile. -/
theorem Routing.delivery_plain (routing : Routing) (plain : routing.context.profile = .plain)
    (frames : Frames) (site field : String) (sender : Nat) :
    routing.delivery frames site field sender = none := by
  have empty : routing.deliveries.filter (fun _ => false) = [] := by
    induction routing.deliveries with
    | nil => rfl
    | cons _ _ ih => exact ih
  simp [Routing.delivery, Context.draws, Context.replacement?, plain, empty]

theorem Routing.delivery_profile {routing : Routing} {frames : Frames} {site field : String}
    {sender : Nat} {origins : Origin × Origin}
    (found : routing.delivery frames site field sender = some origins) :
    ∃ replacement, routing.context.profile = .fiatShamir replacement := by
  cases profile : routing.context.profile with
  | fiatShamir replacement => exact ⟨replacement, rfl⟩
  | plain => rw [routing.delivery_plain profile] at found; cases found

/-- Owner-local services keep their actual capability, root, nominal request
and complete source path. They never become public transcript queries. -/
def Routing.local (routing : Routing) (frames : Frames) (site field : String)
    (handle : Nat) : Option (ServicePort × Origin) := do
  let candidates := routing.locals.filter fun candidate =>
    candidate.handle == handle &&
      candidate.template.qualify (candidate.template.event[2]?.getD "") == site &&
      SourceOccurrences.localValid routing.snapshot routing.context candidate.port (.draw field)
        candidate.template &&
      SourceOccurrences.repeatSites candidate.template == frames.map (·.site)
  let [candidate] := candidates | none
  let origin ← Domain.localOrigin routing.context candidate.port (.draw field)
    candidate.template (frames.map (·.index))
  return (candidate.port, origin)

/-- Resolution cannot change a public draw's nominal reply carrier. -/
theorem Routing.draw_request {routing : Routing} {frames : Frames} {site field : String}
    {handle : Nat} {origin : Origin}
    (found : routing.draw frames site field handle = some origin) :
    origin.request = some (.draw field) := by
  unfold Routing.draw at found
  split at found
  · exact OccurrenceResolution.resolved_request found
  · cases found

end Zkc.Construction.Original
