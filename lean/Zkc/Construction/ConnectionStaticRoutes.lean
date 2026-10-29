module

public import Zkc.Construction.ConnectionContext

@[expose] public section

/-! Finite local-service and delivery selection. The checks retain the original
source def-use and occurrence validators. Their interpretation covers every
valuation of the source stack, without substituting constants for loop binders. -/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionStaticRoutes
open Zkc.Source Zkc.Source.Structured NormalForm ConnectionFrame

def localCandidates (routing : Original.Routing) (sites : List String)
    (site field : String) (handle : Nat) : List Original.LocalRoute :=
  routing.locals.filter fun candidate =>
    candidate.handle == handle &&
      candidate.template.qualify (candidate.template.event[2]?.getD "") == site &&
      SourceOccurrences.localValid routing.snapshot routing.context candidate.port (.draw field)
        candidate.template && SourceOccurrences.repeatSites candidate.template == sites

structure Local (routing : Original.Routing) (sites : List String)
    (site field : String) (handle : Nat) (port : ServicePort) (template : Template) where
  selected : localCandidates routing sites site field handle = [⟨handle, port, template⟩]
  entry : template.entry = routing.context.entry
  count : template.repeats = sites.length
  steps : template.steps.all (fun step => step.kind == "apply" || step.kind == "repeat") = true
  callee : String
  localSite : String
  input : String
  event : template.event = ["query", callee, localSite, input, port.contract, "draw", port.owner]

def Local.origin {routing : Original.Routing} {sites : List String} {site field : String}
    {handle : Nat} {port : ServicePort} {template : Template}
    (binding : Local routing sites site field handle port template) : Origin :=
  Origin.query routing.context.entry (template.qualify binding.localSite)
    ("input_" ++ decimal port.root) port.contract port.owner (.draw field)

theorem Local.target {routing : Original.Routing} {sites : List String} {site field : String}
    {handle : Nat} {port : ServicePort} {template : Template}
    (binding : Local routing sites site field handle port template)
    (frames : Original.Frames) (same : frames.map (·.site) = sites) :
    Domain.localOrigin routing.context port (.draw field) template (frames.map (·.index)) =
      some (Domain.atCoordinates binding.origin (frames.map (·.index))) := by
  have count : template.repeats = frames.length := by rw [binding.count, ← same, List.length_map]
  simp only [Domain.localOrigin, binding.entry, count, List.length_map, ne_eq,
    not_true_eq_false, binding.steps, Bool.not_true, or_self, ↓reduceIte,
    binding.event, Request.draw, Local.origin, Bool.false_eq_true]

theorem Local.source {routing : Original.Routing} {sites : List String} {site field : String}
    {handle : Nat} {port : ServicePort} {template : Template}
    (binding : Local routing sites site field handle port template)
    (frames : Original.Frames) (same : frames.map (·.site) = sites) :
    routing.local frames site field handle =
      some (port, Domain.atCoordinates binding.origin (frames.map (·.index))) := by
  have selected : routing.locals.filter (fun candidate =>
      candidate.handle == handle &&
      candidate.template.qualify (candidate.template.event[2]?.getD "") == site &&
      SourceOccurrences.localValid routing.snapshot routing.context candidate.port (.draw field)
        candidate.template && SourceOccurrences.repeatSites candidate.template == frames.map (·.site)) =
        [⟨handle, port, template⟩] := by rw [same]; exact binding.selected
  simp only [Original.Routing.local, selected, binding.target frames same, bind, Option.bind, pure]

/-- A failed static selection remains failed for every reached index. -/
theorem resolve_none {snapshot : Snapshot} {context : Context} {expected : Origin}
    {sites : List String} {candidates : List Template}
    (checked : OccurrenceResolution.resolveStatic snapshot context expected sites candidates = none)
    (frames : Original.Frames) (same : frames.map (·.site) = sites) :
    OccurrenceResolution.resolve snapshot context expected frames candidates = none := by
  have filtered : candidates.filter (OccurrenceResolution.matchesOccurrence snapshot context expected frames) =
      candidates.filter (OccurrenceResolution.matchesStatic snapshot context expected sites) := by
    apply List.filter_congr
    intro candidate _
    rw [OccurrenceResolution.matchesOccurrence_eq_static, same]
  unfold OccurrenceResolution.resolve
  rw [filtered]
  unfold OccurrenceResolution.resolveStatic at checked
  split at checked
  · cases checked
  · rename_i notSingle
    split
    · rename_i candidate found
      exact False.elim (notSingle candidate found)
    · rfl

inductive LocalMode (routing : Original.Routing) (sites : List String) (site field : String) (handle : Nat) : Type where
  | producer (mode : routing.mode = .producer) : LocalMode routing sites site field handle
  | validatorHandle (mode : routing.mode = .validator) (privateHandle : handle ≠ routing.selectedHandle) :
      LocalMode routing sites site field handle
  | validatorService (mode : routing.mode = .validator) (noService : routing.context.service.isSome = false) :
      LocalMode routing sites site field handle
  | validatorRoute (mode : routing.mode = .validator)
      (noRoute : OccurrenceResolution.resolveStatic routing.snapshot routing.context
        (routing.context.query site (.draw field)) sites routing.draws = none) :
      LocalMode routing sites site field handle

theorem LocalMode.sound {routing : Original.Routing} {sites : List String} {site field : String} {handle : Nat}
    (checked : LocalMode routing sites site field handle)
    (frames : Original.Frames) (same : frames.map (·.site) = sites) :
    routing.mode = .producer ∨ (routing.mode = .validator ∧ routing.draw frames site field handle = none) := by
  cases checked with
  | producer mode => exact Or.inl mode
  | validatorHandle mode privateHandle =>
    exact Or.inr ⟨mode, by simp only [Original.Routing.draw, privateHandle, false_and, ↓reduceIte]⟩
  | validatorService mode noService =>
    exact Or.inr ⟨mode, by simp only [Original.Routing.draw, noService, Bool.false_eq_true, and_false, ↓reduceIte]⟩
  | validatorRoute mode noRoute =>
    refine Or.inr ⟨mode, ?_⟩
    unfold Original.Routing.draw
    split
    · exact resolve_none noRoute frames same
    · rfl

def deliveryCandidates (routing : Original.Routing) (site : String) : List Original.Delivery :=
  routing.deliveries.filter fun candidate =>
    Original.deliveryValid routing.snapshot routing.context candidate.draw candidate.message &&
      candidate.message.qualify (candidate.message.event[2]?.getD "") == site &&
      routing.context.draws.contains
        (candidate.draw.qualify (candidate.draw.event[2]?.getD ""), site)

structure Delivery (routing : Original.Routing) (sites : List String)
    (site field : String) (sender : Nat) (draw message : Template) where
  distinctDraws : (routing.context.draws.map Prod.fst).Nodup
  distinctMessages : (routing.context.draws.map Prod.snd).Nodup
  selected : deliveryCandidates routing site = [⟨draw, message⟩]
  messageRoute : OccurrenceResolution.resolveStatic routing.snapshot routing.context
    (routing.context.message site sender routing.context.producer) sites [message] = some message
  drawRoute : OccurrenceResolution.resolveStatic routing.snapshot routing.context
    (routing.context.query (draw.qualify (draw.event[2]?.getD "")) (.draw field)) sites [draw] = some draw

theorem Delivery.source {routing : Original.Routing} {sites : List String} {site field : String}
    {sender : Nat} {draw message : Template}
    (binding : Delivery routing sites site field sender draw message)
    (frames : Original.Frames) (same : frames.map (·.site) = sites) :
    routing.delivery frames site field sender = some
      (Domain.atCoordinates (routing.context.query (draw.qualify (draw.event[2]?.getD "")) (.draw field))
        (frames.map (·.index)),
       Domain.atCoordinates (routing.context.message site sender routing.context.producer)
        (frames.map (·.index))) := by
  have query := OccurrenceResolution.resolve_of_static binding.drawRoute frames same
  have message := OccurrenceResolution.resolve_of_static binding.messageRoute frames same
  simp only [Original.Routing.delivery, binding.distinctDraws, binding.distinctMessages,
    decide_true, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  change (do
    let _ ← some ()
    let [candidate] := deliveryCandidates routing site | none
    let message ← OccurrenceResolution.resolve routing.snapshot routing.context
      (routing.context.message site sender routing.context.producer) frames [candidate.message]
    let draw ← OccurrenceResolution.resolve routing.snapshot routing.context
      (routing.context.query (candidate.draw.qualify (candidate.draw.event[2]?.getD "")) (.draw field)) frames [candidate.draw]
    pure (draw, message)) = _
  rw [binding.selected]
  simp only [bind, Option.bind, query, message, pure]

end Zkc.Construction.ConnectionStaticRoutes
