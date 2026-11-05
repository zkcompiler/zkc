module

public import Zkc.Construction.ConnectionServiceRoutes
public import Zkc.Construction.ConnectionRouteCoverageSupport

@[expose] public section

/-! Source coverage is derived from finite source-owned routes independently
of simulation. A refused target cannot justify an omitted reached route. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Zkc.Construction.ConnectionServiceRequests
open Zkc.Source Zkc.Source.Structured NormalForm ConnectionFrame ConnectionRouteCoverage

def Service.query {carriers : Carriers} (service : Service) (site : String) :
    (participantInterfaceOn carriers).Op :=
  match service with
  | .draw field handle => .query site (.draw field) (.cons handle .nil)
  | .index contract handle bound => .query site (.sampleIndex contract)
      (.cons handle (.cons bound .nil))
  | .indices contract handle bound count => .query site (.sampleIndices contract)
      (.cons handle (.cons bound (.cons count .nil)))

theorem Public.coverage {carriers : Carriers} {routing : Original.Routing}
    {sites : List String} {site : String} {service : Service} {template : Template}
    (binding : Public routing sites site service template)
    (mode : routing.mode = .validator) (frames : Original.Frames)
    (same : frames.map (·.site) = sites) :
    Original.ActionCovered routing frames (service.query (carriers := carriers) site) := by
  have resolved := OccurrenceResolution.resolve_of_static binding.route frames same
  have asked : (Domain.atCoordinates
      ((service.routeContext routing.context).query site service.request)
      (frames.map (·.index))).request = some service.request := by
    rw [OccurrenceResolution.atCoordinates_request]; rfl
  cases service with
  | draw field handle =>
    exact ConnectionActionCoverage.publicQuery handle binding.selected mode binding.publicService same binding.route
  | index contract handle bound =>
    refine ⟨binding.valid, Or.inl ⟨mode, binding.nominal, _, ?_, asked⟩⟩
    simp only [Original.Routing.serviceRequest, ← binding.selected, Service.handle,
      binding.publicService, show (Request.sampleIndex bound).valid = true from binding.valid,
      and_self, ↓reduceIte]
    exact resolved
  | indices contract handle bound count =>
    refine ⟨binding.valid, Or.inl ⟨mode, binding.nominal, _, ?_, asked⟩⟩
    simp only [Original.Routing.serviceRequest, ← binding.selected, Service.handle,
      binding.publicService, show (Request.sampleIndices bound count).valid = true from binding.valid,
      and_self, ↓reduceIte]
    exact resolved

theorem Local.coverage {carriers : Carriers} {routing : Original.Routing}
    {sites : List String} {site : String} {service : Service} {port : ServicePort} {template : Template}
    (binding : Local routing sites site service port template)
    (frames : Original.Frames) (same : frames.map (·.site) = sites) :
    Original.ActionCovered routing frames (service.query (carriers := carriers) site) := by
  have found := binding.source frames same
  have asked : (Domain.atCoordinates binding.origin (frames.map (·.index))).request =
      some service.request := by rw [OccurrenceResolution.atCoordinates_request]; rfl
  cases service with
  | draw field handle => exact Or.inr ⟨port, _, found, asked⟩
  | index contract handle bound => exact ⟨binding.valid, Or.inr ⟨port, _, found, binding.nominal, asked⟩⟩
  | indices contract handle bound count => exact ⟨binding.valid, Or.inr ⟨port, _, found, binding.nominal, asked⟩⟩

theorem Delivery.coverage {carriers : Carriers} {routing : Original.Routing}
    {sites : List String} {site : String} {service : Service} {sender : Nat} {query message : Template}
    (binding : Delivery routing sites site service sender query message)
    (replacement : Replacement) (profile : routing.context.profile = .fiatShamir replacement)
    (mode : routing.mode = .producer) (frames : Original.Frames)
    (same : frames.map (·.site) = sites) :
    Original.ActionCovered routing frames
      (.receive service.request.sort site sender : (participantInterfaceOn carriers).Op) := by
  cases service with
  | draw field handle =>
    exact ConnectionActionCoverage.delivery sender query message replacement profile mode
      ⟨binding.distinctQueries, binding.distinctMessages, binding.selected,
        binding.messageRoute, binding.queryRoute⟩ same
  | index contract handle bound =>
    simp only [Original.ActionCovered, profile, mode, Service.request, Request.sampleIndex]
    refine ⟨_, _, _, binding.typedSource frames same rfl, rfl, binding.valid, ?_⟩
    rw [OccurrenceResolution.atCoordinates_request]; rfl
  | indices contract handle bound count =>
    simp only [Original.ActionCovered, profile, mode, Service.request, Request.sampleIndices]
    refine ⟨_, _, _, binding.typedSource frames same rfl, rfl, binding.valid, ?_⟩
    rw [OccurrenceResolution.atCoordinates_request]; rfl

noncomputable def coveredService {carriers : Carriers} {A : Type}
    (routing : Original.Routing) (frames final : Original.Frames) (post : A → Prop)
    (site : String) (operation : ServiceOp) (arguments : Values carriers.Value operation.arguments)
    (valid : operation.validInputs arguments = true)
    (covered : Original.ActionCovered routing frames (.query site operation arguments))
    (next : carriers.Value operation.result → PIR.Process (Occurrence.signature carriers) A)
    (tail : ∀ value, Covered routing post frames final (next value)) :
    Covered routing post frames final
      ((PIR.Process.interpret Occurrence.actions (serviceAction (.query site operation arguments))).bind next) := by
  simp only [serviceAction, valid, ite_true, PIR.Process.interpret, Occurrence.actions, PIR.Process.bind]
  apply Covered.action _ _ _ covered
  intro value
  by_cases checked : operation.validReply arguments value = true
  · simpa only [checked, ite_true, PIR.Process.interpret, PIR.Process.bind] using tail value
  · simp only [checked]
    exact .halt _ _ _

noncomputable def Service.coverForm {scope : Scope} {callees : List CalleeKey} {out : List Ty}
    (service : Service) (valid : service.request.valid = true)
    (routing : Original.Routing) (site : String)
    (next : Form [] callees (.value service.request.sort :: scope) out)
    (model : DomainModel) (tables : Tables model (Occurrence.signature model.toCarriers))
    (context : ProtocolContext) (runs : Runs model (Occurrence.signature model.toCarriers))
    (processes : CalleeProcesses model callees (Occurrence.signature model.toCarriers))
    (binders : Binders model scope) (frames final : Original.Frames)
    (post : Values (Component model.Value) out → Prop)
    (covered : Original.ActionCovered routing frames
      (service.query (carriers := model.toCarriers) (qualifyProtocolSite context.applicationPrefix site)))
    (tail : ∀ value, Covered routing post frames final
      (next.denoteOn model Occurrence.actions tables (LawResults.empty model) context runs processes
        (.cons value binders))) :
    Covered routing post frames final ((service.form site next).denoteOn model Occurrence.actions tables
      (LawResults.empty model) context runs processes binders) := by
  cases service <;>
    apply coveredService routing frames final post _ _ _ (by exact valid) covered _ tail

end Zkc.Construction.ConnectionServiceRequests
