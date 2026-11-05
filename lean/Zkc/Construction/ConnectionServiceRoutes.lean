module

public import Zkc.Construction.ConnectionServiceRequests

@[expose] public section

/-! Source-owned local and delivery selection for typed finite services. All
checks are finite syntax, ownership, ordered operands and occurrence checks. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Zkc.Construction.ConnectionServiceRequests
open Zkc.Source Zkc.Source.Structured NormalForm ConnectionFrame

def localCandidates (routing : Original.Routing) (sites : List String)
    (site : String) (service : Service) : List Original.LocalRoute :=
  routing.locals.filter fun candidate =>
    candidate.handle == service.handle &&
      candidate.template.qualify (candidate.template.event[2]?.getD "") == site &&
      SourceOccurrences.localValid routing.snapshot routing.context candidate.port service.request
        candidate.template && SourceOccurrences.repeatSites candidate.template == sites

structure Local (routing : Original.Routing) (sites : List String)
    (site : String) (service : Service) (port : ServicePort) (template : Template) where
  selected : localCandidates routing sites site service = [⟨service.handle, port, template⟩]
  entry : template.entry = routing.context.entry
  count : template.repeats = sites.length
  steps : template.steps.all (fun step => step.kind == "apply" || step.kind == "repeat") = true
  callee : String
  localSite : String
  input : String
  event : template.event = ["query", callee, localSite, input,
    port.contract, service.request.method, port.owner]
  nominal : port.contract = service.contract
  valid : service.request.valid = true

def Local.origin {routing : Original.Routing} {sites : List String} {site : String}
    {service : Service} {port : ServicePort} {template : Template}
    (binding : Local routing sites site service port template) : Origin :=
  Origin.query routing.context.entry (template.qualify binding.localSite)
    ("input_" ++ decimal port.root) port.contract port.owner service.request

theorem Local.target {routing : Original.Routing} {sites : List String} {site : String}
    {service : Service} {port : ServicePort} {template : Template}
    (binding : Local routing sites site service port template)
    (frames : Original.Frames) (same : frames.map (·.site) = sites) :
    Domain.localOrigin routing.context port service.request template (frames.map (·.index)) =
      some (Domain.atCoordinates binding.origin (frames.map (·.index))) := by
  have count : template.repeats = frames.length := by rw [binding.count, ← same, List.length_map]
  simp only [Domain.localOrigin, binding.entry, count, List.length_map, ne_eq,
    not_true_eq_false, binding.steps, Bool.not_true, or_self, ↓reduceIte,
    binding.event, Local.origin, Bool.false_eq_true]

theorem Local.source {routing : Original.Routing} {sites : List String} {site : String}
    {service : Service} {port : ServicePort} {template : Template}
    (binding : Local routing sites site service port template)
    (frames : Original.Frames) (same : frames.map (·.site) = sites) :
    routing.localRequest frames site service.request service.handle =
      some (port, Domain.atCoordinates binding.origin (frames.map (·.index))) := by
  have selected : localCandidates routing (frames.map (·.site)) site service =
      [⟨service.handle, port, template⟩] := by rw [same]; exact binding.selected
  change (do
    let [candidate] := localCandidates routing (frames.map (fun frame : Occurrence.Frame => frame.site)) site service | none
    let origin ← Domain.localOrigin routing.context candidate.port service.request
      candidate.template (frames.map (fun frame : Occurrence.Frame => frame.index))
    pure (candidate.port, origin)) = _
  rw [selected]
  simp only [binding.target frames same, bind, Option.bind, pure]

def Service.publicRoute (service : Service) (routing : Original.Routing)
    (frames : Original.Frames) (site : String) : Option Origin :=
  match service with
  | .draw field handle => routing.draw frames site field handle
  | _ => routing.serviceRequest frames site service.request service.handle

inductive LocalMode (routing : Original.Routing) (sites : List String)
    (site : String) (service : Service) : Type where
  | producer (mode : routing.mode = .producer) : LocalMode routing sites site service
  | privateHandle (mode : routing.mode = .validator)
      (privateHandle : service.handle ≠ routing.selectedHandle) :
      LocalMode routing sites site service
  | noService (mode : routing.mode = .validator)
      (noService : routing.context.service.isSome = false) : LocalMode routing sites site service
  | noRoute (mode : routing.mode = .validator)
      (noRoute : OccurrenceResolution.resolveStatic routing.snapshot
        (service.routeContext routing.context)
        ((service.routeContext routing.context).query site service.request) sites
        (service.candidates routing) = none) : LocalMode routing sites site service

theorem LocalMode.sound {routing : Original.Routing} {sites : List String} {site : String}
    {service : Service} (checked : LocalMode routing sites site service)
    (frames : Original.Frames) (same : frames.map (·.site) = sites) :
    routing.mode = .producer ∨
      (routing.mode = .validator ∧ service.publicRoute routing frames site = none) := by
  cases checked with
  | producer mode => exact Or.inl mode
  | privateHandle mode privateHandle =>
    refine Or.inr ⟨mode, ?_⟩
    cases service <;> simp_all [Service.publicRoute, Original.Routing.draw,
      Original.Routing.serviceRequest, Service.handle]
  | noService mode noService =>
    refine Or.inr ⟨mode, ?_⟩
    cases service <;> simp_all [Service.publicRoute, Original.Routing.draw,
      Original.Routing.serviceRequest]
  | noRoute mode noRoute =>
    refine Or.inr ⟨mode, ?_⟩
    have absent := ConnectionStaticRoutes.resolve_none noRoute frames same
    cases service <;> simp only [Service.publicRoute, Original.Routing.draw,
      Original.Routing.serviceRequest]
    all_goals split <;> first | exact absent | rfl

inductive Operands {scope : Scope} (layout : Layout scope) : Service → List Nat → Type where
  | draw (field : String) (handle : Nat) : Operands layout (.draw field handle) []
  | index (contract : String) (handle bound reference : Nat)
      (read : layout[reference]? = some (.data (.present (.index bound)))) :
      Operands layout (.index contract handle bound) [reference]
  | indices (contract : String) (handle bound count boundRef countRef : Nat)
      (boundRead : layout[boundRef]? = some (.data (.present (.index bound))))
      (countRead : layout[countRef]? = some (.data (.present (.index count)))) :
      Operands layout (.indices contract handle bound count) [boundRef, countRef]

theorem Operands.read {model : DomainModel} {scope : Scope} {binders : Binders model scope}
    {history : Domain.History model.toCarriers} {layout : Layout scope}
    {environment : Domain.Environment model.toCarriers} {service : Service} {references : List Nat}
    (operands : Operands layout service references)
    (related : Holds model binders history layout environment) :
    Domain.requestOperands environment references service.request = true := by
  cases operands <;>
    simp [Domain.requestOperands, Service.request, Request.draw, Request.sampleIndex,
      Request.sampleIndices, related.index, Term.eval, *]

theorem Service.localAction {carriers : Carriers} (service : Service) (routing : Original.Routing)
    (state : Original.State carriers) (site : String) (port : ServicePort) (origin : Origin)
    (localMode : routing.mode = .producer ∨
      (routing.mode = .validator ∧ service.publicRoute routing state.frames site = none))
    (route : routing.localRequest state.frames site service.request service.handle = some (port, origin))
    (nominal : port.contract = service.contract) (valid : service.request.valid = true)
    (asked : origin.request = some service.request) :
    service.action routing state site =
      (Domain.requestValue origin service.request (.localService port origin)).bind
        (fun value => .done (value, state)) := by
  cases service with
  | draw field handle =>
    change routing.local state.frames site field handle = some (port, origin) at route
    change routing.mode = .producer ∨ (routing.mode = .validator ∧
      routing.draw state.frames site field handle = none) at localMode
    rcases localMode with producer | ⟨validator, absent⟩
    all_goals
      simp only [Service.action, Original.query, *]
      simp only [Domain.requestValue, Service.request, Request.valid, Request.draw, asked,
        ↓reduceIte, ↓reduceDIte]
      rfl
  | index contract handle bound =>
    rcases localMode with producer | ⟨validator, absent⟩
    · exact Original.service_local _ _ _ _ _ _ _ _ producer route nominal
    · exact Original.service_local_unselected _ _ _ _ _ _ _ _ absent route nominal

  | indices contract handle bound count =>
    rcases localMode with producer | ⟨validator, absent⟩
    · exact Original.service_local _ _ _ _ _ _ _ _ producer route nominal
    · exact Original.service_local_unselected _ _ _ _ _ _ _ _ absent route nominal

def LocalReturned {carriers : Carriers} (request : Request) (state : Original.State carriers)
    (environment : Domain.Environment carriers)
    (source : carriers.Value request.sort × Original.State carriers)
    (target : Domain.Environment carriers) : Prop :=
  source.2 = state ∧ ∃ encoded, Domain.Value.encode request.sort source.1 = some encoded ∧
    target = environment ++ [encoded]

theorem LocalReturned.frame {model : DomainModel} {scope : Scope} {binders : Binders model scope}
    {layout : Layout scope} {request : Request} {state : Original.State model.toCarriers}
    {environment target : Domain.Environment model.toCarriers}
    {source : model.Value request.sort × Original.State model.toCarriers}
    (returned : LocalReturned request state environment source target)
    (related : Holds model binders state.history layout environment) :
    Holds model (.cons source.1 binders) source.2.history
      (layout.map (Cell.rename .there) ++ [.data (.present (.var .here))]) target := by
  obtain ⟨same, encoded, value, appended⟩ := returned
  rw [same, appended]
  exact related.bindData source.1 value

noncomputable def Service.localSimulation {scope : Scope} {layout : Layout scope}
    (service : Service) (routing : Original.Routing) (sites : List String) (site : String)
    (port : ServicePort) (template : Template) (binding : Local routing sites site service port template)
    (mode : LocalMode routing sites site service) (coordinates references : List Nat)
    (operands : Operands layout service references)
    (model : DomainModel) (binders : Binders model scope)
    (state : Original.State model.toCarriers) (environment : Domain.Environment model.toCarriers)
    (related : Holds model binders state.history layout environment)
    (same : state.frames.map (·.site) = sites)
    (pathRead : Domain.localCoordinates environment coordinates = some (state.frames.map (·.index))) :
    Original.Simulation (LocalReturned service.request state environment)
      (fun _ frame => frame = environment)
      (service.action routing state site)
      (Domain.View.localService routing.context port service.request template coordinates references
        [.data service.request.sort] environment) := by
  let origin := Domain.atCoordinates binding.origin (state.frames.map (·.index))
  have asked : origin.request = some service.request := by
    rw [OccurrenceResolution.atCoordinates_request]
    rfl
  have found := binding.target state.frames same
  have source := service.localAction routing state site port origin
    (mode.sound state.frames same) (binding.source state.frames same) binding.nominal binding.valid asked
  rw [source]
  have operation : (service.request.operation port.contract).isSome = true := by
    cases service <;> simp [Service.request, Request.operation, Request.draw,
      Request.sampleIndex, Request.sampleIndices, binding.nominal, Service.contract]
  have target := Domain.localRequest_of_checks routing.context port service.request template
    coordinates references environment (state.frames.map (·.index)) origin
    ⟨binding.valid, operation, operands.read related⟩ pathRead
    (by simpa only [origin] using found)
  rw [Domain.View.localService, target]
  apply Original.Simulation.request
  intro value
  apply Classical.choice
  obtain ⟨encoded, encode⟩ := Domain.Value.encode_exists (carriers := model.toCarriers)
    (by simp [Domain.dataType, service.data]) value
  rw [encode]
  exact ⟨.done ⟨rfl, encoded, encode, rfl⟩⟩

structure Delivery (routing : Original.Routing) (sites : List String)
    (site : String) (service : Service) (sender : Nat) (query message : Template) where
  distinctQueries : (routing.context.draws.map Prod.fst).Nodup
  distinctMessages : (routing.context.draws.map Prod.snd).Nodup
  selected : ConnectionStaticRoutes.deliveryCandidates routing site = [⟨query, message⟩]
  sourceRequest : SourceOccurrences.requestAt routing.snapshot routing.context query =
    some service.request
  valid : service.request.valid = true
  messageRoute : OccurrenceResolution.resolveStatic routing.snapshot routing.context
    (routing.context.message site sender routing.context.producer) sites [message] = some message
  typedMessageRoute : OccurrenceResolution.resolveStatic routing.snapshot
    (service.routeContext routing.context)
    ((service.routeContext routing.context).message site sender routing.context.producer)
    sites [message] = some message
  queryRoute : OccurrenceResolution.resolveStatic routing.snapshot
    (service.routeContext routing.context)
    ((service.routeContext routing.context).query
      (query.qualify (query.event[2]?.getD "")) service.request) sites [query] = some query

theorem Delivery.typedSource {routing : Original.Routing} {sites : List String} {site : String}
    {service : Service} {sender : Nat} {query message : Template}
    (binding : Delivery routing sites site service sender query message)
    (frames : Original.Frames) (same : frames.map (·.site) = sites)
    (typed : service.routeContext routing.context =
      routing.context.mapReplacement fun replacement =>
        { replacement with request := some service.request }) :
    routing.typedDelivery frames site service.request.sort sender = some (service.request,
      Domain.atCoordinates ((service.routeContext routing.context).query
        (query.qualify (query.event[2]?.getD "")) service.request) (frames.map (·.index)),
      Domain.atCoordinates ((service.routeContext routing.context).message site sender
        routing.context.producer) (frames.map (·.index))) := by
  have resolvedQuery := OccurrenceResolution.resolve_of_static binding.queryRoute frames same
  have resolvedMessage := OccurrenceResolution.resolve_of_static binding.typedMessageRoute frames same
  rw [typed] at resolvedQuery resolvedMessage ⊢
  simp only [Original.Routing.typedDelivery, binding.distinctQueries, binding.distinctMessages,
    decide_true, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  change (do
    let _ ← some ()
    let [candidate] := ConnectionStaticRoutes.deliveryCandidates routing site | none
    let request ← SourceOccurrences.requestAt routing.snapshot routing.context candidate.draw
    if request.sort ≠ service.request.sort then none else pure ()
    let context := routing.context.mapReplacement fun replacement =>
      { replacement with request := some request }
    let message ← OccurrenceResolution.resolve routing.snapshot context
      (context.message site sender context.producer) frames [candidate.message]
    let query ← OccurrenceResolution.resolve routing.snapshot context
      (context.query (candidate.draw.qualify (candidate.draw.event[2]?.getD "")) request)
      frames [candidate.draw]
    pure (request, query, message)) = _
  rw [binding.selected]
  simp only [bind, Option.bind, binding.sourceRequest, ne_eq, not_true_eq_false,
    ↓reduceIte, pure]
  simp only [Context.mapReplacement] at resolvedMessage resolvedQuery ⊢
  rw [resolvedMessage, resolvedQuery]

theorem Delivery.receive {routing : Original.Routing} {sites : List String} {site : String}
    {service : Service} {sender : Nat} {query message : Template}
    (binding : Delivery routing sites site service sender query message)
    {carriers : Carriers} (state : Original.State carriers)
    (same : state.frames.map (·.site) = sites) (mode : routing.mode = .producer) :
    Original.receive routing state service.request.sort site sender =
      (Original.queryRequest state
        (Domain.atCoordinates ((service.routeContext routing.context).query
          (query.qualify (query.event[2]?.getD "")) service.request)
          (state.frames.map (·.index))) service.request).bind fun source =>
        match Domain.Payload.ofValue service.request.sort source.1 with
        | none => .halt .refused
        | some payload =>
          (Original.record source.2
            (Domain.atCoordinates ((service.routeContext routing.context).message site sender
              routing.context.producer) (state.frames.map (·.index))) payload).bind
            (fun observed => .done (source.1, observed.2)) := by
  cases service with
  | draw field handle =>
    have fieldBinding : ConnectionStaticRoutes.Delivery routing sites site field sender query message :=
      ⟨binding.distinctQueries, binding.distinctMessages, binding.selected,
        binding.messageRoute, binding.queryRoute⟩
    have route := fieldBinding.source state.frames same
    simp only [Service.request, Service.routeContext]
    rw [Original.queryRequest_draw]
    simp only [Request.draw, Original.receive, mode, route, Domain.Payload.ofValue,
      Ty.isHandle, dite_true]
  | index contract handle bound =>
    have route := binding.typedSource state.frames same rfl
    simp only [Service.request, Request.sampleIndex, Original.receive, mode]
    unfold Original.receiveRequest
    simp only [Service.request, Request.sampleIndex] at route
    rw [route]
    rfl
  | indices contract handle bound count =>
    have route := binding.typedSource state.frames same rfl
    simp only [Service.request, Request.sampleIndices, Original.receive, mode]
    unfold Original.receiveRequest
    simp only [Service.request, Request.sampleIndices] at route
    rw [route]
    rfl


/-- Public source queries use the shared decoder before entering the actual
normal-form continuation. The finite decoder proves the reply guard. -/
theorem Public.fold {scope : Scope} {callees : List CalleeKey} {out : List Ty}
    {service : Service} {routing : Original.Routing} {sites : List String}
    {template : Template} (site : String) (context : ProtocolContext)
    (binding : Public routing sites (qualifyProtocolSite context.applicationPrefix site) service template)
    (mode : routing.mode = .validator)
    (next : Form [] callees (.value service.request.sort :: scope) out)
    (model : DomainModel) (tables : Tables model (Occurrence.signature model.toCarriers))
    (runs : Runs model (Occurrence.signature model.toCarriers))
    (processes : CalleeProcesses model callees (Occurrence.signature model.toCarriers))
    (binders : Binders model scope) (state : Original.State model.toCarriers)
    (same : state.frames.map (·.site) = sites) :
    Original.fold routing ((service.form site next).denoteOn model Occurrence.actions tables
      (LawResults.empty model) context runs processes binders) state =
      (Original.queryRequest state
        (Domain.atCoordinates ((service.routeContext routing.context).query
          (qualifyProtocolSite context.applicationPrefix site) service.request)
          (state.frames.map (·.index))) service.request).bind fun source =>
        Original.fold routing (next.denoteOn model Occurrence.actions tables
          (LawResults.empty model) context runs processes (.cons source.1 binders)) source.2 := by
  rw [service.fold_form binding.valid, binding.source state same mode]
  simp only [Original.queryRequest, PIR.Process.bind_assoc, PIR.Process.bind]
  exact service.request_checked binding.valid _ _ _

/-- Private requests preserve the reached source state and history. -/
theorem Local.fold {scope : Scope} {callees : List CalleeKey} {out : List Ty}
    {service : Service} {routing : Original.Routing} {sites : List String}
    {template : Template} {port : ServicePort} (site : String) (context : ProtocolContext)
    (binding : Local routing sites (qualifyProtocolSite context.applicationPrefix site) service port template)
    (mode : LocalMode routing sites (qualifyProtocolSite context.applicationPrefix site) service)
    (next : Form [] callees (.value service.request.sort :: scope) out)
    (model : DomainModel) (tables : Tables model (Occurrence.signature model.toCarriers))
    (runs : Runs model (Occurrence.signature model.toCarriers))
    (processes : CalleeProcesses model callees (Occurrence.signature model.toCarriers))
    (binders : Binders model scope) (state : Original.State model.toCarriers)
    (same : state.frames.map (·.site) = sites) :
    Original.fold routing ((service.form site next).denoteOn model Occurrence.actions tables
      (LawResults.empty model) context runs processes binders) state =
      (service.action routing state (qualifyProtocolSite context.applicationPrefix site)).bind fun source =>
        Original.fold routing (next.denoteOn model Occurrence.actions tables
          (LawResults.empty model) context runs processes (.cons source.1 binders)) source.2 := by
  rw [service.fold_form binding.valid]
  rw [service.localAction routing state _ port _ (mode.sound _ same)
    (binding.source _ same) binding.nominal binding.valid
    (by rw [OccurrenceResolution.atCoordinates_request]; rfl)]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind]
  exact service.request_checked binding.valid _ _ _

end Zkc.Construction.ConnectionServiceRequests
