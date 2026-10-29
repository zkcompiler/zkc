module

public import Zkc.Construction.Uniform.ScalarSupport
public import Zkc.Construction.Uniform.ScalarProjection

@[expose] public section

/-! Scalar presentation derived from independent reached-source coverage. There
is no per-protocol route, frame or instruction correspondence in this proof. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
namespace Zkc.Construction.Uniform.ScalarObservation
open Zkc.Source Zkc.Source.Structured
open ScalarSupport ScalarProjection
variable {F G A : Type}

private theorem resolved_key {routing : Original.Routing} {frames : Original.Frames}
    {expected origin : Origin} {candidates : List Template} {repeated : Bool}
    (empty : repeated = false → frames = []) (static : expected.event.length = 6)
    (resolved : OccurrenceResolution.resolve routing.snapshot routing.context expected frames candidates = some origin) :
    key repeated origin = expected := by
  rw [OccurrenceResolution.resolved_origin resolved]
  cases repeated with
  | false => rw [empty rfl]; rfl
  | true => exact Origin.withoutCoordinates_atCoordinates expected _ static

private theorem message_key {routing : Original.Routing} {frames : Original.Frames}
    {site : String} {sender receiver : Nat} {origin : Origin} {repeated : Bool}
    (empty : repeated = false → frames = [])
    (resolved : routing.message frames site sender receiver = some origin) :
    key repeated origin = routing.context.message site sender receiver :=
  resolved_key empty rfl resolved

private theorem draw_key {routing : Original.Routing} {frames : Original.Frames}
    {site field : String} {handle : Nat} {origin : Origin} {repeated : Bool}
    (empty : repeated = false → frames = [])
    (resolved : routing.draw frames site field handle = some origin) :
    key repeated origin = routing.context.query site (.draw field) := by
  unfold Original.Routing.draw at resolved
  split at resolved
  · exact resolved_key empty rfl resolved
  · cases resolved

private theorem fold_call (routing : Original.Routing)
    (op : (Occurrence.signature (uniformCarriers F G)).Op)
    (next : (Occurrence.signature (uniformCarriers F G)).Reply op →
      PIR.Process (Occurrence.signature (uniformCarriers F G)) A)
    (state : Original.State (uniformCarriers F G)) :
    Original.fold routing (.call op next) state =
      (Original.operations routing op state).bind fun result =>
        Original.fold routing (next result.1) result.2 := rfl

/-- Coverage supplies every route and nominal identity. Support supplies only
scalar representability and the artifact's iteration restriction. The relation
retains the whole source result, final stack and complete projected history. -/
theorem simulation {routing : Original.Routing} {repeated : Bool}
    (mode : routing.mode = .validator) (replacement : Replacement)
    (profile : routing.context.profile = .fiatShamir replacement)
    (noLocal : routing.locals = [])
    {frames final : Original.Frames}
    {source : PIR.Process (Occurrence.signature (uniformCarriers F G)) A}
    (covered : Original.RouteCoverage routing frames final source)
    (supported : Supported repeated source)
    (empty : repeated = false → frames = [])
    (suffix : Domain.History (uniformCarriers F G)) :
    Nonempty (Original.Simulation
      (fun scalar actual => scalar.1 = actual.1 ∧ actual.2.frames = final ∧
        scalar.2 = history repeated actual.2.history)
      (fun _ _ => True)
      (SourceProcess.sourceView routing.context
        ((source.interpret Occurrence.erase).interpret CommonAdapter.project) (history repeated suffix))
      ((Original.fold routing source ⟨frames, suffix⟩).interpret (operations repeated))) := by
  induction covered generalizing suffix with
  | done => unfold Original.fold; exact ⟨.done ⟨rfl, rfl, rfl⟩⟩
  | halt => unfold Original.fold; exact ⟨.halt _⟩
  | enter frames final frame tail ih =>
      cases supported with
      | enter _ allowed support =>
        have current := ih support (by intro impossible; simp_all) suffix
        simpa only [fold_call, Original.operations,
          PIR.Process.bind, PIR.Process.interpret, Occurrence.erase] using current
  | leave frames final frame last tail ih =>
      cases supported with
      | leave _ support =>
        have current := ih support (by intro h; rw [empty h]; rfl) suffix
        simpa only [fold_call, Original.operations, last,
          ↓reduceIte, PIR.Process.bind, PIR.Process.interpret, Occurrence.erase] using current
  | action frames final operation covered tail ih =>
      cases supported with
      | action _ allowed support =>
        cases operation with
        | receive ty site sender =>
          have present : ty.isHandle = false ∧ ∃ origin,
              routing.message frames site sender routing.context.validator = some origin := by
            simpa only [Original.ActionCovered, mode, profile, Original.Routing.self] using covered
          obtain ⟨_, origin, route⟩ := present
          have mapped := message_key empty route
          cases allowed with
          | boolean =>
            simp only [fold_call, Original.operations, profile,
              Original.receive, mode, route, PIR.Process.bind, PIR.Process.interpret,
              Occurrence.erase, CommonAdapter.project, SourceProcess.sourceView,
              SourceProcess.receive, operations]
            refine ⟨Original.Simulation.call _ (fun reply => ?_)⟩
            simp only [Domain.Payload.ofValue, Ty.isHandle, ↓reduceDIte, Original.record,
              PIR.Process.bind, PIR.Process.interpret, operations, event, mapped]
            rw [mapped]
            refine Original.Simulation.call _ (fun ignored => ?_)
            have current := ih reply (support reply) empty (suffix ++ [.message origin (.boolean reply)])
            simpa only [history, List.map_append, List.map_cons, List.map_nil, event, mapped] using Classical.choice current
          | field name =>
            simp only [fold_call, Original.operations, profile,
              Original.receive, mode, route, PIR.Process.bind, PIR.Process.interpret,
              Occurrence.erase, CommonAdapter.project, SourceProcess.sourceView,
              SourceProcess.receive, operations]
            refine ⟨Original.Simulation.call _ (fun reply => ?_)⟩
            simp only [Domain.Payload.ofValue, Ty.isHandle, ↓reduceDIte, Original.record,
              PIR.Process.bind, PIR.Process.interpret, operations, event, mapped]
            rw [mapped]
            refine Original.Simulation.call _ (fun ignored => ?_)
            have current := ih reply (support reply) empty (suffix ++ [.message origin (.field name reply)])
            simpa only [history, List.map_append, List.map_cons, List.map_nil, event, mapped] using Classical.choice current
          | group name =>
            simp only [fold_call, Original.operations, profile,
              Original.receive, mode, route, PIR.Process.bind, PIR.Process.interpret,
              Occurrence.erase, CommonAdapter.project, SourceProcess.sourceView,
              SourceProcess.receive, operations]
            refine ⟨Original.Simulation.call _ (fun reply => ?_)⟩
            simp only [Domain.Payload.ofValue, Ty.isHandle, ↓reduceDIte, Original.record,
              PIR.Process.bind, PIR.Process.interpret, operations, event, mapped]
            rw [mapped]
            refine Original.Simulation.call _ (fun ignored => ?_)
            have current := ih reply (support reply) empty (suffix ++ [.message origin (.group name reply)])
            simpa only [history, List.map_append, List.map_cons, List.map_nil, event, mapped] using Classical.choice current
        | send site receiver value =>
          have present := covered
          simp only [Original.ActionCovered, mode, Original.Routing.self] at present
          obtain ⟨_, origin, route⟩ := present
          have mapped := message_key empty route
          cases allowed with
          | boolean =>
            simp only [fold_call, Original.operations, profile,
              Original.send, mode, route, Domain.Payload.ofValue, Ty.isHandle, ↓reduceDIte,
              Original.record, PIR.Process.bind, PIR.Process.interpret, Occurrence.erase,
              CommonAdapter.project, SourceProcess.sourceView, SourceProcess.send,
              Payload.ofValue, DomainAdapter.embedPayload, operations, event, mapped]
            rw [mapped]
            refine ⟨Original.Simulation.call _ (fun ignored => ?_)⟩
            have current := ih () (support ()) empty (suffix ++ [.message origin (.boolean value)])
            simpa only [history, List.map_append, List.map_cons, List.map_nil, event, mapped] using Classical.choice current
          | field name =>
            simp only [fold_call, Original.operations, profile,
              Original.send, mode, route, Domain.Payload.ofValue, Ty.isHandle, ↓reduceDIte,
              Original.record, PIR.Process.bind, PIR.Process.interpret, Occurrence.erase,
              CommonAdapter.project, SourceProcess.sourceView, SourceProcess.send,
              Payload.ofValue, DomainAdapter.embedPayload, operations, event, mapped]
            rw [mapped]
            refine ⟨Original.Simulation.call _ (fun ignored => ?_)⟩
            have current := ih () (support ()) empty (suffix ++ [.message origin (.field name value)])
            simpa only [history, List.map_append, List.map_cons, List.map_nil, event, mapped] using Classical.choice current
          | group name =>
            simp only [fold_call, Original.operations, profile,
              Original.send, mode, route, Domain.Payload.ofValue, Ty.isHandle, ↓reduceDIte,
              Original.record, PIR.Process.bind, PIR.Process.interpret, Occurrence.erase,
              CommonAdapter.project, SourceProcess.sourceView, SourceProcess.send,
              Payload.ofValue, DomainAdapter.embedPayload, operations, event, mapped]
            rw [mapped]
            refine ⟨Original.Simulation.call _ (fun ignored => ?_)⟩
            have current := ih () (support ()) empty (suffix ++ [.message origin (.group name value)])
            simpa only [history, List.map_append, List.map_cons, List.map_nil, event, mapped] using Classical.choice current
        | query site field arguments =>
          change String at field
          cases arguments with
          | cons handle rest =>
            cases rest
            have publicRoute : ∃ origin, routing.draw frames site field handle = some origin ∧
                origin.request = some (.draw field) := by
              rcases covered with publicRoute | localRoute
              · exact publicRoute.2
              · obtain ⟨port, origin, route, _⟩ := localRoute
                simp [Original.Routing.local, noLocal] at route
            obtain ⟨origin, route, request⟩ := publicRoute
            have mapped := draw_key empty route
            rcases origin with ⟨entry, events, actualRequest⟩
            change actualRequest = some (.draw field) at request
            subst actualRequest
            simp only [fold_call, Original.operations,
              Original.query, mode, route, Original.queryField, ↓reduceDIte,
              PIR.Process.bind, PIR.Process.interpret, Occurrence.erase, CommonAdapter.project,
              SourceProcess.sourceView, SourceProcess.query, operations]
            have entryKey := congrArg Origin.entry mapped
            have eventKey := congrArg Origin.event mapped
            dsimp only [key, Context.query, Origin.query] at entryKey eventKey
            subst entry
            simp only [key, eventKey, Context.query, Origin.query,
              Domain.Raw, Request.draw, eq_mpr_eq_cast, cast_eq]
            simp only [Request.draw] at eventKey
            rw [eventKey]
            refine ⟨Original.Simulation.call _ (fun reply => ?_)⟩
            have current := ih reply (support reply) empty
              (suffix ++ [.challenge ⟨routing.context.entry, events, some (.draw field)⟩])
            simpa only [history, List.map_append, List.map_cons, List.map_nil, event, mapped,
              key, eventKey, Context.query, Origin.query, Domain.Raw, Request.draw,
              eq_mpr_eq_cast, eq_mp_eq_cast, cast_eq] using Classical.choice current

end Zkc.Construction.Uniform.ScalarObservation
