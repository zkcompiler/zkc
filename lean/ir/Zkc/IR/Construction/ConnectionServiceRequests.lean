module

public import Zkc.IR.Construction.ConnectionActionSupport
public import Zkc.IR.Construction.ServiceConnection

@[expose] public section

/-! Finite typed requests for the existing connection engine. Source operands
are literal values in the existing total-term language. Physical references
are checked separately, including the scalar provider's dynamic bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Zkc.Construction.ConnectionServiceRequests
open Zkc.Source Zkc.Source.Structured NormalForm ConnectionFrame

abbrev ServiceBlock := (model : DomainModel) → Domain.View.Block model.toCarriers

inductive Service where
  | draw (field : String) (handle : Nat)
  | index (contract : String) (handle bound : Nat)
  | indices (contract : String) (handle bound count : Nat)
  deriving DecidableEq, Repr

def Service.request : Service → Request
  | .draw field _ => .draw field
  | .index _ _ bound => .sampleIndex bound
  | .indices _ _ bound count => .sampleIndices bound count

def Service.contract : Service → String
  | .draw field _ => "random." ++ field ++ "/0"
  | .index contract .. | .indices contract .. => contract

def Service.handle : Service → Nat
  | .draw _ handle | .index _ handle _ | .indices _ handle .. => handle

def Service.operation : Service → ServiceOp
  | .draw field _ => .draw field
  | .index contract .. => .sampleIndex contract
  | .indices contract .. => .sampleIndices contract

def Service.arguments {scope : Scope} (service : Service) :
    Terms [] scope service.operation.arguments :=
  match service with
  | .draw field handle => .cons (.capability ("random." ++ field ++ "/0") handle) .nil
  | .index contract handle bound =>
      .cons (.capability contract handle) (.cons (.index bound) .nil)
  | .indices contract handle bound count =>
      .cons (.capability contract handle) (.cons (.index bound) (.cons (.index count) .nil))

theorem Service.request_evaluated (service : Service) (model : DomainModel)
    {scope : Scope} (binders : Binders model scope) :
    Request.ofService service.operation (service.arguments.eval (LawResults.empty model) binders) =
      service.request := by cases service <;> rfl

theorem Service.result (service : Service) : service.operation.result = service.request.sort := by
  cases service <;> rfl

def Service.form {scope : Scope} {callees : List CalleeKey} {out : List Ty}
    (service : Service) (site : String)
    (next : Form [] callees (.value service.request.sort :: scope) out) : Form [] callees scope out :=
  match service with
  | .draw field handle => .query site (.draw field)
      (.cons (.capability ("random." ++ field ++ "/0") handle) .nil) next
  | .index contract handle bound => .query site (.sampleIndex contract)
      (.cons (.capability contract handle) (.cons (.index bound) .nil)) next
  | .indices contract handle bound count => .query site (.sampleIndices contract)
      (.cons (.capability contract handle) (.cons (.index bound) (.cons (.index count) .nil))) next

theorem Service.form_callsMatch {scope : Scope} {callees : List CalleeKey} {out : List Ty}
    (service : Service) (site : String)
    (next : Form [] callees (.value service.request.sort :: scope) out) :
    (service.form site next).CallsMatch = next.CallsMatch := by cases service <;> rfl

/-- Specialize one actual source action; this adds no source evaluator. -/
def Service.action {carriers : Carriers} (service : Service) (routing : Original.Routing)
    (state : Original.State carriers) (site : String) :
    PIR.Process (Domain.effects carriers) (carriers.Value service.request.sort × Original.State carriers) :=
  match service with
  | .draw field handle => Original.query routing state site field handle
  | .index contract handle bound =>
      Original.service routing state site contract (.sampleIndex bound) handle
  | .indices contract handle bound count =>
      Original.service routing state site contract (.sampleIndices bound count) handle

def Service.replyCheck {carriers : Carriers} (service : Service) :
    carriers.Value service.request.sort → Bool :=
  match service with
  | .draw _ _ => fun _ => true
  | .index contract handle bound => fun value =>
      (ServiceOp.sampleIndex contract).validReply (.cons handle (.cons bound .nil)) value
  | .indices contract handle bound count => fun value =>
      (ServiceOp.sampleIndices contract).validReply
        (.cons handle (.cons bound (.cons count .nil))) value

theorem Service.replyCheck_decode {carriers : Carriers} (service : Service)
    (valid : service.request.valid = true) (raw : Request.Raw carriers service.request)
    (value : carriers.Value service.request.sort) (decoded : service.request.decode raw = some value) :
    service.replyCheck value = true := by
  cases service with
  | draw field handle => rfl
  | index contract handle bound =>
    have positive : 0 < bound := by
      have := valid
      simp only [Service.request, Request.sampleIndex, Request.valid, Bool.and_eq_true,
        decide_eq_true_eq] at this
      exact this.1
    have same : raw.val = value := Option.some.inj decoded
    subst value
    simpa only [Service.replyCheck] using
      (Request.index_reply_valid (carriers := carriers) contract handle bound positive raw)
  | indices contract handle bound count =>
    have positive : 0 < bound := by
      have := valid
      simp only [Service.request, Request.sampleIndices, Request.valid, Bool.and_eq_true,
        decide_eq_true_eq] at this
      exact this.1.1.1
    have same : List.ofFn (fun i => (raw i).val) = value := Option.some.inj decoded
    subst value
    change (ServiceOp.sampleIndices contract).validReply (carriers := carriers)
      (.cons handle (.cons bound (.cons count .nil))) (List.ofFn fun i => (raw i).val) = true
    exact
      (Request.block_reply_valid (carriers := carriers) contract handle bound count positive raw)

/-- The actual decoder discharges the source reply check for every raw reply,
including local and public stops. No model equation is an input. -/
theorem Service.request_checked {carriers : Carriers} {A : Type}
    (service : Service) (valid : service.request.valid = true) (origin : Origin)
    (effect : Domain.Effect carriers) (next : carriers.Value service.request.sort →
      PIR.Process (Domain.effects carriers) A) :
    (Domain.requestValue origin service.request effect).bind (fun value =>
      if service.replyCheck value then next value else .halt .refused) =
      (Domain.requestValue origin service.request effect).bind next := by
  unfold Domain.requestValue
  rw [ite_eq_left valid]
  split
  · cases effect <;> try rfl
    all_goals
      simp only [PIR.Process.bind]
      congr 1
      funext raw
      split
      · rename_i value decoded
        simp only [PIR.Process.bind, service.replyCheck_decode valid _ value decoded, ite_true]
      · rfl
  · rfl

theorem Service.fold_form {scope : Scope} {callees : List CalleeKey} {out : List Ty}
    (service : Service) (valid : service.request.valid = true)
    (routing : Original.Routing) (site : String)
    (next : Form [] callees (.value service.request.sort :: scope) out)
    (model : DomainModel) (tables : Tables model (Occurrence.signature model.toCarriers))
    (context : ProtocolContext) (runs : Runs model (Occurrence.signature model.toCarriers))
    (processes : CalleeProcesses model callees (Occurrence.signature model.toCarriers))
    (binders : Binders model scope) (state : Original.State model.toCarriers) :
    Original.fold routing ((service.form site next).denoteOn model Occurrence.actions tables
      (LawResults.empty model) context runs processes binders) state =
      (service.action routing state (qualifyProtocolSite context.applicationPrefix site)).bind
        (fun source => if service.replyCheck source.1 then
          Original.fold routing (next.denoteOn model Occurrence.actions tables
            (LawResults.empty model) context runs processes (.cons source.1 binders)) source.2
          else .halt .refused) := by
  cases service <;>
    simp only [Service.request, Request.draw, Request.sampleIndex, Request.sampleIndices,
      Request.valid] at valid
  all_goals
    simp only [Service.form, Form.denoteOn, Form.denoteWithOn, Terms.eval, Term.eval,
      serviceAction]
    simp only [ServiceOp.validInputs, ServiceOp.contract,
      ServiceOp.result, valid, ite_true]
    simp only [PIR.Process.interpret, Occurrence.actions, PIR.Process.bind,
      Original.fold, PIR.Process.interpretState, Original.operations, Service.action,
      Service.replyCheck]
  all_goals congr 1
  all_goals funext source
  all_goals simp only [ServiceOp.validReply, ServiceOp.result, ServiceOp.contract]
  all_goals split_ifs <;> simp_all [PIR.Process.interpret, PIR.Process.bind,
    PIR.Process.interpretState]

def Service.routeContext (service : Service) (context : Context) : Context :=
  match service with
  | .draw .. => context
  | _ => context.mapReplacement fun replacement =>
      { replacement with request := some service.request }

def Service.candidates (service : Service) (routing : Original.Routing) : List Template :=
  match service with
  | .draw .. => routing.draws
  | _ => routing.draws.filter fun template =>
      SourceOccurrences.requestAt routing.snapshot routing.context template == some service.request

structure Public (routing : Original.Routing) (sites : List String)
    (site : String) (service : Service) (template : Template) where
  selected : service.handle = routing.selectedHandle
  publicService : routing.context.service.isSome = true
  valid : service.request.valid = true
  nominal : service.contract = routing.context.contract
  route : OccurrenceResolution.resolveStatic routing.snapshot (service.routeContext routing.context)
    ((service.routeContext routing.context).query site service.request) sites
    (service.candidates routing) = some template

theorem Public.source {routing : Original.Routing} {sites : List String} {site : String}
    {service : Service} {template : Template} (binding : Public routing sites site service template)
    {carriers : Carriers} (state : Original.State carriers)
    (same : state.frames.map (·.site) = sites) (mode : routing.mode = .validator) :
    service.action routing state site = Original.queryRequest state
      (Domain.atCoordinates ((service.routeContext routing.context).query site service.request)
        (state.frames.map (·.index))) service.request := by
  have route := OccurrenceResolution.resolve_of_static binding.route state.frames same
  cases service with
  | draw field handle =>
    rw [Service.action, Original.query, mode]
    have found : routing.draw state.frames site field handle = some
        (Domain.atCoordinates (routing.context.query site (.draw field))
          (state.frames.map (·.index))) := by
      simp only [Original.Routing.draw, ← binding.selected, Service.handle, binding.publicService,
        and_self, ↓reduceIte]
      exact route
    simp only [found, Service.request, Service.routeContext]
    rw [Original.queryRequest_draw]
  | index contract handle bound =>
    apply Original.service_public _ _ _ _ _ _ _ mode binding.nominal
    simp only [Original.Routing.serviceRequest, ← binding.selected, Service.handle,
      binding.publicService, show (Request.sampleIndex bound).valid = true from binding.valid,
      and_self, ↓reduceIte]
    exact route
  | indices contract handle bound count =>
    apply Original.service_public _ _ _ _ _ _ _ mode binding.nominal
    simp only [Original.Routing.serviceRequest, ← binding.selected, Service.handle,
      binding.publicService, show (Request.sampleIndices bound count).valid = true from binding.valid,
      and_self, ↓reduceIte]
    exact route

/-- The finite physical shape, independent of the source term witness. -/
inductive Challenge {scope : Scope} (layout : Layout scope) (context : Context)
    (template : Template) (state path : Nat) : Service → ServiceBlock → Type 1 where
  | draw (field : String) (handle : Nat)
      (nominal : context.contract = "random." ++ field ++ "/0")
      (selected : context.request = some (.draw field)) :
      Challenge layout context template state path (.draw field handle)
      (fun _ => Domain.View.challenge context context.suite field template state path
        [.data (.field field), .transcript context.suite])
  | index (contract : String) (handle bound reference : Nat)
      (read : layout[reference]? = some (.data (.present (.index bound)))) :
      Challenge layout context template state path (.index contract handle bound)
        (fun _ => Domain.View.indexChallenge context context.suite bound template state reference path
          [.data .index, .transcript context.suite])
  | indices (contract : String) (handle bound count : Nat) :
      Challenge layout context template state path (.indices contract handle bound count)
        (fun _ => Domain.View.blockChallenge context context.suite bound count template state path
          [.data .indices, .transcript context.suite])

theorem Service.data (service : Service) : service.request.sort.isHandle = false := by
  cases service <;> rfl

def Returned {carriers : Carriers} (request : Request) (suite : String)
    (state : Original.State carriers) (origin : Origin) (environment : Domain.Environment carriers)
    (source : carriers.Value request.sort × Original.State carriers)
    (target : Domain.Environment carriers) : Prop :=
  source.2 = { state with history := state.history ++ [.challenge origin] } ∧
    ∃ encoded, Domain.Value.encode request.sort source.1 = some encoded ∧
      target = environment ++ [encoded,
        .transcript suite (state.history ++ [.challenge origin])]

theorem Returned.frame {model : DomainModel} {scope : Scope} {binders : Binders model scope}
    {layout : Layout scope} {request : Request} {suite : String}
    {state : Original.State model.toCarriers} {origin : Origin}
    {environment target : Domain.Environment model.toCarriers}
    {source : model.Value request.sort × Original.State model.toCarriers}
    (returned : Returned request suite state origin environment source target)
    (related : Holds model binders state.history layout environment) :
    Holds model (.cons source.1 binders) source.2.history
      ((layout.map Cell.retireHistory).map (Cell.rename .there) ++
        [.data (.present (.var .here)), .history suite]) target := by
  obtain ⟨same, encoded, value, appended⟩ := returned
  rw [same, appended]
  exact ((related.retireHistory _).rename .there (fun _ => rfl)).append
    (.cons ⟨source.1, rfl, value⟩ (.cons rfl .nil))

/-- One target shape theorem consumes every decoded reply of the shared
request kernel. The field branch is the exact existing field statement. -/
noncomputable def Challenge.simulation {scope : Scope} {layout : Layout scope}
    {context : Context} {template : Template} {stateRef pathRef : Nat}
    {service : Service} {target : ServiceBlock}
    (shape : Challenge layout context template stateRef pathRef service target)
    (model : DomainModel) (binders : Binders model scope)
    (state : Original.State model.toCarriers) (environment : Domain.Environment model.toCarriers)
    (related : Holds model binders state.history layout environment)
    (stateRead : layout[stateRef]? = some (.history context.suite))
    (path : List Nat) (pathRead : environment[pathRef]? = some (.indices path))
    (origin : Origin) (asked : origin.request = some service.request)
    (valid : service.request.valid = true) (supported : service.request.nativeSupported = true)
    (_nominal : service.contract = context.contract) (publicService : context.service.isSome = true)
    (resolved : Domain.templateOrigin (service.routeContext context) template path = some origin) :
    Original.Simulation (Returned service.request context.suite state origin environment)
      (fun _ frame => frame = environment)
      (Original.queryRequest state origin service.request) (target model environment) := by
  cases shape with
  | draw field handle contract selected =>
    change Domain.templateOrigin context template path = some origin at resolved
    change origin.request = some (.draw field) at asked
    simp only [Service.request]
    rw [Original.queryRequest_draw]
    apply (Original.Simulation.queryField state origin field asked context context.suite template
      stateRef pathRef environment path (related.readHistory stateRead) pathRead
      (by rw [Domain.queryOrigin, ite_eq_left ⟨rfl, contract, selected⟩, resolved];
          exact ite_eq_left asked)).mapRelations
    · intro source target returned
      exact ⟨returned.1, .data (.field field source.1), rfl, returned.2⟩
    · intro _ _ same
      exact same
  | index contract handle bound reference read =>
    simpa only [PIR.Process.bind_done, Service.request, Domain.View.indexChallenge, Request.sampleIndex] using
      (Original.Simulation.challenge context context.suite (.sampleIndex bound) template
      stateRef pathRef [reference] state environment path origin
      (Returned (.sampleIndex bound) context.suite state origin environment)
      (fun _ frame => frame = environment) PIR.Process.done PIR.Process.done
      (related.readHistory stateRead) pathRead
      ⟨rfl, publicService, valid, rfl, by
        simp [Domain.requestOperands, related.index read, Request.sampleIndex, Term.eval], supported⟩ resolved (by
        intro value
        exact .done ⟨rfl, .data (.index value), rfl, rfl⟩))
  | indices contract handle bound count =>
    simpa only [PIR.Process.bind_done, Service.request, Domain.View.blockChallenge, Request.sampleIndices] using
      (Original.Simulation.challenge context context.suite (.sampleIndices bound count) template
      stateRef pathRef [] state environment path origin
      (Returned (.sampleIndices bound count) context.suite state origin environment)
      (fun _ frame => frame = environment) PIR.Process.done PIR.Process.done
      (related.readHistory stateRead) pathRead
      ⟨rfl, publicService, valid, rfl, rfl, supported⟩ resolved (by
        intro value
        exact .done ⟨rfl, .data ⟨.indices, rfl, value⟩, rfl, rfl⟩))

end Zkc.Construction.ConnectionServiceRequests
