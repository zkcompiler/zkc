module

public import Zkc.IR.Construction.OriginalSimulation
public import Zkc.IR.Construction.DomainCorrespondence

@[expose] public section

/-! Typed service connection laws in the existing source fold and constructed
Process model. These are decoded semantic equations, not native byte receipts.
Requests keep evaluated operands; dynamic instruction references are separate. -/
set_option autoImplicit false
namespace Zkc.Construction
open Zkc.Source

namespace Request

/-- The finite ideal decoder satisfies the checked adversarial source reply
contract for a positive scalar bound. This is not a distribution assumption. -/
theorem index_reply_valid {carriers : Structured.Carriers} (contract : String)
    (handle bound : Nat) (positive : 0 < bound) (value : Fin (replyBound bound)) :
    (Structured.ServiceOp.sampleIndex contract).validReply (carriers := carriers)
      (.cons handle (.cons bound .nil)) value.val = true := by
  change decide (value.val < bound) = true
  rw [decide_eq_true_eq]
  simpa only [replyBound_of_positive positive] using value.isLt

/-- A block is one finite reply with exactly count entries. Its coordinate
values satisfy the same bounded contract without splitting it into queries. -/
theorem block_reply_valid {carriers : Structured.Carriers} (contract : String)
    (handle bound count : Nat) (positive : 0 < bound)
    (values : Fin count → Fin (replyBound bound)) :
    (Structured.ServiceOp.sampleIndices contract).validReply (carriers := carriers)
      (.cons handle (.cons bound (.cons count .nil))) (List.ofFn fun i => (values i).val) = true := by
  change ((List.ofFn fun i => (values i).val).length == count &&
    (List.ofFn fun i => (values i).val).all (· < bound)) = true
  simp only [List.length_ofFn, BEq.rfl, Bool.true_and,
    List.all_eq_true, decide_eq_true_eq]
  exact decoded_block_bounded bound count positive values

def ofService {carriers : Structured.Carriers} (operation : Structured.ServiceOp) :
    Values carriers.Value operation.arguments → Request :=
  match operation with
  | .draw field => fun _ => .draw field
  | .sampleIndex _ => fun | .cons _ (.cons bound .nil) => .sampleIndex bound
  | .sampleIndices _ => fun | .cons _ (.cons bound (.cons count .nil)) => .sampleIndices bound count

theorem ofService_sort {carriers : Structured.Carriers} (operation : Structured.ServiceOp)
    (args : Values carriers.Value operation.arguments) :
    (ofService operation args).sort = operation.result := by
  cases operation with
  | draw => cases args with | cons _ rest => cases rest; rfl
  | sampleIndex =>
    cases args with | cons _ rest =>
      cases rest with | cons _ rest => cases rest; rfl
  | sampleIndices =>
    cases args with | cons _ rest =>
      cases rest with | cons _ rest =>
        cases rest with | cons _ rest => cases rest; rfl

theorem ofService_valid {carriers : Structured.Carriers} (operation : Structured.ServiceOp)
    (args : Values carriers.Value operation.arguments) :
    (ofService operation args).valid = operation.validInputs args := by
  cases operation with
  | draw => cases args with | cons _ rest => cases rest; rfl
  | sampleIndex =>
    cases args with | cons _ rest =>
      cases rest with | cons _ rest => cases rest; rfl
  | sampleIndices =>
    cases args with | cons _ rest =>
      cases rest with | cons _ rest =>
        cases rest with | cons _ rest => cases rest; rfl

end Request

namespace Domain
variable {carriers : Structured.Carriers}

/-- Reduce a checked constructed query to the shared request kernel. Dynamic
scalar operands and static block parameters have already been checked against
the same evaluated request; source association remains an independent premise. -/
theorem challengeRequest_of_checks (context : Context) (suite : String) (request : Request)
    (template : Template) (state coordinates : Nat) (references : List Nat)
    (env : Environment carriers) (history : History carriers) (path : List Nat) (origin : Origin)
    (transcript : env[state]? = some (.transcript suite history))
    (indices : env[coordinates]? = some (.indices path))
    (checks : suite = context.suite ∧ context.service.isSome ∧ request.valid ∧
      (request.operation context.contract).isSome ∧
      (if request.method = "index" then requestOperands env references request else references.isEmpty) ∧
      request.nativeSupported)
    (found : templateOrigin (context.mapReplacement fun replacement =>
      { replacement with request := some request }) template path = some origin) :
    challengeRequest context suite request template state coordinates references
      [.data request.sort, .transcript suite] env =
      (requestValue origin request (.query history origin)).bind (fun value =>
        match Value.encode request.sort value with
        | some encoded => .done (env ++ [encoded, .transcript suite (history ++ [.challenge origin])])
        | none => .halt .refused) := by
  simp [challengeRequest, transcript, indices, checks.1, checks.2.1, checks.2.2.1,
    checks.2.2.2.1, checks.2.2.2.2.1, checks.2.2.2.2.2, found]
  rfl

/-- Private requests use the same decoder after their actual operand values
and complete dynamic ancestry have been checked. No public history is added. -/
theorem localRequest_of_checks (context : Context) (port : ServicePort) (request : Request)
    (template : Template) (coordinates references : List Nat) (env : Environment carriers)
    (path : List Nat) (origin : Origin)
    (checks : request.valid ∧ (request.operation port.contract).isSome ∧ requestOperands env references request)
    (indices : localCoordinates env coordinates = some path)
    (found : localOrigin context port request template path = some origin) :
    localRequest context port request template coordinates references [.data request.sort] env =
      (requestValue origin request (.localService port origin)).bind (fun value =>
        match Value.encode request.sort value with
        | some encoded => .done (env ++ [encoded])
        | none => .halt .refused) := by
  simp [localRequest, checks.1, checks.2.1, checks.2.2, indices, found]
  rfl

/-- Invalid formation and mismatched request identity refuse before querying. -/
theorem requestValue_invalid (origin : Origin) (request : Request)
    (invalid : request.valid = false) (effect : Effect carriers) :
    requestValue origin request effect = .halt .refused := by
  simp [requestValue, invalid]

theorem requestValue_mismatch (origin : Origin) (request : Request)
    (different : origin.request ≠ some request) (effect : Effect carriers) :
    requestValue origin request effect = .halt .refused := by
  simp [requestValue, different]

/-- The literal query carrier and the decoder used by both execution paths. -/
theorem requestValue_query (origin : Origin) (request : Request) (history : History carriers)
    (valid : request.valid = true) (same : origin.request = some request) :
    requestValue origin request (.query history origin) =
      .call (.query history origin) (fun raw =>
        match request.decode (by simpa only [Raw, same] using raw) with
        | some value => .done value
        | none => .halt .refused) := by
  simp only [requestValue, valid, ite_true, same, ↓reduceDIte]
  rfl

/-- Field draw remains exactly the existing specialization for every origin,
including malformed origins. No new field interpreter is introduced. -/
theorem requestValue_draw (origin : Origin) (field : String) (history : History carriers) :
    requestValue origin (.draw field) (.query history origin) =
      if same : origin.request = some (.draw field) then
        .call (.query history origin) (fun raw =>
          .done (by simpa only [Raw, same, Request.Raw, Request.draw] using raw))
      else .halt .refused := by
  unfold requestValue
  simp only [Request.valid, Request.draw, ite_true]
  by_cases same : origin.request = some ⟨"draw", [], .field field⟩ <;>
    simp only [same, ↓reduceDIte]; rfl

end Domain

namespace Original
variable {carriers : Structured.Carriers}

/-- All source field draws use the same generic finite decoder. -/
theorem queryRequest_draw (state : State carriers) (origin : Origin) (field : String) :
    queryRequest state origin (.draw field) = queryField state origin field := by
  rw [queryRequest, Domain.requestValue_draw]
  unfold queryField
  split <;> rfl

/-- The received request comes from the checked source def-use association.
The query precedes its message observation, and every failure in either prefix
prevents the suffix. This rule applies to both typed index result forms. -/
theorem receiveRequest_of_route (routing : Routing) (state : State carriers)
    (site : String) (sender : Nat) (request : Request) (query message : Origin)
    (route : routing.typedDelivery state.frames site request.sort sender =
      some (request, query, message)) :
    receiveRequest routing state request.sort site sender =
      (Domain.requestValue query request (.query state.history query)).bind (fun value =>
        match Domain.Payload.ofValue request.sort value with
        | none => .halt .refused
        | some payload =>
          .call (.observe (.message message payload)) fun _ =>
            .done (value, { state with history :=
              state.history ++ [.challenge query, .message message payload] })) := by
  simp only [receiveRequest, route, ↓reduceDIte, queryRequest, PIR.Process.bind_assoc]
  apply congrArg (PIR.Process.bind (Domain.requestValue query request (.query state.history query)))
  funext value
  cases payload : Domain.Payload.ofValue request.sort value <;>
    simp only [PIR.Process.bind, payload, record, List.append_assoc, List.cons_append,
      List.nil_append]

/-- Exact public route, with the nominal service contract checked independently
of the request's method and values. The continuation retains actual frames. -/
theorem service_public (routing : Routing) (state : State carriers) (site contract : String)
    (request : Request) (handle : Nat) (origin : Origin)
    (mode : routing.mode = .validator) (nominal : contract = routing.context.contract)
    (route : routing.serviceRequest state.frames site request handle = some origin) :
    service routing state site contract request handle = queryRequest state origin request := by
  simp only [service, mode, nominal, ite_true, route]

/-- Private capability use preserves public history and all occurrence frames.
The separate local handler owns its complete stop and post-state behavior. -/
theorem service_local (routing : Routing) (state : State carriers) (site contract : String)
    (request : Request) (handle : Nat) (port : ServicePort) (origin : Origin)
    (mode : routing.mode = .producer)
    (route : routing.localRequest state.frames site request handle = some (port, origin))
    (nominal : port.contract = contract) :
    service routing state site contract request handle =
      (Domain.requestValue origin request (.localService port origin)).bind
        (fun value => .done (value, state)) := by
  unfold service
  rw [mode]
  cases (if contract = routing.context.contract then
      routing.serviceRequest state.frames site request handle else none) <;>
    simp [route, nominal]

/-- A private service of either role remains local when it is not the selected
public capability. Nominal ownership is independently checked by its port. -/
theorem service_local_unselected (routing : Routing) (state : State carriers) (site contract : String)
    (request : Request) (handle : Nat) (port : ServicePort) (origin : Origin)
    (unselected : routing.serviceRequest state.frames site request handle = none)
    (route : routing.localRequest state.frames site request handle = some (port, origin))
    (nominal : port.contract = contract) :
    service routing state site contract request handle =
      (Domain.requestValue origin request (.localService port origin)).bind
        (fun value => .done (value, state)) := by
  cases mode : routing.mode <;> simp [service, mode, unselected, route, nominal]

/-- The existing simulation consumes the common decoder once, including every
refusal branch. The client supplies only its live return-frame relation. -/
def Simulation.request {A B : Type} (origin : Origin) (request : Request)
    (effect : Domain.Effect carriers) (returns : A → B → Prop)
    (live : PIR.Process (Domain.effects carriers) A → Domain.Environment carriers → Prop)
    (left : carriers.Value request.sort → PIR.Process (Domain.effects carriers) A)
    (right : carriers.Value request.sort → PIR.Process (Domain.effects carriers) B)
    (tail : ∀ value, Simulation returns live (left value) (right value)) :
    Simulation returns live ((Domain.requestValue origin request effect).bind left)
      ((Domain.requestValue origin request effect).bind right) := by
  unfold Domain.requestValue
  split
  · split
    · cases effect <;> try exact .halt .refused
      all_goals
        apply Simulation.call
        intro reply
        dsimp only
        split
        · exact tail _
        · exact .halt .refused
    · exact .halt .refused
  · exact .halt .refused

/-- A local source-to-constructed simulation for the actual generic challenge
instruction. Both sides issue the identical effect at the source state's full
history. Every decoded value, refusal, and caller continuation is retained.
The live relation can carry the source occurrence ancestry and immutable frame. -/
def Simulation.challenge {A B : Type} (context : Context) (suite : String)
    (request : Request) (template : Template) (state coordinates : Nat) (references : List Nat)
    (source : State carriers) (env : Domain.Environment carriers) (path : List Nat) (origin : Origin)
    (returns : A → B → Prop)
    (live : PIR.Process (Domain.effects carriers) A → Domain.Environment carriers → Prop)
    (left : carriers.Value request.sort × State carriers → PIR.Process (Domain.effects carriers) A)
    (right : Domain.Environment carriers → PIR.Process (Domain.effects carriers) B)
    (transcript : env[state]? = some (.transcript suite source.history))
    (indices : env[coordinates]? = some (.indices path))
    (checks : suite = context.suite ∧ context.service.isSome ∧ request.valid ∧
      (request.operation context.contract).isSome ∧
      (if request.method = "index" then Domain.requestOperands env references request else references.isEmpty) ∧
      request.nativeSupported)
    (found : Domain.templateOrigin (context.mapReplacement fun replacement =>
      { replacement with request := some request }) template path = some origin)
    (tail : ∀ value, Simulation returns live
      (left (value, { source with history := source.history ++ [.challenge origin] }))
      (match Domain.Value.encode request.sort value with
       | some encoded => right (env ++ [encoded,
           .transcript suite (source.history ++ [.challenge origin])])
       | none => .halt .refused)) :
    Simulation returns live ((queryRequest source origin request).bind left)
      ((Domain.challengeRequest context suite request template state coordinates references
        [.data request.sort, .transcript suite] env).bind right) := by
  rw [Domain.challengeRequest_of_checks context suite request template state coordinates references
    env source.history path origin transcript indices checks found]
  unfold queryRequest
  rw [PIR.Process.bind_assoc, PIR.Process.bind_assoc]
  apply Simulation.request
  intro value
  cases encoded : Domain.Value.encode request.sort value <;>
    simpa only [encoded, PIR.Process.bind] using tail value

/-- Both roles' unselected private services share the common request decoder.
Every reply, local stop, unchanged public history and caller frame relation is
retained, with no transcript-query or private-sampling engine introduced. -/
def Simulation.localService {A B : Type} (routing : Routing) (source : State carriers)
    (site contract : String) (request : Request) (handle : Nat) (port : ServicePort)
    (template : Template) (coordinates references : List Nat)
    (env : Domain.Environment carriers) (path : List Nat) (origin : Origin)
    (returns : A → B → Prop)
    (live : PIR.Process (Domain.effects carriers) A → Domain.Environment carriers → Prop)
    (left : carriers.Value request.sort × State carriers → PIR.Process (Domain.effects carriers) A)
    (right : Domain.Environment carriers → PIR.Process (Domain.effects carriers) B)
    (unselected : routing.serviceRequest source.frames site request handle = none)
    (route : routing.localRequest source.frames site request handle = some (port, origin))
    (nominal : port.contract = contract)
    (checks : request.valid ∧ (request.operation port.contract).isSome ∧
      Domain.requestOperands env references request)
    (indices : Domain.localCoordinates env coordinates = some path)
    (found : Domain.localOrigin routing.context port request template path = some origin)
    (tail : ∀ value, Simulation returns live (left (value, source))
      (match Domain.Value.encode request.sort value with
       | some encoded => right (env ++ [encoded])
       | none => .halt .refused)) :
    Simulation returns live ((service routing source site contract request handle).bind left)
      ((Domain.localRequest routing.context port request template coordinates references
        [.data request.sort] env).bind right) := by
  rw [service_local_unselected routing source site contract request handle port origin unselected route nominal,
    Domain.localRequest_of_checks routing.context port request template coordinates references env path origin
      checks indices found, PIR.Process.bind_assoc, PIR.Process.bind_assoc]
  apply Simulation.request
  intro value
  cases encoded : Domain.Value.encode request.sort value <;>
    simpa only [encoded, PIR.Process.bind] using tail value

end Original
end Zkc.Construction
