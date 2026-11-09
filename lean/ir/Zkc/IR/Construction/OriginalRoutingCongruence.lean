module

public import Zkc.IR.Construction.OriginalLaws
public import Zkc.IR.Source.Structured.DomainProtocolLinking

@[expose] public section

/-! Discarding templates of the other action kind preserves resolution.
This law concerns source routes only; it assumes no participant simulation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace Zkc.Construction.Original
open Zkc.Source

private theorem message_keep (context : Context) (template : Template) (site : String)
    (sender receiver : Nat)
    (same : template.origin context = some (context.message site sender receiver)) :
    template.messageSite?.isSome = true := by
  unfold Template.origin at same
  split at same
  · simp_all [Template.messageSite?]
  · rename_i protocol ownSite input contract role shape
    cases request : context.request with
    | none => simp [request] at same
    | some request =>
      simp only [request, Option.bind_eq_bind, Option.bind_some] at same
      split at same
      · simp only [Option.some.injEq] at same
        have tag := congrArg (fun origin : Origin => origin.event.head?) same
        simp [Context.query, Context.message, Origin.query, Origin.message] at tag
      · cases same
  · cases same

private theorem query_keep (context : Context) (template : Template) (site : String)
    (request : Request)
    (same : template.origin context = some (context.query site request)) :
    template.querySite?.isSome = true := by
  unfold Template.origin at same
  split at same
  · split at same
    · have tag := congrArg (fun origin : Option Origin => origin.map (fun value => value.event.head?)) same
      simp [Context.query, Origin.query, Origin.message] at tag
    · cases same
  · simp_all [Template.querySite?]
  · cases same

private theorem resolve_filter (snapshot : Structured.Snapshot) (context : Context)
    (expected : Origin) (frames : Frames) (templates : List Template) (keep : Template → Bool)
    (law : ∀ template, template.origin context = some expected → keep template = true) :
    OccurrenceResolution.resolve snapshot context expected frames (templates.filter keep) =
      OccurrenceResolution.resolve snapshot context expected frames templates := by
  unfold OccurrenceResolution.resolve
  congr 1
  rw [List.filter_filter]
  apply List.filter_congr
  intro template _
  by_cases matched : OccurrenceResolution.matchesOccurrence snapshot context expected frames template = true
  · have origin : template.origin context = some expected := by
      simp only [OccurrenceResolution.matchesOccurrence, Bool.and_eq_true, beq_iff_eq] at matched
      exact matched.1.2
    simp [matched, law template origin]
  · simp [Bool.eq_false_iff.mpr matched]

theorem message_filter (routing : Routing) (frames : Frames) (site : String) (sender receiver : Nat) :
    { routing with messages := routing.messages.filter (·.messageSite?.isSome) }.message frames site sender receiver =
      routing.message frames site sender receiver :=
  resolve_filter _ _ _ _ _ _ (fun template => message_keep _ template site sender receiver)

theorem draw_filter (routing : Routing) (frames : Frames) (site field : String) (handle : Nat) :
    { routing with draws := routing.draws.filter (·.querySite?.isSome) }.draw frames site field handle =
      routing.draw frames site field handle := by
  unfold Routing.draw
  split
  · exact resolve_filter _ _ _ _ _ _ (fun template => query_keep _ template site (.draw field))
  · rfl

/-- Filtering by action kind preserves resolution at every nominal request,
including index and block services and all missing or ambiguous routes. -/
theorem serviceRequest_filter (routing : Routing) (frames : Frames) (site : String)
    (request : Request) (handle : Nat) :
    { routing with draws := routing.draws.filter (·.querySite?.isSome) }.serviceRequest
        frames site request handle = routing.serviceRequest frames site request handle := by
  unfold Routing.serviceRequest
  split
  · have reorder : (routing.draws.filter (·.querySite?.isSome)).filter
          (fun template => SourceOccurrences.requestAt routing.snapshot routing.context template ==
            some request) =
        (routing.draws.filter (fun template =>
          SourceOccurrences.requestAt routing.snapshot routing.context template ==
            some request)).filter
            (·.querySite?.isSome) := by
      simp only [List.filter_filter, Bool.and_comm]
    rw [reorder]
    exact resolve_filter _ _ _ _ _ _ (fun template => query_keep _ template site request)
  · rfl

/-- Equality of every route queried by original execution. Candidate tables
need not be equal; generic request routes retain their nominal request, sort,
capability, dynamic frames and refusal behavior. -/
structure RouteEquivalence (first second : Routing) : Prop where
  context : first.context = second.context
  mode : first.mode = second.mode
  messages : ∀ frames site sender receiver,
    first.message frames site sender receiver = second.message frames site sender receiver
  draws : first.mode = .validator → ∀ frames site field handle,
    first.draw frames site field handle = second.draw frames site field handle
  deliveries : ∀ frames site field sender,
    first.delivery frames site field sender = second.delivery frames site field sender
  locals : ∀ frames site field handle,
    first.local frames site field handle = second.local frames site field handle
  serviceRequests : first.mode = .validator → ∀ frames site request handle,
    first.serviceRequest frames site request handle =
      second.serviceRequest frames site request handle
  localRequests : ∀ frames site request handle,
    first.localRequest frames site request handle = second.localRequest frames site request handle
  typedDeliveries : ∀ frames site ty sender,
    first.typedDelivery frames site ty sender = second.typedDelivery frames site ty sender

/-- Equal primitive routes imply equality of the full original fold, including
all source outputs, occurrence stacks, observations, typed replies and stops. -/
theorem fold_congr {carriers : Structured.Carriers} {A : Type} (first second : Routing)
    (same : RouteEquivalence first second)
    (source : PIR.Process (Structured.Occurrence.signature carriers) A) (state : State carriers) :
    fold first source state = fold second source state := by
  have services : ∀ state site contract request handle,
      @service carriers first state site contract request handle =
        service second state site contract request handle := by
    intro state site contract request handle
    cases selected : first.mode with
    | producer => simp only [service, selected, ← same.mode, same.localRequests]
    | validator =>
      simp only [service, selected, ← same.mode, same.context,
        same.serviceRequests selected, same.localRequests]
  have operations : @operations carriers first = operations second := by
    funext operation state
    cases operation with
    | enter => rfl
    | leave => rfl
    | action action =>
      cases action with
      | receive ty site sender =>
        simp only [Original.operations, same.context]
        cases second.context.profile
        · simp only [receivePlain, same.mode, same.context, same.messages, Context.role]
          rw [same.context]
        · simp only [receive, receiveRequest, same.mode, same.context, same.messages,
            same.deliveries, same.typedDeliveries, Context.role]
          rw [same.context]
      | @send ty site receiver value =>
        simp only [Original.operations, same.context]
        cases second.context.profile
        · simp only [sendPlain, same.mode, same.context, same.messages, Context.role]
          rw [same.context]
        · simp only [send, same.mode, same.context, same.messages, Context.role]
          rw [same.context]
      | query site operation args =>
        cases operation with
        | draw field =>
          rcases args with _ | ⟨handle, _ | _⟩
          change query first state site field handle = query second state site field handle
          cases selected : first.mode with
          | producer => simp only [query, selected, ← same.mode, same.locals]
          | validator => simp only [query, selected, ← same.mode, same.draws selected, same.locals]
        | sampleIndex contract =>
          rcases args with _ | ⟨handle, _ | ⟨bound, _ | _⟩⟩
          exact services state site contract (.sampleIndex bound) handle
        | sampleIndices contract =>
          rcases args with _ | ⟨handle, _ | ⟨bound, _ | ⟨count, _ | _⟩⟩⟩
          exact services state site contract (.sampleIndices bound count) handle
  simp only [fold, operations]

/-- Message and draw tables may share a source template list: removing entries
of the other event kind preserves every fold, including refusal branches. -/
theorem fold_filter {carriers : Structured.Carriers} {A : Type} (routing : Routing)
    (source : PIR.Process (Structured.Occurrence.signature carriers) A) (state : State carriers) :
    fold { routing with
      messages := routing.messages.filter (fun template => template.messageSite?.isSome)
      draws := routing.draws.filter (fun template => template.querySite?.isSome) } source state =
      fold routing source state := by
  apply fold_congr
  exact {
    context := rfl
    mode := rfl
    messages := message_filter routing
    draws := fun _ => draw_filter routing
    deliveries := by intros; rfl
    locals := by intros; rfl
    serviceRequests := fun _ => serviceRequest_filter routing
    localRequests := by intros; rfl
    typedDeliveries := by intros; rfl }

end Zkc.Construction.Original

namespace Zkc.Source.Structured.Occurrence
/-- Root role masking fixes the source input semantics independently of ABI
encoding. Hidden values can be discarded before any source operation runs. -/
theorem participant_mask_congr (model : DomainModel) (program : Program) (role : Nat)
    (first second : Values (Component model.Value) program.payload.entry.inputs)
    (same : maskValues role program.payload.entry.inputScopes first =
      maskValues role program.payload.entry.inputScopes second) :
    participant model program role first = participant model program role second := by
  unfold participant
  simp only [invoke_body model program.payload _ program.payload.entry_mem]
  simp only [CheckedProtocol.denoteWithOn, ProtocolContext.mapScopes_root, same]
end Zkc.Source.Structured.Occurrence
