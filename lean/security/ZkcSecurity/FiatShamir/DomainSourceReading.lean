module

public import ZkcSecurity.FiatShamir.SourceReading
public import ZkcSecurity.FiatShamir.NominalDomain
public import Zkc.Construction.OriginalEffects

public section

/-! The nominal Domain adapter for public Fiat-Shamir source operations.
All routing decisions are the existing Original decisions, including refusal.
The adapter supports both folded roles under the endpoint reading. Producer
execution/completeness, plain delivery and private sampling have different
consumers; this module does not identify them with that endpoint projection.
-/
set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.DomainSourceReading
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript
open DomainReduction
variable {carriers : Carriers}

theorem draw_supported {origin : Origin} {field : String}
    (request : origin.request = some (.draw field)) : Domain.drawRequest origin = true := by
  rcases origin with ⟨entry, events, asked⟩
  change asked = some (.draw field) at request
  subst asked
  rfl

@[expose] def record (state : Original.State carriers) (origin : Origin) (payload : Domain.Payload carriers) :
    PIR.Process (NominalDomain.signature carriers) (Unit × Original.State carriers) :=
  .call (.deliver origin payload) fun _ =>
    .done ((), { state with history := state.history ++ [.message origin payload] })

@[expose] def queryField (state : Original.State carriers) (origin : Origin) (field : String) :
    PIR.Process (NominalDomain.signature carriers) (carriers.Field field × Original.State carriers) :=
  if request : origin.request = some (.draw field) then
    .call (.query origin (draw_supported request)) fun raw =>
      .done (Original.fieldReply origin field request raw,
        { state with history := state.history ++ [.challenge origin] })
  else .halt .refused

@[expose] def receive (routing : Original.Routing) (state : Original.State carriers) (ty : Ty)
    (site : String) (sender : Nat) :
    PIR.Process (NominalDomain.signature carriers) (carriers.Value ty × Original.State carriers) :=
  match routing.mode with
  | .producer =>
    match ty with
    | .field field =>
      match routing.delivery state.frames site field sender with
      | none => .halt .refused
      | some (draw, message) =>
        (queryField state draw field).bind fun (value, final) =>
          (record final message (.field field value)).bind fun (_, observed) => .done (value, observed)
    | _ => .halt .refused
  | .validator =>
    match routing.message state.frames site sender routing.context.validator with
    | none => .halt .refused
    | some origin =>
      .call (.receive ty origin) fun value =>
        match Domain.Payload.ofValue ty value with
        | none => .halt .refused
        | some payload =>
          .done (value, { state with history := state.history ++ [.message origin payload] })

@[expose] def send (routing : Original.Routing) (state : Original.State carriers) (ty : Ty)
    (site : String) (receiver : Nat) (value : carriers.Value ty) :
    PIR.Process (NominalDomain.signature carriers) (Unit × Original.State carriers) :=
  let sender := match routing.mode with
    | .producer => routing.context.producer | .validator => routing.context.validator
  match routing.message state.frames site sender receiver, Domain.Payload.ofValue ty value with
  | some origin, some payload => record state origin payload
  | _, _ => .halt .refused

/-- No local-service effect is silently reclassified as a public query. The
public adapter refuses its unsupported branch; the installation below requires
that the actual routing has no local routes. -/
@[expose] def query (routing : Original.Routing) (state : Original.State carriers)
    (site field : String) (handle : Nat) :
    PIR.Process (NominalDomain.signature carriers) (carriers.Field field × Original.State carriers) :=
  match routing.mode, routing.draw state.frames site field handle with
  | .validator, some origin => queryField state origin field
  | _, _ => .halt .refused

@[expose] def operations (routing : Original.Routing) :
    PIR.StateOperationInterpretation (Occurrence.signature carriers)
      (NominalDomain.signature carriers) (Original.State carriers)
  | .enter frame, state => .done ((), { state with frames := state.frames ++ [frame] })
  | .leave frame, state =>
    if state.frames.getLast? = some frame then
      .done ((), { state with frames := state.frames.dropLast })
    else .halt .refused
  | .action (.receive ty site sender), state => receive routing state ty site sender
  | .action (@Participant.Action.send _ _ _ _ ty site receiver value), state =>
      send routing state ty site receiver value
  | .action (.query site field (.cons handle .nil)), state => query routing state site field handle

theorem record_reading (state : Original.State carriers) (origin : Origin)
    (payload : Domain.Payload carriers) :
    Bridge NominalDomain.interface SourceReading.Post state.history
      (Original.record state origin payload) (record state origin payload) := by
  exact ⟨ReadingTo.absorbSend (absorb := NominalDomain.interface (carriers := carriers))
      (.deliver origin payload) _ _ () rfl (.observe _ (.done _ _ rfl)),
    .observe _ (.done _ _ rfl)⟩

theorem queryField_reading (state : Original.State carriers) (origin : Origin) (field : String) :
    Bridge NominalDomain.interface SourceReading.Post state.history
      (Original.queryField state origin field) (queryField state origin field) := by
  unfold Original.queryField queryField
  by_cases request : origin.request = some (.draw field)
  · simp only [request, ↓reduceDIte]
    exact ⟨ReadingTo.query (absorb := NominalDomain.interface (carriers := carriers))
      _ _ _ (.query origin (draw_supported request)) _ id
      (draw_supported request) rfl (fun _ => .done _ _ rfl),
      .query _ _ _ (draw_supported request) (fun _ => .done _ _ rfl)⟩
  · simp only [request, ↓reduceDIte]
    exact .halt _ _

theorem receive_reading (routing : Original.Routing) (state : Original.State carriers)
    (ty : Ty) (site : String) (sender : Nat) :
    Bridge NominalDomain.interface SourceReading.Post state.history
      (Original.receive routing state ty site sender) (receive routing state ty site sender) := by
  unfold Original.receive receive
  cases routing.mode with
  | producer =>
    dsimp only
    cases ty <;> try exact .halt _ _
    rename_i field
    dsimp only
    cases routing.delivery state.frames site field sender with
    | none => exact .halt _ _
    | some origins =>
      rcases origins with ⟨draw, message⟩
      apply (queryField_reading state draw field).bind
      intro reached result agrees
      simp only [SourceReading.Post] at agrees
      subst reached
      apply (record_reading result.2 message (.field field result.1)).bind
      intro reached final agrees
      exact .done _ _ agrees
  | validator =>
    dsimp only
    cases route : routing.message state.frames site sender routing.context.validator with
    | none => exact .halt _ _
    | some origin =>
      constructor
      · refine ReadingTo.receive (absorb := NominalDomain.interface (carriers := carriers))
          ty site site (routing.context.role sender) _ (.receive ty origin) _
          (.message origin) (NominalDomain.received ty origin) id rfl ?_ ?_
        · intro payload
          simpa only [Option.map_id, id_eq] using NominalDomain.received_message ty origin payload
        · intro payload value decoded
          simp only [id_eq, Domain.Payload.ofValue_value decoded]
          exact .observe _ (.done _ _ rfl)
      · refine .receive ty site site (routing.context.role sender) _ ?_
        intro value
        cases Domain.Payload.ofValue ty value with
        | none => exact .halt _ _
        | some payload => exact .observe _ (.done _ _ rfl)

theorem send_reading (routing : Original.Routing) (state : Original.State carriers)
    (ty : Ty) (site : String) (receiver : Nat) (value : carriers.Value ty) :
    Bridge NominalDomain.interface SourceReading.Post state.history
      (Original.send routing state ty site receiver value) (send routing state ty site receiver value) := by
  unfold Original.send send
  cases routing.mode with
  | producer =>
    dsimp only
    cases routing.message state.frames site routing.context.producer receiver <;>
      cases Domain.Payload.ofValue ty value <;> try exact .halt _ _
    exact ⟨.send _ _ _ _ (record_reading state _ _).reading,
      .send _ _ _ _ (record_reading state _ _).coherent⟩
  | validator =>
    dsimp only
    cases routing.message state.frames site routing.context.validator receiver <;>
      cases Domain.Payload.ofValue ty value <;> try exact .halt _ _
    exact record_reading state _ _

theorem local_none (routing : Original.Routing) (noLocal : routing.locals = [])
    (frames : Original.Frames) (site field : String) (handle : Nat) :
    routing.local frames site field handle = none := by
  simp only [Original.Routing.local, noLocal, List.filter_nil]

theorem query_reading (routing : Original.Routing) (noLocal : routing.locals = [])
    (state : Original.State carriers) (site field : String) (handle : Nat) :
    Bridge NominalDomain.interface SourceReading.Post state.history
      (Original.query routing state site field handle) (query routing state site field handle) := by
  unfold Original.query query
  rw [local_none routing noLocal]
  cases routing.mode <;> cases routing.draw state.frames site field handle
  all_goals first | exact .halt _ _ | exact queryField_reading state _ field

/-- This is the only installation premise for the public adapter: an actual
Fiat-Shamir profile with no private service routes. Both folded roles are
covered under readExecution; this is not a producer completeness theorem. -/
@[expose] def interpretation (routing : Original.Routing) (replacement : Replacement)
    (profile : routing.context.profile = .fiatShamir replacement) (noLocal : routing.locals = []) :
    SourceReading.Interpretation routing (NominalDomain.interface (carriers := carriers)) where
  operations := operations routing
  law := by
    intro operation state
    cases operation with
    | enter frame => exact .done _ _ rfl
    | leave frame =>
      simp only [Original.operations, operations]
      split
      · exact .done _ _ rfl
      · exact .halt _ _
    | action action =>
      cases action with
      | receive ty site sender =>
        simpa only [Original.operations, operations, profile] using
          receive_reading routing state ty site sender
      | send site receiver value =>
        simpa only [Original.operations, operations, profile] using
          send_reading routing state _ site receiver value
      | query site field arguments =>
        cases arguments with
        | cons handle tail =>
          cases tail
          exact query_reading routing noLocal state site field handle

@[expose] def presentation {A : Type} (routing : Original.Routing)
    (source : PIR.Process (Occurrence.signature carriers) A) (state : Original.State carriers) :
    PIR.Process (NominalDomain.signature carriers) (A × Original.State carriers) :=
  source.interpretState (operations routing) state

/-- Automatic source reading and coherence from the installed primitive laws.
There is no per-source Routed witness, whole-source equality, or restriction on
oracle replies. Routing coverage and artifact correspondence remain separate
admission obligations; this theorem also faithfully reads refused routes. -/
theorem reading {A : Type} (routing : Original.Routing) (replacement : Replacement)
    (profile : routing.context.profile = .fiatShamir replacement) (noLocal : routing.locals = [])
    (source : PIR.Process (Occurrence.signature carriers) A) (state : Original.State carriers) :
    Bridge NominalDomain.interface SourceReading.Post state.history
      (Original.fold routing source state) (presentation routing source state) :=
  (interpretation routing replacement profile noLocal).reading source state

end ZkcSecurity.FiatShamir.DomainSourceReading
