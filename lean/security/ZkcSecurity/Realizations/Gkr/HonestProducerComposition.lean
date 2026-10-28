module

public import ZkcSecurity.FiatShamir.HonestReadback
public import Zkc.Construction.OriginalEffects
public import Zkc.Construction.OriginalLaws
public import ZkcSecurity.Obligations.HonestComposition

@[expose] public section

/-! Honest synchronization of actual source actions through the existing
Original.fold. These are routing laws, independent of protocol mathematics.
All histories, occurrence stacks, typed replies and full returns are retained. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace ZkcSecurity.Realizations.Gkr.HonestProducerComposition
open Zkc Source Structured Construction
open ZkcSecurity.FiatShamir

variable {F G A : Type}

abbrev State := Original.State (uniformCarriers F G)

/-- Closing the actual source iteration restores its caller's stack and keeps
the complete history produced by the child. A refused close has no proof. -/
theorem within {B : Type} (routing : Original.Routing) (site : String) (index : Nat)
    (state : State (F := F) (G := G))
    (left : PIR.Process (Occurrence.signature (uniformCarriers F G)) A)
    (right : PIR.Process (Occurrence.signature (uniformCarriers F G)) B)
    (post : (A × State (F := F) (G := G)) → (B × State (F := F) (G := G)) → Prop)
    (body : Readback (fun l r =>
      l.2.frames = state.frames ++ [⟨site, index⟩] ∧
      r.2.frames = state.frames ++ [⟨site, index⟩] ∧
      post (l.1, { l.2 with frames := state.frames })
        (r.1, { r.2 with frames := state.frames }))
      (Original.fold { routing with mode := .producer } left
        { state with frames := state.frames ++ [⟨site, index⟩] })
      (Original.fold { routing with mode := .validator } right
        { state with frames := state.frames ++ [⟨site, index⟩] })) :
    Readback post
      (Original.fold { routing with mode := .producer } (Occurrence.iterations.within site index left) state)
      (Original.fold { routing with mode := .validator } (Occurrence.iterations.within site index right) state) := by
  rw [Original.fold_within, Original.fold_within]
  apply body.bind
  rintro ⟨l, ls⟩ ⟨r, rs⟩ ⟨lf, rf, holds⟩
  simp only at lf rf holds ⊢
  simp only [lf, rf, List.getLast?_concat, List.dropLast_concat, ite_true]
  exact .done holds

/-- The standard source construction applied to an action-only body view.
The caller must associate that view with the admitted occurrence-aware body. -/
def constructed (routing : Original.Routing)
    (source : PIR.Process (participantInterface F G) A) (state : State (F := F) (G := G)) :=
  Original.fold routing (source.interpret Occurrence.actions) state

private theorem yields_true {I : PIR.Signature} {B : Type} (process : PIR.Process I B) :
    PIR.Yields (fun _ => True) process := by
  induction process with
  | done => trivial
  | halt => trivial
  | call _ _ ih => exact ih

/-- Pure return facts survive the actual construction; stops cannot supply a
return and no condition is placed on any provider's typed replies. -/
theorem constructed_yields (routing : Original.Routing)
    (source : PIR.Process (participantInterface F G) A) (property : A → Prop)
    (holds : PIR.Yields property source) (state : State (F := F) (G := G)) :
    PIR.Yields (fun result => property result.1) (constructed routing source state) := by
  rw [constructed, Original.fold_actions]
  induction source generalizing state with
  | done => exact holds
  | halt => trivial
  | call operation next ih =>
    simp only [PIR.Process.interpretState]
    apply (yields_true (Original.operations routing (.action operation) state)).bind
    rintro ⟨reply, reached⟩ _
    exact ih reply (holds reply) reached

/-- Attach a proved all-return invariant to a synchronization derivation. -/
theorem frame_left {B : Type} {post : A → B → Prop} {property : A → Prop}
    {left : PIR.Process (Domain.effects (uniformCarriers F G)) A}
    {right : PIR.Process (Domain.effects (uniformCarriers F G)) B}
    (aligned : Readback post left right) (holds : PIR.Yields property left) :
    Readback (fun a b => post a b ∧ property a) left right := by
  induction aligned with
  | done h => exact .done ⟨h, holds⟩
  | checkpointLeft env _ ih => exact .checkpointLeft env (ih (holds ()))
  | checkpointRight env _ ih => exact .checkpointRight env (ih holds)
  | observeLeft event _ ih => exact .observeLeft event (ih (holds ()))
  | observeRight event _ ih => exact .observeRight event (ih holds)
  | sendReceive site schema peer rsite rschema rpeer payload value decoded _ ih =>
    exact .sendReceive site schema peer rsite rschema rpeer payload value decoded (ih (holds ()))
  | sendRight site schema peer payload _ ih => exact .sendRight site schema peer payload (ih holds)
  | query history origin supported _ ih => exact .query history origin supported (fun reply => ih reply (holds reply))

theorem constructed_bind {B : Type} (routing : Original.Routing)
    (source : PIR.Process (participantInterface F G) A)
    (next : A → PIR.Process (participantInterface F G) B) (state : State (F := F) (G := G)) :
    constructed routing (source.bind next) state =
      (constructed routing source state).bind fun result => constructed routing (next result.1) result.2 := by
  simp only [constructed, PIR.Process.interpret_bind, Original.fold_bind]

theorem constructed_call (routing : Original.Routing)
    (operation : (participantInterface F G).Op)
    (next : (participantInterface F G).Reply operation → PIR.Process (participantInterface F G) A)
    (state : State (F := F) (G := G)) :
    constructed routing (.call operation next) state =
      (Original.operations routing (.action operation) state).bind fun result =>
        constructed routing (next result.1) result.2 := by
  simp only [constructed, PIR.Process.interpret, Occurrence.actions, PIR.Process.bind,
    Original.fold, PIR.Process.interpretState]

/-- Both returned histories include exactly the same actual typed payload. -/
theorem message (routing : Original.Routing) (replacement : Replacement)
    (profile : routing.context.profile = .fiatShamir replacement)
    (state : State (F := F) (G := G)) (site field : String) (value : F) (origin : Origin)
    (route : routing.message state.frames site routing.context.producer routing.context.validator = some origin) :
    Readback (fun left right =>
      left = ((), { state with history := state.history ++ [.message origin (.field field value)] }) ∧
      right = (value, { state with history := state.history ++ [.message origin (.field field value)] }))
      (constructed { routing with mode := .producer }
        (.call (.send (ty := .field field) site routing.context.validator value) .done) state)
      (constructed { routing with mode := .validator }
        (.call (.receive (.field field) site routing.context.producer) .done) state) := by
  have producerRoute : ({ routing with mode := .producer } : Original.Routing).message
      state.frames site routing.context.producer routing.context.validator = some origin := route
  have validatorRoute : ({ routing with mode := .validator } : Original.Routing).message
      state.frames site routing.context.producer routing.context.validator = some origin := route
  simp only [constructed, PIR.Process.interpret, Occurrence.actions, PIR.Process.bind]
  rw [Original.fold_action, Original.fold_action]
  simp only [Original.operations, profile, Original.send, Original.receive,
    producerRoute, validatorRoute, Domain.Payload.ofValue, Ty.isHandle,
    dite_true, Original.record, PIR.Process.bind]
  apply Readback.sendReceive (carriers := uniformCarriers F G) (ty := .field field)
    _ _ _ _ _ _ (.field field value) value (by simp [Domain.Payload.value])
  apply Readback.observeLeft
  apply Readback.observeRight
  exact .done ⟨rfl, rfl⟩

/-- The actual public query and its checked def-use delivery synchronize on
one nominal request and the entire reached history, for every typed reply. -/
theorem challenge (routing : Original.Routing) (replacement : Replacement)
    (profile : routing.context.profile = .fiatShamir replacement)
    (state : State (F := F) (G := G)) (querySite deliverySite field : String) (handle : Nat)
    (draw delivery : Origin)
    (producerRoute : routing.delivery state.frames deliverySite field routing.context.validator =
      some (draw, delivery))
    (queryRoute : routing.draw state.frames querySite field handle = some draw)
    (deliveryRoute : routing.message state.frames deliverySite routing.context.validator
      routing.context.producer = some delivery)
    (request : draw.request = some (.draw field)) :
    Readback (fun left right => ∃ value : F,
      left = (value, { state with history := state.history ++
        [.challenge draw, .message delivery (.field field value)] }) ∧
      right = (value, { state with history := state.history ++
        [.challenge draw, .message delivery (.field field value)] }))
      (constructed { routing with mode := .producer }
        (.call (.receive (.field field) deliverySite routing.context.validator) .done) state)
      (constructed { routing with mode := .validator }
        (.call (.query querySite field (.cons handle .nil)) fun value =>
          .call (.send (ty := .field field) deliverySite routing.context.producer value)
            fun _ => .done value) state) := by
  rw [constructed_call, constructed_call]
  simp only [Original.operations, profile]
  rw [Original.producer_delivery (carriers := uniformCarriers F G)
    { routing with mode := .producer } state deliverySite field routing.context.validator
    draw delivery rfl producerRoute request,
    Original.public_query (carriers := uniformCarriers F G)
      { routing with mode := .validator } state querySite field handle draw rfl queryRoute]
  simp only [PIR.Process.bind, constructed]
  apply Readback.query _ _ (by rcases draw with ⟨entry, event, actual⟩; dsimp only at request; subst actual; rfl)
  intro reply
  have sent : ({ routing with mode := .validator } : Original.Routing).message
      state.frames deliverySite routing.context.validator routing.context.producer = some delivery := deliveryRoute
  simp only [PIR.Process.interpret, Occurrence.actions, PIR.Process.bind,
    Original.fold, PIR.Process.interpretState, Original.operations, profile,
    Original.send, sent, Domain.Payload.ofValue, Ty.isHandle, dite_true,
    Original.record, PIR.Process.bind, Original.fieldReply]
  apply Readback.observeLeft
  apply Readback.observeRight
  exact .done ⟨Original.fieldReply draw field request reply, rfl, by
    simp only [List.append_assoc, List.singleton_append]; rfl⟩

/-- Continue a proof message from precisely its actual reached state. -/
theorem message_step {B : Type} (routing : Original.Routing) (replacement : Replacement)
    (profile : routing.context.profile = .fiatShamir replacement)
    (state : State (F := F) (G := G)) (site field : String) (value : F) (origin : Origin)
    (route : routing.message state.frames site routing.context.producer routing.context.validator = some origin)
    (nextLeft : PIR.Process (participantInterface F G) A)
    (nextRight : F → PIR.Process (participantInterface F G) B)
    (post : (A × State (F := F) (G := G)) → (B × State (F := F) (G := G)) → Prop)
    (suffix : Readback post
      (constructed { routing with mode := .producer } nextLeft
        { state with history := state.history ++ [.message origin (.field field value)] })
      (constructed { routing with mode := .validator } (nextRight value)
        { state with history := state.history ++ [.message origin (.field field value)] })) :
    Readback post
      (constructed { routing with mode := .producer }
        (.call (.send (ty := .field field) site routing.context.validator value) fun _ => nextLeft) state)
      (constructed { routing with mode := .validator }
        (.call (.receive (.field field) site routing.context.producer) nextRight) state) := by
  change Readback post
    (constructed _ ((PIR.Process.call (I := participantInterface F G) (.send (ty := .field field) site routing.context.validator value) .done).bind
      (fun _ => nextLeft)) state)
    (constructed _ ((PIR.Process.call (I := participantInterface F G) (.receive (.field field) site routing.context.producer) .done).bind nextRight) state)
  rw [constructed_bind, constructed_bind]
  apply (message routing replacement profile state site field value origin route).bind
  rintro left right ⟨rfl, rfl⟩
  exact suffix

/-- Continue both sides after the same actual challenge and delivery. -/
theorem challenge_step {B : Type} (routing : Original.Routing) (replacement : Replacement)
    (profile : routing.context.profile = .fiatShamir replacement)
    (state : State (F := F) (G := G)) (querySite deliverySite field : String) (handle : Nat)
    (draw delivery : Origin)
    (producerRoute : routing.delivery state.frames deliverySite field routing.context.validator =
      some (draw, delivery))
    (queryRoute : routing.draw state.frames querySite field handle = some draw)
    (deliveryRoute : routing.message state.frames deliverySite routing.context.validator
      routing.context.producer = some delivery)
    (request : draw.request = some (.draw field))
    (nextLeft : F → PIR.Process (participantInterface F G) A)
    (nextRight : F → PIR.Process (participantInterface F G) B)
    (post : (A × State (F := F) (G := G)) → (B × State (F := F) (G := G)) → Prop)
    (suffix : ∀ value, Readback post
      (constructed { routing with mode := .producer } (nextLeft value)
        { state with history := state.history ++ [.challenge draw, .message delivery (.field field value)] })
      (constructed { routing with mode := .validator } (nextRight value)
        { state with history := state.history ++ [.challenge draw, .message delivery (.field field value)] })) :
    Readback post
      (constructed { routing with mode := .producer }
        (.call (.receive (.field field) deliverySite routing.context.validator) nextLeft) state)
      (constructed { routing with mode := .validator }
        (.call (.query querySite field (.cons handle .nil)) fun value =>
          .call (.send (ty := .field field) deliverySite routing.context.producer value)
            fun _ => nextRight value) state) := by
  change Readback post
    (constructed _ ((PIR.Process.call (I := participantInterface F G) (.receive (.field field) deliverySite routing.context.validator) .done).bind nextLeft) state)
    (constructed _ ((PIR.Process.call (I := participantInterface F G) (.query querySite field (.cons handle .nil)) fun value =>
      .call (.send (ty := .field field) deliverySite routing.context.producer value)
        fun _ => .done value).bind nextRight) state)
  rw [constructed_bind, constructed_bind]
  apply (challenge routing replacement profile state querySite deliverySite field handle
    draw delivery producerRoute queryRoute deliveryRoute request).bind
  rintro left right ⟨value, rfl, rfl⟩
  exact suffix value

end ZkcSecurity.Realizations.Gkr.HonestProducerComposition
