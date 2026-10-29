module

public import Zkc.Construction.OriginalRouting
public import Zkc.Semantics.StateInterpretation

@[expose] public section

/-! Construct the actual occurrence-aware original process by effect folding.
There is no source AST evaluator and no artifact readback here. The target
signature and runtime handler are the existing nominal constructed ones.
-/
set_option autoImplicit false
namespace Zkc.Construction.Original
open Zkc.Source
open Domain (effects Raw)

structure State (carriers : Structured.Carriers) where
  frames : Frames := []
  history : Domain.History carriers := []

variable {carriers : Structured.Carriers}

/-- Typed replies are decoded at the recorded nominal request, never by host
carrier equality. A failed query keeps the runtime handler's attempted event
and oracle post-state; this continuation runs only after an actual reply. -/
def queryField (state : State carriers) (origin : Origin) (field : String) :
    PIR.Process (effects carriers) (carriers.Field field × State carriers) :=
  if request : origin.request = some (.draw field) then
    .call (.query state.history origin) fun reply =>
      .done ((by simpa only [Raw, request, Request.draw] using reply),
        { state with history := state.history ++ [.challenge origin] })
  else .halt .refused

/-- Public observation appends the exact event after, and only after, its
payload is available. No receive failure invents an absorbed message. -/
def record (state : State carriers) (origin : Origin) (payload : Domain.Payload carriers) :
    PIR.Process (effects carriers) (Unit × State carriers) :=
  .call (.observe (.message origin payload)) fun _ =>
    .done ((), { state with history := state.history ++ [.message origin payload] })

def receive (routing : Routing) (state : State carriers) (ty : Structured.Ty)
    (site : String) (sender : Nat) :
    PIR.Process (effects carriers) (carriers.Value ty × State carriers) :=
  match routing.mode with
  | .producer =>
    match ty with
    | .field field =>
      match routing.delivery state.frames site field sender with
      | none => .halt .refused
      | some (draw, message) =>
        (queryField state draw field).bind fun (value, final) =>
          (record final message (.field field value)).bind fun (_, observed) =>
            .done (value, observed)
    | _ => .halt .refused
  | .validator =>
    match routing.message state.frames site sender routing.context.validator with
    | none => .halt .refused
    | some origin =>
      .call (.receive ty site site (routing.context.role sender)) fun value =>
        match Domain.Payload.ofValue ty value with
        | none => .halt .refused
        | some payload => (record state origin payload).bind fun (_, final) => .done (value, final)

-- Keep one stored provider for the receive equations used by both roles.
-- This materializes their proofs without adding global simplifier rules.
section
attribute [local simp] receive
end

def send (routing : Routing) (state : State carriers) (ty : Structured.Ty)
    (site : String) (receiver : Nat) (value : carriers.Value ty) :
    PIR.Process (effects carriers) (Unit × State carriers) :=
  let sender := match routing.mode with
    | .producer => routing.context.producer
    | .validator => routing.context.validator
  match routing.message state.frames site sender receiver, Domain.Payload.ofValue ty value with
  | some origin, some payload =>
    match routing.mode with
    | .producer =>
      .call (.send site site (routing.context.role receiver) payload) fun _ => record state origin payload
    | .validator => record state origin payload
  | _, _ => .halt .refused

def query (routing : Routing) (state : State carriers) (site field : String) (handle : Nat) :
    PIR.Process (effects carriers) (carriers.Field field × State carriers) :=
  match routing.mode, routing.draw state.frames site field handle with
  | .validator, some origin => queryField state origin field
  | _, _ =>
    match routing.local state.frames site field handle with
    | some (port, origin) =>
      if request : origin.request = some (.draw field) then
        .call (.localService port origin) fun reply =>
          .done ((by simpa only [Raw, request, Request.draw] using reply), state)
      else .halt .refused
    | none => .halt .refused

/-- Plain receives preserve construction state and perform only the real
message action. Source occurrence resolution still authenticates the site. -/
def receivePlain (routing : Routing) (state : State carriers) (ty : Structured.Ty)
    (site : String) (sender : Nat) :
    PIR.Process (effects carriers) (carriers.Value ty × State carriers) :=
  let receiver := match routing.mode with
    | .producer => routing.context.producer | .validator => routing.context.validator
  match routing.message state.frames site sender receiver with
  | none => .halt .refused
  | some _ =>
      if ty.isService then .halt .refused
      else .call (.receive ty site site (routing.context.role sender)) fun value => .done (value, state)

/-- Plain sends output the real payload. They never turn it into a transcript
observation, including sends by the validator. -/
def sendPlain (routing : Routing) (state : State carriers) (ty : Structured.Ty)
    (site : String) (receiver : Nat) (value : carriers.Value ty) :
    PIR.Process (effects carriers) (Unit × State carriers) :=
  let sender := match routing.mode with
    | .producer => routing.context.producer | .validator => routing.context.validator
  match routing.message state.frames site sender receiver, Domain.Payload.ofValue ty value with
  | some _, some payload =>
      .call (.send site site (routing.context.role receiver) payload) fun _ => .done ((), state)
  | _, _ => .halt .refused

/-- Frames are outermost first. Leaving checks the exact last frame. A stopped
body never reaches this operation; it cannot pop a frame or execute a suffix. -/
def operations (routing : Routing) :
    PIR.StateOperationInterpretation (Structured.Occurrence.signature carriers) (effects carriers)
      (State carriers)
  | .enter frame, state => .done ((), { state with frames := state.frames ++ [frame] })
  | .leave frame, state =>
    if state.frames.getLast? = some frame then
      .done ((), { state with frames := state.frames.dropLast })
    else .halt .refused
  | .action (.receive ty site sender), state =>
      match routing.context.profile with
      | .plain => receivePlain routing state ty site sender
      | .fiatShamir _ => receive routing state ty site sender
  | .action (@Participant.Action.send _ _ _ _ ty site receiver value), state =>
      match routing.context.profile with
      | .plain => sendPlain routing state ty site receiver value
      | .fiatShamir _ => send routing state ty site receiver value
  | .action (.query site field (.cons handle .nil)), state => query routing state site field handle

/-- The fold is generic in all typed replies, inputs, and reached stop reasons. -/
def fold {A : Type} (routing : Routing)
    (source : PIR.Process (Structured.Occurrence.signature carriers) A) (state : State carriers) :
    PIR.Process (effects carriers) (A × State carriers) :=
  source.interpretState (operations routing) state

/-- The only root source of the construction is the admitted original. -/
def participant (model : Structured.DomainModel) (program : Structured.Program)
    (routing : Routing) (self : Nat)
    (inputs : Values (Component model.Value) program.payload.entry.inputs)
    (state : State model.toCarriers := {}) :=
  fold { routing with snapshot := program.snapshot }
    (Structured.Occurrence.participant model program self inputs) state

/-- Exact sequence law: the suffix sees the reached history and frames. -/
theorem fold_bind {A B : Type} (routing : Routing)
    (source : PIR.Process (Structured.Occurrence.signature carriers) A)
    (next : A → PIR.Process (Structured.Occurrence.signature carriers) B) (state : State carriers) :
    fold routing (source.bind next) state =
      (fold routing source state).bind fun (value, final) => fold routing (next value) final :=
  PIR.Process.interpretState_bind _ _ _ _

/-- All stopped prefixes remain stopped, including inside a loop or call. -/
theorem fold_halt {A : Type} (routing : Routing) (reason : PIR.Stop) (state : State carriers) :
    fold routing (.halt reason : PIR.Process _ A) state = .halt reason := rfl

end Zkc.Construction.Original
