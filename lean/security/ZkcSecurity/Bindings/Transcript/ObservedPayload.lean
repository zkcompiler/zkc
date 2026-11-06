module

public import Zkc.Construction.OriginalEffects
public import ZkcSecurity.ProgramLogic.Transcript.Typed

@[expose] public section

/-! At a field draw following a public message, the ideal transcript key
fixes the received value, including its nominal sort. Resampling the draw at
that key also preserves the replayed validator residual. -/
set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.ObservedPayload
open Zkc.Source Zkc.Source.Structured Zkc.Construction

variable {C : Carriers}

/-- Read the last message immediately preceding the selected draw. Both full
origins are checked, including their application and iteration coordinates. -/
def beforeDraw (message draw : Origin) (ty : Ty) (key : Domain.History C) : Option (C.Value ty) :=
  match key.reverse with
  | .challenge q :: .message m payload :: _ =>
    if q = draw ∧ m = message then payload.value ty else none
  | _ => none

theorem beforeDraw_observed (history : Domain.History C) (message draw : Origin)
    {ty : Ty} {value : C.Value ty} {payload : Domain.Payload C}
    (encoded : Domain.Payload.ofValue ty value = some payload) :
    beforeDraw message draw ty (history ++ [.message message payload] ++ [.challenge draw]) =
      some value := by
  simp [beforeDraw, Domain.Payload.value_ofValue encoded]

/-- The observation and draw belong to the original construction's actual
process. If observation stops, the query continuation is never reached. -/
theorem record_query (state : Original.State C) (message draw : Origin)
    (payload : Domain.Payload C) (field : String) (request : draw.request = some (.draw field)) :
    ((Original.record state message payload).bind fun pair ↦
      Original.queryField pair.2 draw field) =
      .call (.observe (.message message payload)) (fun _ ↦
        .call (.query (state.history ++ [.message message payload]) draw) (fun raw ↦
          .done ((by simpa only [Domain.Raw, request, Request.draw] using raw), {
            state with history := state.history ++ [.message message payload] ++ [.challenge draw] }))) := by
  simp only [Original.record, PIR.Process.bind, Original.queryField, request, ↓reduceDIte]

variable {I : PIR.Signature} {A : Type} [DecidableEq (Domain.Event C)]

/-- Both the payload and the residual reached by the validator are fixed
under resampling the current cell, for every background answer table. -/
theorem replay_at_draw
    (absorb : Typed.Interface I (Domain.Event C) (Domain.Payload C) Domain.Raw)
    (table : (key : Domain.History C) → Typed.ByLast Domain.Raw key)
    (validator : PIR.Process I A) (initial events : Domain.History C)
    (message draw : Origin) {ty : Ty} {value : C.Value ty} {payload : Domain.Payload C}
    (encoded : Domain.Payload.ofValue ty value = some payload)
    (raw : Typed.ByLast Domain.Raw (initial ++ (events ++ [.message message payload]) ++ [.challenge draw])) :
    let observed := events ++ [.message message payload]
    let key := initial ++ observed ++ [.challenge draw]
    (beforeDraw message draw ty key,
      Typed.replay absorb (Typed.readTable (Function.update table key raw)) validator initial observed) =
    (some value, Typed.replay absorb (Typed.readTable table) validator initial observed) := by
  dsimp only
  rw [Typed.replay_update]
  have same := beforeDraw_observed (initial ++ events) message draw encoded
  simpa only [List.append_assoc] using congrArg
    (fun v ↦ (v, Typed.replay absorb (Typed.readTable table) validator initial
      (events ++ [.message message payload]))) same

end ZkcSecurity.FiatShamir.ObservedPayload
