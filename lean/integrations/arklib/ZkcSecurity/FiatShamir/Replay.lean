module

public import Zkc.Construction.FiatShamir

@[expose] public section

/-! Replaying a validator along a typed transcript history.

`replay` walks a validator process along a list of absorbed transcript events,
reading each event exactly as `Zkc.Construction.transform` would have absorbed
it: a receive consumes a message event at its occurrence and decodes its
payload, a query consumes its challenge occurrence and is answered by the
challenge table at the history ending with that occurrence, and a send consumes
the message event carrying its value. The result is the residual process after
the last event, or `none` when the events are not a history the transform could
absorb from this process.

Two facts make replay the key of the Fiat–Shamir security argument. It is a
function of the events, so every history determines at most one residual
process. And it reads the challenge table only at histories no longer than the
replayed one (`replay_congr`), so resampling the table at a longer history
leaves the residual unchanged.
-/

set_option autoImplicit false

namespace ZkcSecurity.FiatShamir
open Zkc.Source Zkc.Construction Zkc.Source.Common.Native

variable {F G A : Type} [DecidableEq F] [DecidableEq G]

/-- Walk `process` along `events`, starting after `history`. -/
def replay (context : Context) (table : History F G → F) :
    PIR.Proc (Actions F G) A → History F G → History F G → Option (PIR.Proc (Actions F G) A)
  | process, _, [] => some process
  | .done _, _, _ :: _ => none
  | .halt _, _, _ :: _ => none
  | .call (.receive ty site sender) next, history, event :: rest =>
      match event with
      | .message origin payload =>
          if origin = context.message site sender context.validator then
            match payload.value ty with
            | some value =>
                replay context table (next value) (history ++ [.message origin payload]) rest
            | none => none
          else none
      | _ => none
  | .call (.query site _ _) next, history, event :: rest =>
      if event = .challenge (context.query site) then
        replay context table (next (table (history ++ [event]))) (history ++ [event]) rest
      else none
  | .call (.send (ty := ty) site receiver sent) next, history, event :: rest =>
      match Payload.ofValue ty sent with
      | some payload =>
          if event = .message (context.message site context.validator receiver) payload then
            replay context table (next ()) (history ++ [event]) rest
          else none
      | none => none

variable (context : Context) (table : History F G → F)

@[simp] theorem replay_nil (process : PIR.Proc (Actions F G) A) (history : History F G) :
    replay context table process history [] = some process := by
  cases process <;> rfl

/-- One received message, absorbed at its occurrence. -/
theorem replay_receive (ty : Ty) (site : String) (sender : Nat)
    (next : ScalarValue F G ty → PIR.Proc (Actions F G) A) (history : History F G)
    (payload : Payload F G) (value : ScalarValue F G ty) (decoded : payload.value ty = some value) :
    replay context table (.call (.receive ty site sender) next) history
        [.message (context.message site sender context.validator) payload] =
      some (next value) := by
  simp [replay, decoded]

/-- One challenge occurrence, answered by the table at the history ending with it. -/
theorem replay_query (site : String) (op : services.Op)
    (arguments : Values (ScalarValue F G) (services.arguments op))
    (next : F → PIR.Proc (Actions F G) A) (history : History F G) :
    replay context table (.call (.query site op arguments) next) history
        [.challenge (context.query site)] =
      some (next (table (history ++ [.challenge (context.query site)]))) := by
  simp [replay]

/-- One sent message, absorbed with its value. -/
theorem replay_send {ty : Ty} (site : String) (receiver : Nat) (sent : ScalarValue F G ty)
    (next : Unit → PIR.Proc (Actions F G) A) (history : History F G) (payload : Payload F G)
    (encoded : Payload.ofValue ty sent = some payload) :
    replay context table (.call (.send site receiver sent) next) history
        [.message (context.message site context.validator receiver) payload] =
      some (next ()) := by
  simp [replay, encoded]

/-- Replaying a concatenation replays the first part, then the second from the
residual and the extended history. -/
theorem replay_append (first second : History F G) :
    ∀ (process : PIR.Proc (Actions F G) A) (history : History F G),
      replay context table process history (first ++ second) =
        (replay context table process history first).bind fun residual =>
          replay context table residual (history ++ first) second := by
  induction first with
  | nil => intro process history; simp
  | cons event rest ih =>
      intro process history
      cases process with
      | done value => rfl
      | halt stop => rfl
      | call operation next =>
          cases operation with
          | receive ty site sender =>
              cases event with
              | message origin payload =>
                  simp only [List.cons_append, replay]
                  split
                  · split
                    · rename_i value _
                      rw [ih]
                      simp
                    · rfl
                  · rfl
              | binding _ _ => rfl
              | challenge _ => rfl
          | query site op arguments =>
              simp only [List.cons_append, replay]
              split
              · rw [ih]
                simp
              · rfl
          | send site receiver sent =>
              simp only [List.cons_append, replay]
              split
              · split
                · rw [ih]
                  simp
                · rfl
              · rfl

/-- Replay reads the challenge table only at histories no longer than the
replayed one. -/
theorem replay_congr {other : History F G → F} (events : History F G) :
    ∀ (process : PIR.Proc (Actions F G) A) (history : History F G),
      (∀ key : History F G, key.length ≤ history.length + events.length → table key = other key) →
      replay context table process history events =
        replay context other process history events := by
  induction events with
  | nil => intro process history _; simp
  | cons event rest ih =>
      intro process history agree
      have shifted : ∀ key : History F G,
          key.length ≤ (history ++ [event]).length + rest.length → table key = other key := by
        intro key bound
        apply agree
        simp only [List.length_append, List.length_cons, List.length_nil] at bound ⊢
        omega
      cases process with
      | done value => rfl
      | halt stop => rfl
      | call operation next =>
          cases operation with
          | receive ty site sender =>
              cases event with
              | message origin payload =>
                  simp only [replay]
                  split
                  · split
                    · exact ih _ _ shifted
                    · rfl
                  · rfl
              | binding _ _ => rfl
              | challenge _ => rfl
          | query site op arguments =>
              simp only [replay]
              split
              · have same : table (history ++ [event]) = other (history ++ [event]) := by
                  apply agree
                  simp
                rw [same]
                exact ih _ _ shifted
              · rfl
          | send site receiver sent =>
              simp only [replay]
              split
              · split
                · exact ih _ _ shifted
                · rfl
              · rfl

end ZkcSecurity.FiatShamir
