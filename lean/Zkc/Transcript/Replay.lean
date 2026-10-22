module

public import Zkc.Transcript.Interface

@[expose] public section

/-! # Replay of a validator along absorbed events

`replay` walks a validator along absorbed events, recovering received replies
from their events and answering queries from a table of raw answers, read at
the absorbed history before each occurrence and the occurrence. It returns the
residual process after the last event, or `none` when the events are not a
history the transform could absorb from the process. Replay is a function of
the events and reads the table only at histories shorter than the replayed one
(`replay_congr`): the two facts the security arguments need.
-/

set_option autoImplicit false

namespace Zkc.Transcript

variable {I : PIR.Signature} {E P A : Type} {Raw : E → Type} [DecidableEq E]

/-- Walk `process` along the absorbed `events`, starting after `history`.
Received replies are recovered from their events and queries are answered by
decoding `table` at the history before their occurrence and the occurrence. The
result is the residual process after the last event, or `none` when the events
are not a history the transform could absorb from this process. -/
def replay (absorb : Interface I E P Raw) (table : (preceding : List E) → (event : E) → Raw event) :
    PIR.Process I A → List E → List E → Option (PIR.Process I A)
  | process, _, [] => some process
  | .done _, _, _ :: _ => none
  | .halt _, _, _ :: _ => none
  | .call operation next, history, observed :: rest =>
      match absorb operation with
      | .receive _ recover =>
          match recover observed with
          | some value => replay absorb table (next value) (history ++ [observed]) rest
          | none => none
      | .send event value =>
          if observed = event then replay absorb table (next value) (history ++ [observed]) rest
          else none
      | .query event decode =>
          if observed = event then
            match decode (table history event) with
            | some value => replay absorb table (next value) (history ++ [event]) rest
            | none => none
          else none
      | .refuse => none

variable (absorb : Interface I E P Raw) (table : (preceding : List E) → (event : E) → Raw event)

@[simp] theorem replay_nil (process : PIR.Process I A) (history : List E) :
    replay absorb table process history [] = some process := by
  cases process <;> rfl

/-- One received message, absorbed with its event. -/
theorem replay_receive {operation : I.Op} {next : I.Reply operation → PIR.Process I A}
    {event : P → E} {recover : E → Option (I.Reply operation)}
    (absorbed : absorb operation = .receive event recover) (history : List E) (message : P)
    {value : I.Reply operation} (recovered : recover (event message) = some value) :
    replay absorb table (.call operation next) history [event message] = some (next value) := by
  simp [replay, absorbed, recovered]

/-- One sent value, absorbed with its event. -/
theorem replay_send {operation : I.Op} {next : I.Reply operation → PIR.Process I A}
    {event : E} {value : I.Reply operation} (absorbed : absorb operation = .send event value)
    (history : List E) :
    replay absorb table (.call operation next) history [event] = some (next value) := by
  simp [replay, absorbed]

/-- One challenge occurrence, answered by decoding the table at it. -/
theorem replay_query {operation : I.Op} {next : I.Reply operation → PIR.Process I A}
    {event : E} {decode : Raw event → Option (I.Reply operation)}
    (absorbed : absorb operation = .query event decode) (history : List E)
    {value : I.Reply operation} (decoded : decode (table history event) = some value) :
    replay absorb table (.call operation next) history [event] = some (next value) := by
  simp [replay, absorbed, decoded]

/-- Replaying a concatenation replays the first part, then the second from the
residual and the extended history. -/
theorem replay_append (first second : List E) :
    ∀ (process : PIR.Process I A) (history : List E),
      replay absorb table process history (first ++ second) =
        (replay absorb table process history first).bind fun residual =>
          replay absorb table residual (history ++ first) second := by
  induction first with
  | nil => intro process history; simp
  | cons observed rest ih =>
      intro process history
      cases process with
      | done value => rfl
      | halt stop => rfl
      | call operation next =>
          rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
            ⟨event, decode⟩ | _
          · simp only [List.cons_append, replay, absorbed]
            cases recover observed with
            | none => rfl
            | some value => simp [ih]
          · simp only [List.cons_append, replay, absorbed]
            split
            · simp [ih]
            · rfl
          · simp only [List.cons_append, replay, absorbed]
            split
            · rename_i same
              subst same
              cases decode (table history observed) with
              | none => rfl
              | some value => simp [ih]
            · rfl
          · simp only [List.cons_append, replay, absorbed]
            rfl

/-- Replay reads the table only at histories shorter than the replayed one. -/
theorem replay_congr {other : (preceding : List E) → (event : E) → Raw event} (events : List E) :
    ∀ (process : PIR.Process I A) (history : List E),
      (∀ (preceding : List E) (event : E), preceding.length < history.length + events.length →
        table preceding event = other preceding event) →
      replay absorb table process history events = replay absorb other process history events := by
  induction events with
  | nil => intro process history _; simp
  | cons observed rest ih =>
      intro process history agree
      have shifted : ∀ (preceding : List E) (event : E),
          preceding.length < (history ++ [observed]).length + rest.length →
            table preceding event = other preceding event := by
        intro preceding event bound
        apply agree
        simp only [List.length_append, List.length_cons, List.length_nil] at bound ⊢
        omega
      cases process with
      | done value => rfl
      | halt stop => rfl
      | call operation next =>
          rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
            ⟨event, decode⟩ | _
          · simp only [replay, absorbed]
            cases recover observed with
            | none => rfl
            | some value => exact ih _ _ shifted
          · simp only [replay, absorbed]
            split
            · exact ih _ _ shifted
            · rfl
          · simp only [replay, absorbed]
            split
            · rename_i same
              subst same
              have agreeing : table history observed = other history observed := by
                apply agree
                simp
              rw [agreeing]
              cases decode (other history observed) with
              | none => rfl
              | some value => exact ih _ _ shifted
            · rfl
          · simp only [replay, absorbed]

end Zkc.Transcript
