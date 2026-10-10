import Zkc.Compiler.Role.Simulation.Source

/-! A source-cut controller for real independent cursors. `tick` runs exactly
one exposed request, retaining failed-action state/events. `select` leaves an
unselected cursor literally unchanged. Successful cuts carry actual joint
replies; message send/receive failure halves are treated separately below. -/
set_option autoImplicit false
namespace Zkc.Compiler.Role.Driver
open Simulation

variable {I J : PIR.Signature} {A B S E : Type}

/-- Install a completed primitive result, including failed-action effects. -/
def accept {Reply : Type} (next : Reply → PIR.Proc J B)
    (result : PIR.Execution S E Reply) (events : List E) : Cursor J S E B :=
  ⟨match result.outcome with
    | .returned reply => next reply
    | .stopped reason => .halt reason,
    result.state, events ++ result.events⟩

/-- Exactly one exposed local action; no normalization of a peer is requested. -/
def tick (handler : PIR.Handler J S E) (cursor : Cursor J S E B) : Cursor J S E B :=
  match cursor.program with
  | .done _ | .halt _ => cursor
  | .call action next =>
      accept next (handler action cursor.state) cursor.events

/-- The selected source view controls whether the endpoint runs one action. -/
def select (view : (op : I.Op) → View I J op) (op : I.Op)
    (handler : PIR.Handler J S E) (cursor : Cursor J S E B) : Cursor J S E B :=
  match view op with
  | .request .. => tick handler cursor
  | .silent | .terminal .. => cursor

/-- On an actual request, the existing runner consumes precisely the same result. -/
theorem tick_advance (handler : PIR.Handler J S E) (op : J.Op)
    (next : J.Reply op → PIR.Proc J B) (state : S) (events : List E) :
    advance (fun op state => some (handler op state)) 1 ⟨.call op next, state, events⟩ =
      advance (fun op state => some (handler op state)) 0
        (tick handler ⟨.call op next, state, events⟩) := by
  cases h : handler op state with
  | mk outcome final emitted =>
      cases outcome <;> simp only [advance, tick, accept, h]

abbrev Cut (I : PIR.Signature) := (op : I.Op) × I.Reply op

/-- A finite prefix of the joint tree, including value-dependent continuations. -/
inductive SourcePrefix : PIR.Proc I A → List (Cut I) → PIR.Proc I A → Prop where
  | nil (p) : SourcePrefix p [] p
  | cons (op : I.Op) (next : I.Reply op → PIR.Proc I A) (reply : I.Reply op)
      {cuts tail} (rest : SourcePrefix (next reply) cuts tail) :
      SourcePrefix (.call op next) (⟨op, reply⟩ :: cuts) tail

/-- The actual joint handler determines the successful source cuts. A failed
request is left at the boundary for the separately modelled failure step. -/
def successfulTrace (handler : PIR.Handler I S E) :
    PIR.Proc I A → S → List (Cut I) × PIR.Proc I A
  | .done value, _ => ([], .done value)
  | .halt reason, _ => ([], .halt reason)
  | .call op next, state =>
      let result := handler op state
      match result.outcome with
      | .stopped _ => ([], .call op next)
      | .returned reply =>
          let rest := successfulTrace handler (next reply) result.state
          (⟨op, reply⟩ :: rest.1, rest.2)

/-- No arbitrary schedule premise: the trace is produced by the actual joint
source execution, stopping before its first failed primitive. -/
theorem successfulTrace_source (handler : PIR.Handler I S E) (p : PIR.Proc I A) (state : S) :
    SourcePrefix p (successfulTrace handler p state).1 (successfulTrace handler p state).2 := by
  induction p generalizing state with
  | done value => exact .nil _
  | halt reason => exact .nil _
  | call op next ih =>
      cases h : handler op state with
      | mk outcome final emitted =>
          cases outcome with
          | stopped reason => simp only [successfulTrace, h]; exact .nil _
          | returned reply =>
              simp only [successfulTrace, h]
              exact .cons op next reply (ih reply final)

/-- Each cut may supply an external receive strategy. The endpoint sees only
its own state and current request; it receives no peer completion flag. -/
abbrev Services (I J : PIR.Signature) (S E : Type) := I.Op → PIR.Handler J S E

def drive (view : (op : I.Op) → View I J op) (services : Services I J S E) :
    List (Cut I) → Cursor J S E B → Cursor J S E B
  | [], cursor => cursor
  | cut :: rest, cursor => drive view services rest
      (select view cut.1 (services cut.1) cursor)

/-- Per-action reply coupling, not a correctness theorem for whole programs.
In a message receiver case this must be the actual delivered reply. -/
def ReplyCoupled (view : (op : I.Op) → View I J op) (services : Services I J S E)
    (cut : Cut I) (cursor : Cursor J S E B) : Prop :=
  match view cut.1 with
  | .silent => True
  | .request action map =>
      (services cut.1 action cursor.state).outcome = .returned (map cut.2)
  | .terminal .. => False

def Coupled (view : (op : I.Op) → View I J op) (services : Services I J S E) :
    List (Cut I) → Cursor J S E B → Prop
  | [], _ => True
  | cut :: rest, cursor => ReplyCoupled view services cut cursor ∧
      Coupled view services rest (select view cut.1 (services cut.1) cursor)

/-- An open endpoint may take these successful steps with these actual services.
No step is required for a foreign source action. -/
inductive OpenPrefix : Cursor J S E B → Cursor J S E B → Prop where
  | refl (cursor) : OpenPrefix cursor cursor
  | step (handler : PIR.Handler J S E) (action : J.Op)
      (next : J.Reply action → PIR.Proc J B) (state : S) (events : List E)
      (reply : J.Reply action)
      (success : (handler action state).outcome = .returned reply)
      {last : Cursor J S E B}
      (rest : OpenPrefix (tick handler ⟨.call action next, state, events⟩) last) :
      OpenPrefix ⟨.call action next, state, events⟩ last

theorem selected_success (view : (op : I.Op) → View I J op) (result : A → B)
    (services : Services I J S E) (op : I.Op) (next : I.Reply op → PIR.Proc I A)
    (reply : I.Reply op) (cursor : Cursor J S E B)
    (aligned : Aligned view result (.call op next) cursor.program)
    (coupled : ReplyCoupled view services ⟨op, reply⟩ cursor) :
    Aligned view result (next reply) (select view op (services op) cursor).program := by
  simp only [Aligned] at aligned
  cases v : view op with
  | silent =>
      simp only [v] at aligned
      simpa only [select, v] using aligned reply
  | terminal reason noReply => exact False.elim (noReply reply)
  | request action map =>
      simp only [v] at aligned
      obtain ⟨tail, head, aligned⟩ := aligned
      simp only [ReplyCoupled, v] at coupled
      simpa only [select, v, tick, accept, head, coupled] using aligned reply

/-- Generic finite prefix simulation between different trees/result types.
It proves retained continuation alignment and actual open endpoint reachability. -/
theorem prefix_simulation (view : (op : I.Op) → View I J op) (result : A → B)
    (services : Services I J S E) {p tail : PIR.Proc I A} {cuts : List (Cut I)}
    (path : SourcePrefix p cuts tail) (cursor : Cursor J S E B)
    (aligned : Aligned view result p cursor.program)
    (coupled : Coupled view services cuts cursor) :
    Aligned view result tail (drive view services cuts cursor).program ∧
      OpenPrefix cursor (drive view services cuts cursor) := by
  induction path generalizing cursor with
  | nil p => exact ⟨aligned, .refl cursor⟩
  | @cons op next reply cuts tail rest ih =>
      obtain ⟨this, later⟩ := coupled
      have related := selected_success view result services op next reply cursor aligned this
      obtain ⟨final, reachable⟩ := ih _ related later
      refine ⟨final, ?_⟩
      cases v : view op with
      | silent => simpa only [drive, select, v] using reachable
      | terminal reason noReply => exact False.elim (noReply reply)
      | request action map =>
          simp only [Aligned, v] at aligned
          obtain ⟨nextLocal, head, _⟩ := aligned
          simp only [ReplyCoupled, v] at this
          cases cursor with
          | mk program state events =>
              dsimp only at head
              subst program
              exact .step (services op) action nextLocal state events (map reply) this
                (by simpa only [drive, select, v] using reachable)

/-- An unselected cursor keeps its pending action, state and complete event prefix. -/
theorem select_silent (view : (op : I.Op) → View I J op) (op : I.Op)
    (handler : PIR.Handler J S E) (cursor : Cursor J S E B) (silent : view op = .silent) :
    select view op handler cursor = cursor := by simp only [select, silent]

/-- An active failure records the actual post-state, emits its effects and drops
only this endpoint's suffix. Peers are retained by `select_silent`. -/
theorem tick_stopped (handler : PIR.Handler J S E) (action : J.Op)
    (next : J.Reply action → PIR.Proc J B) (state final : S) (events emitted : List E)
    (reason : PIR.Stop) (stopped : handler action state = ⟨.stopped reason, final, emitted⟩) :
    tick handler ⟨.call action next, state, events⟩ =
      ⟨.halt reason, final, events ++ emitted⟩ := by simp only [tick, accept, stopped]

end Zkc.Compiler.Role.Driver
