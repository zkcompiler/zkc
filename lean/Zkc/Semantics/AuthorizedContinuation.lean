import Zkc.Semantics.ContinuationReport
import Zkc.Source.Endpoint

set_option autoImplicit false

namespace PIR.AuthorizedContinuation
open Continuation

variable {I : Signature} {P : Interaction I} {A B S E : Type}

/-- An actual admitted invocation. Source and immutable binding stay in the
    internal receipt. Construction alone does not authorize disclosure. -/
structure Invocation (F : Frontend I P.Role (Terminal A))
    (C : EndpointContract P (Terminal A)) where
  source : F.Source
  binding : F.Binding
  actor : P.Role
  body : Proc I (Terminal A)
  admitted : Admitted F C source binding actor body

/-- The installed service policy sees the actual source, binding and actor.
    Its Boolean decision is not supplied by the requester as an authority flag. -/
abbrev Policy (F : Frontend I P.Role (Terminal A)) :=
  F.Source → F.Binding → P.Role → Nat → Nat → Nat → Bool

/-- Authoritative state for one service instance. Target occurrences are unique
    in this instance; a source run receives the next monotone identifier.
    External serialized values are not an API for replacing this ledger. -/
structure Ledger where
  nextRun : Nat
  consumedTargets : List Nat
  deriving DecidableEq, Repr

def empty : Ledger := ⟨0, []⟩

structure Receipt (F : Frontend I P.Role (Terminal A)) where
  source : F.Source
  binding : F.Binding
  actor : P.Role
  run : Nat
  site : Nat
  consumer : Nat
  target : Nat
  report : Report S E A B

structure Result (F : Frontend I P.Role (Terminal A)) where
  receipt : Option (Receipt (S := S) (E := E) (B := B) F)
  combined : Execution S E B
  ledger : Ledger
  authorizedExport : Option B

def exportReturned : Outcome B → Option B
  | .returned b => some b
  | .stopped _ => none

def eraseValue : Outcome B → Outcome Unit
  | .returned _ => .returned ()
  | .stopped why => .stopped why

def decision : Outcome (Terminal A) → Outcome Bool
  | .returned (.accepted _) => .returned true
  | .returned .rejected => .returned false
  | .stopped why => .stopped why

/-- A concrete optional release schema, separate from the private receipt.
    It reveals decision/status information, never capture or return values.
    Use still requires permission to disclose those statuses in the experiment. -/
def publicStatus {F : Frontend I P.Role (Terminal A)}
    (out : Result (S := S) (E := E) (B := B) F) : Option (Outcome Bool) × Outcome Unit :=
  (out.receipt.map (fun r => decision r.report.verifier.outcome), eraseValue out.combined.outcome)

/-- The atomic adapter performs actual verification, consumes the fresh target
    before invoking the arm, and exports only a completed arm value. The arm
    receives runtime state S but has no ledger-writing capability. Already
    emitted effects are retained even when no export is authorized. -/
def execute (F : Frontend I P.Role (Terminal A)) (C : EndpointContract P (Terminal A))
    (policy : Policy F) (call : Invocation F C) (site consumer target : Nat)
    (handler : Handler I S E) (arm : A → Proc I B) (state : S) (ledger : Ledger) :
    Result (S := S) (E := E) (B := B) F :=
  if !(policy call.source call.binding call.actor site consumer target) then
    ⟨none, ⟨.stopped .refused, state, []⟩, ledger, none⟩
  else if target ∈ ledger.consumedTargets then
    ⟨none, ⟨.stopped .refused, state, []⟩, ledger, none⟩
  else
    let first := call.body.run handler state
    let next : Ledger := ⟨ledger.nextRun + 1, ledger.consumedTargets⟩
    match first.outcome with
    | .returned (.accepted a) =>
      let consumed : Ledger := ⟨next.nextRun, target :: next.consumedTargets⟩
      let last := (arm a).run handler first.state
      let combined := ⟨last.outcome, last.state, first.events ++ last.events⟩
      let receipt : Receipt F := ⟨call.source, call.binding, call.actor, ledger.nextRun,
        site, consumer, target, ⟨first, some last, combined⟩⟩
      ⟨some receipt, combined, consumed, exportReturned last.outcome⟩
    | .returned .rejected =>
      let combined : Execution S E B := ⟨.stopped .reject, first.state, first.events⟩
      ⟨some ⟨call.source, call.binding, call.actor, ledger.nextRun, site, consumer, target,
        ⟨first, none, combined⟩⟩, combined, next, none⟩
    | .stopped why =>
      let combined : Execution S E B := ⟨.stopped why, first.state, first.events⟩
      ⟨some ⟨call.source, call.binding, call.actor, ledger.nextRun, site, consumer, target,
        ⟨first, none, combined⟩⟩, combined, next, none⟩

/-- Installed interpretation of one service. The request cannot replace its
    arm, handler or policy. Native identity must select this actual service.
    The arm's phase and bound obligations are part of installation. -/
structure Service (F : Frontend I P.Role (Terminal A))
    (C : EndpointContract P (Terminal A)) (S E B : Type) where
  policy : Policy F
  handler : Handler I S E
  arm : A → Proc I B
  armBound : Nat
  armConforms : ∀ a phase, C.returned (.accepted a) phase → Conforms P (arm a) phase
  armBounded : ∀ a, Within armBound (arm a)

def Service.invoke {F : Frontend I P.Role (Terminal A)} {C : EndpointContract P (Terminal A)}
    (service : Service F C S E B) (call : Invocation F C)
    (site consumer target : Nat) (state : S) (ledger : Ledger) :
    Result (S := S) (E := E) (B := B) F :=
  execute F C service.policy call site consumer target service.handler service.arm state ledger

theorem Service.formed {F : Frontend I P.Role (Terminal A)} {C : EndpointContract P (Terminal A)}
    (service : Service F C S E B) (call : Invocation F C) :
    Conforms P (after call.body service.arm) C.initialPhase :=
  Continuation.formed P call.body service.arm C.returned C.initialPhase
    call.admitted.conforms call.admitted.returned service.armConforms

theorem Service.bounded {F : Frontend I P.Role (Terminal A)} {C : EndpointContract P (Terminal A)}
    (service : Service F C S E B) (call : Invocation F C) :
    Within (C.publicBound + service.armBound) (after call.body service.arm) := by
  apply Boundary.within_bind _ _ _ _ call.admitted.bounded
  intro result
  cases result with
  | accepted a => exact service.armBounded a
  | rejected => cases service.armBound <;> trivial

variable (F : Frontend I P.Role (Terminal A)) (C : EndpointContract P (Terminal A))
variable (policy : Policy F) (call : Invocation F C) (site consumer target : Nat)
variable (handler : Handler I S E) (arm : A → Proc I B) (state : S) (ledger : Ledger)

theorem replay_refused (used : target ∈ ledger.consumedTargets) :
    execute F C policy call site consumer target handler arm state ledger =
      ⟨none, ⟨.stopped .refused, state, []⟩, ledger, none⟩ := by
  by_cases allowed : policy call.source call.binding call.actor site consumer target = true <;>
    simp [execute, allowed, used]

theorem unauthorized_refused
    (denied : policy call.source call.binding call.actor site consumer target = false) :
    execute F C policy call site consumer target handler arm state ledger =
      ⟨none, ⟨.stopped .refused, state, []⟩, ledger, none⟩ := by
  simp [execute, denied]

theorem source_bound (allowed : policy call.source call.binding call.actor site consumer target = true)
    (fresh : target ∉ ledger.consumedTargets) :
    ∃ receipt, (execute F C policy call site consumer target handler arm state ledger).receipt =
      some receipt ∧ receipt.source = call.source ∧ receipt.binding = call.binding ∧
      receipt.actor = call.actor ∧ receipt.run = ledger.nextRun ∧
      receipt.site = site ∧ receipt.consumer = consumer ∧ receipt.target = target ∧
      receipt.report.verifier = call.body.run handler state := by
  cases h : (call.body.run handler state).outcome with
  | stopped why => simp [execute, allowed, fresh, h]
  | returned value => cases value <;> simp [execute, allowed, fresh, h]

theorem actual_report (allowed : policy call.source call.binding call.actor site consumer target = true)
    (fresh : target ∉ ledger.consumedTargets) :
    (execute F C policy call site consumer target handler arm state ledger).combined =
      (after call.body arm).run handler state := by
  cases h : (call.body.run handler state).outcome with
  | stopped why => simp [execute, allowed, fresh, h, stopped_no_arm call.body arm handler state why h]
  | returned value =>
    cases value with
    | rejected => simp [execute, allowed, fresh, h, rejected_no_arm call.body arm handler state h]
    | accepted a => simp [execute, allowed, fresh, h, accepted_retains_prefix call.body arm handler state a h]

theorem accepted_consumed (allowed : policy call.source call.binding call.actor site consumer target = true)
    (fresh : target ∉ ledger.consumedTargets) (a : A)
    (accepted : (call.body.run handler state).outcome = .returned (.accepted a)) :
    target ∈ (execute F C policy call site consumer target handler arm state ledger).ledger.consumedTargets := by
  simp [execute, allowed, fresh, accepted]

theorem failed_arm_no_export (allowed : policy call.source call.binding call.actor site consumer target = true)
    (fresh : target ∉ ledger.consumedTargets) (a : A)
    (accepted : (call.body.run handler state).outcome = .returned (.accepted a))
    (why : Stop) (failed : ((arm a).run handler (call.body.run handler state).state).outcome =
      .stopped why) :
    (execute F C policy call site consumer target handler arm state ledger).authorizedExport = none := by
  simp [execute, allowed, fresh, accepted, failed, exportReturned]

/-- Receipt authenticity means correspondence to this actual transition.
    Merely deserializing a record with the same field names does not prove it. -/
def Authentic (out : Result (S := S) (E := E) (B := B) F) : Prop :=
  out = execute F C policy call site consumer target handler arm state ledger

end PIR.AuthorizedContinuation
