module

public import Zkc.Semantics.MonadExecution
public import Zkc.Semantics.SignatureSum

@[expose] public section

/-! Outcome-aware free effects for a stateful source interpretation.

An external reply contains its entire execution, including a stopped post-state and log.
Reifying this record is necessary: an ordinary `Process.call` does not run its continuation
when its handler stops. No runtime control step or log emission is an external operation.
The outer process is interpreted by the existing `Process.runM`.
-/

set_option autoImplicit false
namespace Zkc.Source.Structured.OracleProcess

/-- Requests retain the actual provider state; replies retain every possible outcome. -/
abbrev Effect (interface : PIR.Signature) (S E : Type) : PIR.Signature where
  Op := interface.Op × S
  Reply request := PIR.Execution S E (interface.Reply request.1)

variable {I J : PIR.Signature} {S T E F A B : Type}

/-- A returned outer execution is only an envelope; source stops remain inside it. -/
def envelope (value : A) : PIR.Execution Unit Empty A := ⟨.returned value, (), []⟩

/-- Adapt a pure external handler without swallowing its stopped execution. -/
def handler (external : PIR.Handler I S E) : PIR.Handler (Effect I S E) Unit Empty :=
  fun request _ ↦ envelope (external request.1 request.2)

/-- Adapt a monadic external handler. Its outer effects are exactly the caller's effects. -/
def handlerM {m : Type → Type} [Monad m] (external : PIR.MonadHandler m I S E) :
    PIR.MonadHandler m (Effect I S E) Unit Empty :=
  fun request _ ↦ do
    let result ← external request.1 request.2
    pure (envelope result)

theorem represents_effect (external : PIR.Handler I S E) (operation : I.Op) (state : S) :
    (.call (operation, state) .done : PIR.Process (Effect I S E) _).run (handler external) () =
      envelope (external operation state) := by
  simp [PIR.Process.run, handler, envelope, PIR.Execution.follow]

/-- Prefix-preserving sequencing also returns stopped source executions as data. -/
def sequence (first : PIR.Execution S E A)
    (next : A → S → PIR.Process J (PIR.Execution S E B)) :
    PIR.Process J (PIR.Execution S E B) :=
  match first.outcome with
  | .stopped reason => .done ⟨.stopped reason, first.state, first.events⟩
  | .returned value => (next value first.state).bind fun result ↦
      .done ⟨result.outcome, result.state, first.events ++ result.events⟩

/-- Change the returned record while keeping the external effects unchanged. -/
def mapResult (change : A → B) (process : PIR.Process J A) : PIR.Process J B :=
  process.bind fun value ↦ .done (change value)

/-- A complete equality, including the absence of outer stops or extra outer events. -/
def Represents (backend : PIR.Handler J Unit Empty) (process : PIR.Process J A)
    (value : A) : Prop := process.run backend () = envelope value

theorem represents_done (backend : PIR.Handler J Unit Empty) (value : A) :
    Represents backend (.done value) value := rfl

theorem represents_bind (backend : PIR.Handler J Unit Empty) (process : PIR.Process J A)
    (next : A → PIR.Process J B) (value : A) (result : B)
    (first : Represents backend process value) (tail : Represents backend (next value) result) :
    Represents backend (process.bind next) result := by
  unfold Represents at *
  rw [PIR.run_bind, first]
  simp only [envelope, PIR.Execution.follow]
  rw [tail]
  rfl

theorem represents_map (backend : PIR.Handler J Unit Empty) (change : A → B)
    (process : PIR.Process J A) (value : A) (law : Represents backend process value) :
    Represents backend (mapResult change process) (change value) :=
  represents_bind backend process _ value _ law (represents_done _ _)

theorem represents_sequence (backend : PIR.Handler J Unit Empty)
    (first : PIR.Execution S E A) (next : A → S → PIR.Process J (PIR.Execution S E B))
    (meaning : A → S → PIR.Execution S E B)
    (law : ∀ value state, Represents backend (next value state) (meaning value state)) :
    Represents backend (sequence first next) (first.follow meaning) := by
  cases first with
  | mk outcome state events =>
    cases outcome with
    | stopped reason => rfl
    | returned value =>
      exact represents_map backend (fun result ↦
        (⟨result.outcome, result.state, events ++ result.events⟩ : PIR.Execution S E B))
        _ _ (law value state)

/-- Read the existing Process structurally, preserving its complete execution record. -/
def present (operations : (operation : I.Op) → S →
    PIR.Process J (PIR.Execution S E (I.Reply operation))) :
    PIR.Process I A → S → PIR.Process J (PIR.Execution S E A)
  | .done value, state => .done ⟨.returned value, state, []⟩
  | .halt reason, state => .done ⟨.stopped reason, state, []⟩
  | .call operation next, state => (operations operation state).bind fun result ↦
      sequence result fun value current ↦ present operations (next value) current

/-- The generic proof is used with proved local laws, never a source-caller premise. -/
theorem represents_present (operations : (operation : I.Op) → S →
    PIR.Process J (PIR.Execution S E (I.Reply operation)))
    (backend : PIR.Handler J Unit Empty) (meaning : PIR.Handler I S E)
    (law : ∀ operation state, Represents backend (operations operation state)
      (meaning operation state)) (process : PIR.Process I A) (state : S) :
    Represents backend (present operations process state) (process.run meaning state) := by
  induction process generalizing state with
  | done => rfl
  | halt => rfl
  | call operation next ih =>
    exact represents_bind backend _ _ _ _ (law operation state)
      (represents_sequence backend _ _ _ ih)

/-- Execute only external calls, using the generic monadic runner.
The fallback is unreachable for the presentations proved below under the supplied adapter.
Outer monad failure can still produce no execution record, as for `Process.runM` itself. -/
def executeM {m : Type → Type} [Monad m] (external : PIR.MonadHandler m I S E)
    (process : PIR.Process (Effect I S E) (PIR.Execution T F A)) (initial : T) :
    m (PIR.Execution T F A) := do
  let result ← process.runM (handlerM external) ()
  pure (match result.outcome with
    | .returned record => record
    | .stopped reason => ⟨.stopped reason, initial, []⟩)

theorem executeM_pure {m : Type → Type} [Monad m] [LawfulMonad m]
    (external : PIR.Handler I S E)
    (process : PIR.Process (Effect I S E) (PIR.Execution T F A))
    (initial : T) (result : PIR.Execution T F A)
    (law : Represents (handler external) process result) :
    executeM (m := m) (fun operation state ↦ pure (external operation state)) process initial =
      pure result := by
  have adapted : handlerM (m := m) (fun operation state ↦ pure (external operation state)) =
      fun request state ↦ pure (handler external request state) := by
    funext request state
    simp [handlerM, handler]
  unfold executeM
  rw [adapted, PIR.runM_pure]
  simp [Represents, envelope] at law
  simp [law]

end Zkc.Source.Structured.OracleProcess
