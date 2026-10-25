module

public import Zkc.Construction.DomainProducer
public import Zkc.Construction.OriginalSimulation

@[expose] public section

/-! Explicit abstraction of administrative physical frames.

The original process has no physical SSA checkpoints. Its proof/ROM/private
service state and ordered observations agree with the constructed execution
under this named projection. The construction simulation separately retains
all physical frames, the full return ABI, and their live-value obligations.
This projection never identifies oracle states or discards unread proof bytes.
-/
set_option autoImplicit false
namespace Zkc.Construction.Domain
open Zkc.Source

variable {carriers : Structured.Carriers} {S A : Type} {m : Type → Type}
  [Monad m] [LawfulMonad m]

structure InteractionState (carriers : Structured.Carriers) (S : Type) where
  proof : Proof carriers
  oracle : S

def RuntimeState.interaction (state : RuntimeState carriers S) : InteractionState carriers S :=
  ⟨state.proof, state.oracle⟩

/-- Reuse the actual handler and expose its interaction state. No source
arithmetic or protocol operation is reimplemented by this abstraction. -/
def interactionHandler (mode : Mode) (oracle : Oracle m carriers S)
    (services : LocalServices m carriers S) :
    PIR.MonadHandler m (effects carriers) (InteractionState carriers S) (Event carriers) :=
  fun operation state => do
    let result ← handler mode oracle services operation ⟨[], state.proof, state.oracle⟩
    pure ⟨result.outcome, result.state.interaction, result.events⟩

/-- Runtime physical frames cannot affect any query, reply, proof-buffer
transition, stop, service post-state, or observation of the current handler. -/
theorem handler_interaction (mode : Mode) (oracle : Oracle m carriers S)
    (services : LocalServices m carriers S) (operation : (effects carriers).Op)
    (state : RuntimeState carriers S) :
    interactionHandler mode oracle services operation state.interaction =
      (handler mode oracle services operation state >>= fun result =>
        PIR.Execution.expand (fun state => pure state.interaction) result) := by
  cases state with
  | mk environment proof oracleState =>
    cases operation <;>
      simp only [interactionHandler, handler, RuntimeState.interaction, PIR.Execution.expand,
        bind_assoc, pure_bind]
    case receive ty site schema peer =>
      cases mode <;> cases proof <;> simp only [pure_bind]
      split <;> simp only [pure_bind]
    case query history origin =>
      split <;> simp only [bind_assoc, pure_bind]
    case send site schema peer payload =>
      cases mode <;> simp only [pure_bind]

/-- Exact state abstraction in every lawful outer monad. Failure mass and all
inner stopped prefixes remain part of the same execution. -/
theorem run_interaction (mode : Mode) (oracle : Oracle m carriers S)
    (services : LocalServices m carriers S)
    (process : PIR.Process (effects carriers) A) (state : RuntimeState carriers S) :
    process.runM (interactionHandler mode oracle services) state.interaction =
      (run mode oracle process state services >>= fun result =>
        PIR.Execution.expand (fun state => pure state.interaction) result) := by
  have law := PIR.runM_expand (m := m) (fun state : RuntimeState carriers S => pure state.interaction)
    (handler mode oracle services) (interactionHandler mode oracle services)
    (fun operation state => by simpa only [pure_bind] using handler_interaction mode oracle services operation state)
    process state
  simpa only [pure_bind, run] using law

private theorem runM_operation {I : PIR.Signature} {T E : Type}
    (handler : PIR.MonadHandler m I T E) (operation : I.Op) (state : T) :
    (PIR.Process.call operation .done).runM handler state = handler operation state := by
  simp only [PIR.Process.runM]
  have continuation : (fun result : PIR.Execution T E (I.Reply operation) =>
      result.followM (m := m) (fun value state => pure ⟨.returned value, state, []⟩)) = pure := by
    funext result
    cases result with
    | mk outcome state events =>
      cases outcome <;> simp [PIR.Execution.followM]
  rw [continuation]
  exact bind_pure _

/-- Checkpoint erasure is legitimate exactly at the explicit interaction-state
abstraction. It is not equality of complete physical runtime frames. -/
theorem interaction_forgetCheckpoints (mode : Mode) (oracle : Oracle m carriers S)
    (services : LocalServices m carriers S)
    (process : PIR.Process (effects carriers) A) (state : InteractionState carriers S) :
    (process.interpret Original.forgetCheckpoints).runM (interactionHandler mode oracle services) state =
      process.runM (interactionHandler mode oracle services) state := by
  rw [PIR.runM_interpret]
  congr 1
  funext operation current
  cases operation <;> simp only [Original.forgetCheckpoints]
  all_goals first
    | exact runM_operation (I := effects carriers) (interactionHandler mode oracle services) _ _
    | simp only [PIR.Process.runM, interactionHandler, handler, pure_bind,
        RuntimeState.interaction]

end Zkc.Construction.Domain
