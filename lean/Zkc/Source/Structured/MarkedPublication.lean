module

public import Zkc.Source.Structured.MarkedPrefix
public import Zkc.Source.Structured.OracleMetadata
public import Zkc.Source.Structured.ReceiverForwarding

@[expose] public section

/-! Split the original run at the first non-mark action. All marks run under
the publication handler. On success only the source frame has advanced. -/
set_option autoImplicit false
namespace Zkc.Source.Structured.OraclePublication
open OracleProtocol (withMarks)
variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment} {S E A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
  (oracles : List (CheckedOracle snapshot domains math))
  (ordinary : PIR.MonadHandler m (participantInterfaceOn model.toCarriers) S E)
  (base : PIR.MonadHandler m (oracleReadInterface model.toCarriers) S E)
  (publish : PIR.MonadHandler m (Interface model) S E)

private theorem keepsMarks (original : OracleRuntimeState model snapshot domains math S)
    (marks : List (String × String)) :
    ReceiverForwarding.Keeps oracles ordinary base publish original
      (withMarks marks (.done ())) () := by
  induction marks with
  | nil => exact PIR.Process.ReturnsUnder.done ()
  | cons mark marks ih =>
    exact PIR.Process.ReturnsUnder.call
      (ReceiverForwarding.mark oracles ordinary base publish original _ _) ih

/-- A law for the first action may use the original logical store even when
the preceding marks change the cursor. A failed mark skips the entire suffix. -/
theorem runMarked (marks : List (String × String))
    (process : PIR.Process (OracleProtocol.Interface model) A)
    (state : OracleProtocol.State model snapshot domains math S)
    (next : OracleProtocol.State model snapshot domains math S →
      m (PIR.Execution (OracleProtocol.State model snapshot domains math S) (OracleProtocol.Event E) A))
    (law : ∀ current, current.oracle = state.oracle →
      process.runM (actionM model oracles ordinary base publish) current = next current) :
    (withMarks marks process).runM (actionM model oracles ordinary base publish) state =
      ((withMarks marks (.done ())).runM (actionM model oracles ordinary base publish) state >>=
        fun record ↦ record.followM fun () ↦ next) := by
  have split := OracleProtocol.withMarks_bind (model := model) marks (.done ()) (fun _ ↦ process)
  change (withMarks marks ((PIR.Process.done ()).bind fun _ ↦ process)).runM _ state = _
  rw [← split, PIR.runM_bind]
  apply MonadicPostcondition.continuation (keepsMarks oracles ordinary base publish state.oracle marks state rfl)
  rintro ⟨outcome, current, events⟩ kept
  cases outcome with
  | stopped why => rfl
  | returned reply => cases reply; simp only [PIR.Execution.followM, law current kept.1]

/-- Lift an outcome and logical store predicate through the checked marks of an original
execution. A mark can refuse, and every successful mark preserves the store. -/
theorem markedOutcomes (marks : List (String × String))
    (process : PIR.Process (OracleProtocol.Interface model) A)
    (property : PIR.Outcome A → OracleRuntimeState model snapshot domains math S → Prop)
    (refusal : ∀ store, property (.stopped .refused) store)
    (original : OracleRuntimeState model snapshot domains math S)
    (tail : ∀ current, current.oracle = original → Std.Do.Internal.Ensures (fun result ↦ property result.outcome result.state.oracle)
      (process.runM (actionM model oracles ordinary base publish) current))
    (state : OracleProtocol.State model snapshot domains math S) (same : state.oracle = original) :
    Std.Do.Internal.Ensures (fun result ↦ property result.outcome result.state.oracle)
      ((withMarks marks process).runM (actionM model oracles ordinary base publish) state) := by
  induction marks generalizing state with
  | nil => exact tail state same
  | cons mark marks ih =>
    rcases mark with ⟨source, observed⟩
    rw [withMarks, PIR.Process.runM, actionM_local _ _ _ _ _ _ rfl, pure_bind]
    simp only [OracleProtocol.handler]
    split
    · exact MonadicPostcondition.pure _ _ (refusal _)
    · rename_i frame _
      simp only [PIR.Execution.followM]
      apply MonadicPostcondition.map (ih {state with frame := frame} same)
      exact fun _ valid ↦ valid

/-- Run one original iteration frame around a state-sensitive callback
postcondition. Entry or exit may refuse. A stopped body skips the exit,
and a successful exit preserves the store produced by the body. -/
theorem iterationOutcomes (site : String) (index : Nat)
    (process : PIR.Process (OracleProtocol.Interface model) A)
    (property : PIR.Outcome A → OracleRuntimeState model snapshot domains math S → Prop)
    (refusal : ∀ store, property (.stopped .refused) store)
    (state : OracleProtocol.State model snapshot domains math S)
    (body : ∀ current, current.oracle = state.oracle →
      Std.Do.Internal.Ensures (fun result ↦ property result.outcome result.state.oracle)
        (process.runM (actionM model oracles ordinary base publish) current)) :
    Std.Do.Internal.Ensures (fun result ↦ property result.outcome result.state.oracle)
      ((OracleProtocol.enter model (.iteration site index) process).runM
        (actionM model oracles ordinary base publish) state) := by
  simp only [OracleProtocol.enter, PIR.Process.bind, PIR.Process.runM,
    actionM_local oracles ordinary base publish (.iteration site index) _ rfl, OracleProtocol.handler, pure_bind]
  split
  · exact MonadicPostcondition.pure _ _ (refusal _)
  · simp only [PIR.Execution.followM]
    apply MonadicPostcondition.map _ _ (fun _ valid ↦ valid)
    rw [PIR.runM_bind]
    refine Std.Do.Internal.Ensures.bind (P := fun r ↦ property r.outcome r.state.oracle) ?head ?_
    case head => exact body _ rfl
    rintro ⟨out, current, events⟩ valid
    cases out with
    | stopped why => exact MonadicPostcondition.pure _ _ valid
    | returned value =>
      simp only [PIR.Execution.followM]
      simp only [PIR.Process.runM, actionM_local oracles ordinary base publish .leave _ rfl, OracleProtocol.handler, pure_bind]
      split
      · simp only [PIR.Execution.followM, pure_bind]
        exact MonadicPostcondition.pure _ _ (refusal _)
      · simp only [PIR.Execution.followM, pure_bind]
        exact MonadicPostcondition.pure _ _ valid

/-- Compose a deterministic cell or metadata reply with the actual marked
continuation. A stale source frame refuses before the continuation. The
reply may change the store and emit events, as a virtual read does. -/
theorem markedReplyOutcomes {op : (OracleProtocol.Interface model).Op}
    {after : ((OracleProtocol.Interface model).Reply op → PIR.Process (OracleProtocol.Interface model) A) → Prop}
    {process : PIR.Process (OracleProtocol.Interface model) A}
    (head : OracleProtocol.AtMarkedCall op after process) (site : OracleLocation)
    (reply : (OracleProtocol.Interface model).Reply op)
    (original post : OracleRuntimeState model snapshot domains math S)
    (trace : OracleProtocol.State model snapshot domains math S → List (OracleProtocol.Event E))
    (action : ∀ current, current.oracle = original → actionM model oracles ordinary base publish op current =
      pure (cursorReply site current reply post (trace current)))
    (property : PIR.Outcome A → OracleRuntimeState model snapshot domains math S → Prop)
    (refusal : ∀ store, property (.stopped .refused) store)
    (tail : ∀ next, after next → ∀ current, current.oracle = post →
      Std.Do.Internal.Ensures (fun result ↦ property result.outcome result.state.oracle)
        ((next reply).runM (actionM model oracles ordinary base publish) current))
    (state : OracleProtocol.State model snapshot domains math S) (same : state.oracle = original) :
    Std.Do.Internal.Ensures (fun result ↦ property result.outcome result.state.oracle)
      (process.runM (actionM model oracles ordinary base publish) state) := by
  obtain ⟨marks, next, eqn, valid⟩ := head
  rw [eqn]
  apply markedOutcomes oracles ordinary base publish marks _ property refusal original _ state same
  intro current kept
  rw [PIR.Process.runM, action current kept, pure_bind]
  unfold cursorReply
  split
  · simp only [PIR.Execution.followM]
    apply MonadicPostcondition.map (tail next valid _ rfl)
    exact fun _ ok ↦ ok
  · exact MonadicPostcondition.pure _ _ (refusal _)

end Zkc.Source.Structured.OraclePublication
