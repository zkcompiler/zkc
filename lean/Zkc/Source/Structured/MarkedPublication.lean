module

public import Zkc.Source.Structured.MarkedPrefix
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

end Zkc.Source.Structured.OraclePublication
