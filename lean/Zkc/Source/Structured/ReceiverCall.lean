module

public import Zkc.Source.Structured.ReceiverForwarding
public import Zkc.Source.Structured.MarkedPrefix
public import Zkc.Semantics.ReturnedPostcondition

@[expose] public section

/-! Source call marks and frame operations check the cursor while preserving
the oracle state. A child may change that state and its return value. -/
set_option autoImplicit false
namespace Zkc.Source.Structured.ReceiverForwarding
variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec} {math : OracleMathEnvironment}
  {S E A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
  (oracles : List (CheckedOracle snapshot domains math))
  (ordinary : PIR.MonadHandler m (participantInterfaceOn model.toCarriers) S E)
  (base : PIR.MonadHandler m (oracleReadInterface model.toCarriers) S E)
  (publish : PIR.MonadHandler m (OraclePublication.Interface model) S E)

local notation "Store" => OracleRuntimeState model snapshot domains math S
local notation "State" => OracleProtocol.State model snapshot domains math S
local notation "action" => OraclePublication.actionM model oracles ordinary base publish

theorem marks (original : Store) (labels : List (String × String)) :
    Keeps oracles ordinary base publish original
      (OracleProtocol.withMarks labels (.done ())) () := by
  induction labels with
  | nil => exact PIR.Process.ReturnsUnder.done _
  | cons label rest ih => exact (mark oracles ordinary base publish original label.1 label.2).call ih

private theorem enterCall (original : Store) (signature : ProtocolSignature) (site : String) :
    Keeps oracles ordinary base publish original (.call (.application signature site) .done) () := by
  apply PIR.Process.ReturnsUnder.action
  intro state same
  rw [OraclePublication.actionM_local _ _ _ _ _ _ rfl]
  apply Zkc.MonadicPostcondition.pure
  simp only [OracleProtocol.handler]
  repeat' split
  all_goals exact ⟨same, fun _ _ ↦ trivial⟩

private theorem leaveCall (original : Store) :
    Keeps oracles ordinary base publish original (.call .leave .done) () := by
  apply PIR.Process.ReturnsUnder.action
  intro state same
  rw [OraclePublication.actionM_local _ _ _ _ _ _ rfl]
  apply Zkc.MonadicPostcondition.pure
  simp only [OracleProtocol.handler]
  split <;> exact ⟨same, fun _ _ ↦ trivial⟩

/-- Lift a child law through the caller's actual marks, entry and exit.
The postcondition may refer to both the output and the final oracle store. -/
theorem atApplication (before : State) (labels : List (String × String))
    (signature : ProtocolSignature) (site : String) (child : PIR.Process (OracleProtocol.Interface model) A)
    (post : A → Store → Prop)
    (law : ∀ state : State, state.oracle = before.oracle →
      PIR.Process.OnReturn action state child (fun a next ↦ post a next.oracle)) :
    PIR.Process.OnReturn action before
      ((OracleProtocol.withMarks labels (.done ())).bind fun _ ↦
        OracleProtocol.enter model (.application signature site) child) (fun a next ↦ post a next.oracle) := by
  apply PIR.Process.OnReturn.bind (head := (marks oracles ordinary base publish before.oracle labels).onReturn rfl)
  intro _ marked valid
  change PIR.Process.OnReturn _ _ ((PIR.Process.call (I := OracleProtocol.Interface model) (.application signature site) .done).bind fun _ ↦
    child.bind fun a ↦ (PIR.Process.call (I := OracleProtocol.Interface model) .leave .done).bind fun _ ↦ .done a) _
  apply PIR.Process.OnReturn.bind (head := (enterCall oracles ordinary base publish before.oracle signature site).onReturn valid.1)
  intro _ entered kept
  apply PIR.Process.OnReturn.bind (head := law entered kept.1)
  intro a current correct
  apply PIR.Process.OnReturn.bind (head := (leaveCall oracles ordinary base publish current.oracle).onReturn rfl)
  intro _ final restored
  exact PIR.Process.OnReturn.done (restored.1 ▸ correct)

end Zkc.Source.Structured.ReceiverForwarding
