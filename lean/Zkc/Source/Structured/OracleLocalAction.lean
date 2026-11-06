module

public import Zkc.Source.Structured.OraclePublication

@[expose] public section

/-! Protocol bookkeeping and logical metadata actions can be interpreted
without the network, base query provider or publication chooser. -/
set_option autoImplicit false
namespace Zkc.Source.Structured
variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment} {S E : Type}
  {m : Type → Type} [Monad m] [LawfulMonad m]

namespace OracleProcess

theorem operation_local (oracles : List (CheckedOracle snapshot domains math))
    (location : OracleLocation) (self : Nat) (roles : Nat → Nat) (op : OracleOp)
    (arguments : Values (Component (ProtocolValue model.toCarriers)) op.arguments)
    (state : OracleRuntimeState model snapshot domains math S) (closed : externalQuery op = false) :
    operation (E := E) model oracles location self roles op arguments state =
      .done (OracleExecution.operation model oracles refusingBase location self roles op arguments state) := by
  cases op <;> try rfl
  case query kind owner => cases owner with | none => rfl | some _ => cases closed

end OracleProcess

namespace OraclePublication

def localAction : OracleProtocolAction model.toCarriers → Bool
  | .ordinary _ => false
  | .oracle request => match request.operation with
    | .send .. => false
    | op => !OracleProcess.externalQuery op
  | _ => true

set_option smartUnfolding false in
theorem actionM_local (oracles : List (CheckedOracle snapshot domains math))
    (ordinary : PIR.MonadHandler m (participantInterfaceOn model.toCarriers) S E)
    (base : PIR.MonadHandler m (oracleReadInterface model.toCarriers) S E)
    (publish : PIR.MonadHandler m (Interface model) S E)
    (op : OracleProtocolAction model.toCarriers)
    (state : OracleProtocol.State model snapshot domains math S) (closed : localAction op = true) :
    actionM model oracles ordinary base publish op state =
      pure (OracleProtocol.handler model oracles OracleProcess.refusingOrdinary OracleProcess.refusingBase
        op state) := by
  have noPublication : ∀ candidate, request? (E := E) op state candidate = none := by
    cases op <;> try exact fun _ ↦ rfl
    case oracle request =>
      rcases request with ⟨oper, location, self, roles, arguments⟩
      cases oper <;> first | exact fun _ ↦ rfl | cases closed
  have original : OracleProcess.actionM model oracles ordinary base op state =
      pure (OracleProtocol.handler model oracles OracleProcess.refusingOrdinary OracleProcess.refusingBase
        op state) := by
    cases op <;> try exact OracleProcess.executeM_done _ _ _
    case ordinary => cases closed
    case oracle request =>
      rcases request with ⟨oper, location, self, roles, arguments⟩
      have localOp : OracleProcess.externalQuery oper = false := by
        cases oper <;> first | rfl | simpa [localAction] using closed
      unfold OracleProcess.actionM
      simp only [OracleProcess.action, OracleProtocol.handler]
      split
      · exact OracleProcess.executeM_done _ _ _
      · rw [OracleProcess.operation_local _ _ _ _ _ _ _ localOp]
        exact OracleProcess.executeM_done _ _ _
  simp only [actionM, original, pure_bind, afterM, noPublication]

end OraclePublication
end Zkc.Source.Structured
