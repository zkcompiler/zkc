module

public import Zkc.Source.Structured.OracleProcessExecution

@[expose] public section

/-! A free semantic view of the existing source protocol handler. Source control operations
reuse the original definitions after proving their independence from external handlers.
-/

set_option autoImplicit false
namespace Zkc.Source.Structured.OracleProcess
variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment} {S E A : Type}

/-- Ordinary effects and logical requests are the only nonlocal action arms. -/
def externalAction : OracleProtocolAction model.toCarriers → Bool
  | .ordinary _ | .oracle _ => true
  | _ => false

def refusingOrdinary : PIR.Handler (participantInterfaceOn model.toCarriers) S E :=
  fun _ state ↦ ⟨.stopped .refused, state, []⟩

/-- Marks, cursor/stack changes and data demand consult neither external handler. -/
theorem control_independent (model : DomainModel)
    (oracles : List (CheckedOracle snapshot domains math))
    (ordinaryLeft ordinaryRight : PIR.Handler (participantInterfaceOn model.toCarriers) S E)
    (baseLeft baseRight : PIR.Handler (oracleReadInterface model.toCarriers) S E)
    (action : OracleProtocolAction model.toCarriers)
    (state : OracleProtocol.State model snapshot domains math S)
    (effectFree : externalAction action = false) :
    OracleProtocol.handler model oracles ordinaryLeft baseLeft action state =
      OracleProtocol.handler model oracles ordinaryRight baseRight action state := by
  cases action <;> first | rfl | cases effectFree

/-- The process contains no caller-selected replacement for source control or table meaning. -/
def action (model : DomainModel) (oracles : List (CheckedOracle snapshot domains math))
    (action : OracleProtocolAction model.toCarriers)
    (state : OracleProtocol.State model snapshot domains math S) :
    PIR.Process (Interface model S E)
      (PIR.Execution (OracleProtocol.State model snapshot domains math S) (OracleProtocol.Event E)
        ((OracleProtocol.Interface model).Reply action)) :=
  match action with
  | .ordinary ordinary =>
    mapResult (fun result ↦
      ⟨result.outcome, {state with oracle.provider := result.state},
        result.events.map OracleProtocol.Event.ordinary⟩)
      (.call (.inl ordinary, state.oracle.provider) .done)
  | .oracle request =>
    if request.location.definition != state.frame.definition ||
        request.location.row != state.frame.row then .done ⟨.stopped .refused, state, []⟩
    else
      let location := {request.location with invocation := state.frame.invocation}
      mapResult (fun result ↦
        ⟨result.outcome, {state with oracle := result.state},
          result.events.map OracleProtocol.Event.logical⟩)
        (operation model oracles location request.self request.roles
          request.operation request.arguments state.oracle)
  | action =>
    .done (OracleProtocol.handler model oracles refusingOrdinary refusingBase action state)

theorem action_represents (model : DomainModel)
    (oracles : List (CheckedOracle snapshot domains math))
    (ordinary : PIR.Handler (participantInterfaceOn model.toCarriers) S E)
    (base : PIR.Handler (oracleReadInterface model.toCarriers) S E)
    (sourceAction : OracleProtocolAction model.toCarriers)
    (state : OracleProtocol.State model snapshot domains math S) :
    Represents (handler (externalHandler ordinary base)) (action model oracles sourceAction state)
      (OracleProtocol.handler model oracles ordinary base sourceAction state) := by
  cases sourceAction <;> try rfl
  case oracle request =>
    simp only [action, OracleProtocol.handler]
    split
    · rfl
    · exact represents_map _ _ _ _
        (operation_represents model oracles ordinary base _ _ _ _ _ state.oracle)

/-- Present the actual source process, including its halts and all reached control actions. -/
def protocol (model : DomainModel) (oracles : List (CheckedOracle snapshot domains math))
    (process : PIR.Process (OracleProtocol.Interface model) A)
    (state : OracleProtocol.State model snapshot domains math S) :
    PIR.Process (Interface model S E)
      (PIR.Execution (OracleProtocol.State model snapshot domains math S)
        (OracleProtocol.Event E) A) :=
  present (action model oracles) process state

/-- No interpreter-correspondence premise is required from a source caller. -/
theorem protocol_represents (model : DomainModel)
    (oracles : List (CheckedOracle snapshot domains math))
    (ordinary : PIR.Handler (participantInterfaceOn model.toCarriers) S E)
    (base : PIR.Handler (oracleReadInterface model.toCarriers) S E)
    (process : PIR.Process (OracleProtocol.Interface model) A)
    (state : OracleProtocol.State model snapshot domains math S) :
    Represents (handler (externalHandler ordinary base)) (protocol model oracles process state)
      (process.run (OracleProtocol.handler model oracles ordinary base) state) :=
  represents_present _ _ _ (action_represents model oracles ordinary base) process state

def externalHandlerM {m : Type → Type} [Monad m]
    (ordinary : PIR.MonadHandler m (participantInterfaceOn model.toCarriers) S E)
    (base : PIR.MonadHandler m (oracleReadInterface model.toCarriers) S E) :
    PIR.MonadHandler m (External model) S E
  | .inl action => ordinary action
  | .inr request => base request

/-- Install probabilistic or adversarial handlers in any selected monad. Both effects share S. -/
def runM {m : Type → Type} [Monad m] (model : DomainModel)
    (oracles : List (CheckedOracle snapshot domains math))
    (ordinary : PIR.MonadHandler m (participantInterfaceOn model.toCarriers) S E)
    (base : PIR.MonadHandler m (oracleReadInterface model.toCarriers) S E)
    (process : PIR.Process (OracleProtocol.Interface model) A)
    (state : OracleProtocol.State model snapshot domains math S) :
    m (PIR.Execution (OracleProtocol.State model snapshot domains math S)
        (OracleProtocol.Event E) A) :=
  executeM (externalHandlerM ordinary base) (protocol model oracles process state) state

/-- Identity/pure specialization recovers the complete current interpretation. -/
theorem runM_pure {m : Type → Type} [Monad m] [LawfulMonad m] (model : DomainModel)
    (oracles : List (CheckedOracle snapshot domains math))
    (ordinary : PIR.Handler (participantInterfaceOn model.toCarriers) S E)
    (base : PIR.Handler (oracleReadInterface model.toCarriers) S E)
    (process : PIR.Process (OracleProtocol.Interface model) A)
    (state : OracleProtocol.State model snapshot domains math S) :
    runM (m := m) model oracles (fun action state ↦ pure (ordinary action state))
      (fun request state ↦ pure (base request state)) process state =
        pure (process.run (OracleProtocol.handler model oracles ordinary base) state) := by
  have same : externalHandlerM (m := m) (fun action state ↦ pure (ordinary action state))
      (fun request state ↦ pure (base request state)) =
      fun operation state ↦ pure (externalHandler ordinary base operation state) := by
    funext operation state
    cases operation <;> rfl
  unfold runM
  rw [same]
  exact executeM_pure _ _ _ _ (protocol_represents model oracles ordinary base process state)

end Zkc.Source.Structured.OracleProcess
