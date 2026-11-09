module

public import Zkc.IR.Source.Structured.OracleProcessProtocol
public import Zkc.IR.Source.Structured.OracleIngress

@[expose] public section

/-! The canonical proof interface keeps the checked source subject and actual root ingress.
This presentation does not replace the source reader, checked bodies or protocol algebra.
-/

set_option autoImplicit false
namespace Zkc.Source.Structured.OracleProcess
variable {snapshot : Snapshot} {subject : OracleSubject snapshot}
  {model : DomainModel} {self : Nat} {S E : Type}

/-- Present the actual selected source root from its existing proof-carrying start. -/
def source (start : OracleStart subject model self S) :
    PIR.Process (Interface model S E)
      (PIR.Execution (OracleProtocol.State model subject.unit.snapshot subject.unit.domains
        subject.unit.math S) (OracleProtocol.Event E)
        (Values (Component (ProtocolValue model.toCarriers))
          subject.imported.program.payload.entry.outputs)) :=
  protocol model subject.unit.oracles
    (subject.imported.program.oracleParticipant model self start.installed.inputs) start.state

/-- Complete root correspondence for every pair of handlers; no success condition is used. -/
theorem source_represents (start : OracleStart subject model self S)
    (ordinary : PIR.Handler (participantInterfaceOn model.toCarriers) S E)
    (base : PIR.Handler (oracleReadInterface model.toCarriers) S E) :
    Represents (handler (externalHandler ordinary base)) (source start) (start.run ordinary base) :=
  protocol_represents model subject.unit.oracles ordinary base _ start.state

/-- Install lawful-monadic handlers without altering source, role, input or Oracle association. -/
def sourceRunM {m : Type → Type} [Monad m] (start : OracleStart subject model self S)
    (ordinary : PIR.MonadHandler m (participantInterfaceOn model.toCarriers) S E)
    (base : PIR.MonadHandler m (oracleReadInterface model.toCarriers) S E) :=
  runM model subject.unit.oracles ordinary base
    (subject.imported.program.oracleParticipant model self start.installed.inputs) start.state

/-- Exact specialization includes failed roots, source marks, provider logs and final frames. -/
theorem sourceRunM_pure {m : Type → Type} [Monad m] [LawfulMonad m]
    (start : OracleStart subject model self S)
    (ordinary : PIR.Handler (participantInterfaceOn model.toCarriers) S E)
    (base : PIR.Handler (oracleReadInterface model.toCarriers) S E) :
    sourceRunM (m := m) start (fun action state ↦ pure (ordinary action state))
      (fun request state ↦ pure (base request state)) = pure (start.run ordinary base) :=
  runM_pure model subject.unit.oracles ordinary base _ start.state

/-- Pure execution retains the established root-store invariant, even on failure. -/
theorem sourceRunM_reachable (start : OracleStart subject model self S)
    (ordinary : PIR.Handler (participantInterfaceOn model.toCarriers) S E)
    (base : PIR.Handler (oracleReadInterface model.toCarriers) S E) :
    OracleProtocol.Reachable (sourceRunM (m := Id) start ordinary base).state := by
  have same := sourceRunM_pure (m := Id) start ordinary base
  change sourceRunM (m := Id) start ordinary base = start.run ordinary base at same
  rw [same]
  exact start.run_reachable ordinary base

end Zkc.Source.Structured.OracleProcess
