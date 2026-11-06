module

public import Zkc.Source.Structured.OracleProcessTotal
public import ZkcSecurity.Mathematics.Oracle.Coupling
public import ZkcSecurity.ProgramLogic.Oracle.Execution

@[expose] public section

/-! Local provider distribution laws for the actual logical-oracle source execution.
The existing Process replacement theorem consumes complete execution records, including
failed state and ordered events. No source-specific correspondence premise is introduced.
Internal oracle-query costs need their own charge law; equal output distributions do not
identify the number of hidden provider queries.
-/

set_option autoImplicit false
namespace ZkcSecurity.VCVio.OracleSource

open OracleComp OracleSpec
open Zkc.Source Zkc.Source.Structured
open ZkcSecurity.VCVio.Execution

variable {I : PIR.Signature} {S T E F A : Type}

/-- An external provider's complete distribution law survives the outcome-aware envelope. -/
theorem handler_sameDist
    (left right : PIR.MonadHandler ProbComp I S E)
    (law : ∀ operation state, SameDist (left operation state) (right operation state))
    (request : (OracleProcess.Effect I S E).Op) (state : Unit) :
    SameDist (OracleProcess.handlerM left request state)
      (OracleProcess.handlerM right request state) := by
  let : MeasurableSpace (PIR.Execution Unit Empty (PIR.Execution S E (I.Reply request.1))) := ⊤
  exact (law request.1 request.2).bind_left (fun result ↦ pure (OracleProcess.envelope result))

/-- Replace providers in a free presentation without losing failed records or conditioning
on success. The same postprocessing is applied to the full outer execution on both sides. -/
theorem execute_sameDist
    (left right : PIR.MonadHandler ProbComp I S E)
    (law : ∀ operation state, SameDist (left operation state) (right operation state))
    (process : PIR.Process (OracleProcess.Effect I S E) (PIR.Execution T F A))
    (initial : T) :
    SameDist (OracleProcess.executeM left process initial)
      (OracleProcess.executeM right process initial) := by
  let : MeasurableSpace (PIR.Execution T F A) := ⊤
  exact (Execution.runM_sameDist _ _ (handler_sameDist left right law) process ()).bind_left _

variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment}

/-- Ordinary services and base-table reads share one state. Their local laws apply through
all checked virtual-table expansions, source control and reply-dependent continuations. -/
theorem protocol_sameDist
    (oracles : List (CheckedOracle snapshot domains math))
    (ordinaryLeft ordinaryRight :
      PIR.MonadHandler ProbComp (participantInterfaceOn model.toCarriers) S E)
    (baseLeft baseRight :
      PIR.MonadHandler ProbComp (oracleReadInterface model.toCarriers) S E)
    (ordinaryLaw : ∀ operation state,
      SameDist (ordinaryLeft operation state) (ordinaryRight operation state))
    (baseLaw : ∀ request state, SameDist (baseLeft request state) (baseRight request state))
    (process : PIR.Process (OracleProtocol.Interface model) A)
    (state : OracleProtocol.State model snapshot domains math S) :
    SameDist (OracleProcess.runM model oracles ordinaryLeft baseLeft process state)
      (OracleProcess.runM model oracles ordinaryRight baseRight process state) := by
  apply execute_sameDist
  intro request current
  cases request with
  | inl operation => exact ordinaryLaw operation current
  | inr request => exact baseLaw request current

/-- The same replacement law starts at the actual admitted source and its installed inputs.
It preserves the complete root execution, not only acceptance or decoded reply marginals. -/
theorem source_sameDist {subject : OracleSubject snapshot} {self : Nat}
    (start : OracleStart subject model self S)
    (ordinaryLeft ordinaryRight :
      PIR.MonadHandler ProbComp (participantInterfaceOn model.toCarriers) S E)
    (baseLeft baseRight :
      PIR.MonadHandler ProbComp (oracleReadInterface model.toCarriers) S E)
    (ordinaryLaw : ∀ operation state,
      SameDist (ordinaryLeft operation state) (ordinaryRight operation state))
    (baseLaw : ∀ request state, SameDist (baseLeft request state) (baseRight request state)) :
    SameDist (OracleProcess.sourceRunM start ordinaryLeft baseLeft)
      (OracleProcess.sourceRunM start ordinaryRight baseRight) :=
  protocol_sameDist subject.unit.oracles ordinaryLeft ordinaryRight baseLeft baseRight
    ordinaryLaw baseLaw _ start.state

/-- Local complete-action couplings reuse the generic Process theorem even when provider
states or audit events have different representations. No whole-source coupling is assumed. -/
theorem protocol_relTriple {T F O : Type}
    (oracles : List (CheckedOracle snapshot domains math))
    (ordinaryLeft : PIR.MonadHandler ProbComp (participantInterfaceOn model.toCarriers) S E)
    (ordinaryRight : PIR.MonadHandler ProbComp (participantInterfaceOn model.toCarriers) T F)
    (baseLeft : PIR.MonadHandler ProbComp (oracleReadInterface model.toCarriers) S E)
    (baseRight : PIR.MonadHandler ProbComp (oracleReadInterface model.toCarriers) T F)
    (relation : OracleProtocol.State model snapshot domains math S →
      OracleProtocol.State model snapshot domains math T → Prop)
    (left : OracleProtocol.Event E → List O) (right : OracleProtocol.Event F → List O)
    (localLaw : ∀ operation s t, relation s t →
      OracleComp.ProgramLogic.Relational.RelTriple
        (OracleProcess.actionM model oracles ordinaryLeft baseLeft operation s)
        (OracleProcess.actionM model oracles ordinaryRight baseRight operation t)
        (PIR.Related relation left right))
    (process : PIR.Process (OracleProtocol.Interface model) A)
    (s : OracleProtocol.State model snapshot domains math S)
    (t : OracleProtocol.State model snapshot domains math T) (initial : relation s t) :
    OracleComp.ProgramLogic.Relational.RelTriple
      (OracleProcess.runM model oracles ordinaryLeft baseLeft process s)
      (OracleProcess.runM model oracles ordinaryRight baseRight process t)
      (PIR.Related relation left right) := by
  rw [OracleProcess.runM_actions, OracleProcess.runM_actions]
  exact Coupling.runM_relTriple relation left right _ _ localLaw process s t initial

/-- The relational interface is pinned to one admitted source and equal installed inputs.
The provider states, event representations and residual-state invariant may differ. -/
theorem source_relTriple {subject : OracleSubject snapshot} {self : Nat} {T F O : Type}
    (leftStart : OracleStart subject model self S)
    (rightStart : OracleStart subject model self T)
    (inputs : leftStart.installed.inputs = rightStart.installed.inputs)
    (ordinaryLeft : PIR.MonadHandler ProbComp (participantInterfaceOn model.toCarriers) S E)
    (ordinaryRight : PIR.MonadHandler ProbComp (participantInterfaceOn model.toCarriers) T F)
    (baseLeft : PIR.MonadHandler ProbComp (oracleReadInterface model.toCarriers) S E)
    (baseRight : PIR.MonadHandler ProbComp (oracleReadInterface model.toCarriers) T F)
    (relation : OracleProtocol.State model subject.unit.snapshot subject.unit.domains
        subject.unit.math S →
      OracleProtocol.State model subject.unit.snapshot subject.unit.domains subject.unit.math T →
        Prop)
    (left : OracleProtocol.Event E → List O) (right : OracleProtocol.Event F → List O)
    (localLaw : ∀ operation s t, relation s t →
      OracleComp.ProgramLogic.Relational.RelTriple
        (OracleProcess.actionM model subject.unit.oracles ordinaryLeft baseLeft operation s)
        (OracleProcess.actionM model subject.unit.oracles ordinaryRight baseRight operation t)
        (PIR.Related relation left right))
    (initial : relation leftStart.state rightStart.state) :
    OracleComp.ProgramLogic.Relational.RelTriple
      (OracleProcess.sourceRunM leftStart ordinaryLeft baseLeft)
      (OracleProcess.sourceRunM rightStart ordinaryRight baseRight)
      (PIR.Related relation left right) := by
  unfold OracleProcess.sourceRunM
  rw [inputs]
  exact protocol_relTriple subject.unit.oracles ordinaryLeft ordinaryRight baseLeft baseRight
    relation left right localLaw _ _ _ initial

end ZkcSecurity.VCVio.OracleSource
