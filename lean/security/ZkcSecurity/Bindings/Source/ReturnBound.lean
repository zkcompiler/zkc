module

public import Zkc.Source.Structured.ReceiverCall
public import ZkcSecurity.ProgramLogic.ReturnBound

@[expose] public section

/-! Propagate a local probability bound past checked source marks. A bad
return can only occur after the marked operation is actually reached. -/
namespace ZkcSecurity.SourceReturnBound
open Zkc.Source.Structured
variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec} {math : OracleMathEnvironment}
  {Aux E A : Type} (oracles : List (CheckedOracle snapshot domains math))
  (ordinary : PIR.MonadHandler ProbComp (participantInterfaceOn model.toCarriers) Aux E)
  (base : PIR.MonadHandler ProbComp (oracleReadInterface model.toCarriers) Aux E)
  (publish : PIR.MonadHandler ProbComp (OraclePublication.Interface model) Aux E)

local notation "State" => OracleProtocol.State model snapshot domains math Aux
local notation "action" => OraclePublication.actionM model oracles ordinary base publish

theorem marks (labels : List (String × String)) (before : State) (body : PIR.Process (OracleProtocol.Interface model) A)
    (post : A → State → Prop) (error : ENNReal)
    (atBody : ∀ current : State, current.oracle = before.oracle → ReturnBound (body.runM action current) post error) :
    ReturnBound ((OracleProtocol.withMarks labels body).runM action before) post error := by
  have split := OracleProtocol.withMarks_bind (model := model) labels (.done ()) (fun _ ↦ body)
  change ReturnBound ((OracleProtocol.withMarks labels ((PIR.Process.done ()).bind fun _ ↦ body)).runM action before) _ _
  rw [← split, PIR.runM_bind]
  have head := ReturnBound.ofLaw (run := (OracleProtocol.withMarks labels (.done ())).runM action before) (post := fun value state ↦ state.oracle = before.oracle ∧ value = ()) ((ReceiverForwarding.marks oracles ordinary base publish before.oracle labels).onReturn (initial := before) rfl)
  simpa only [zero_add] using head.bind (fun _ current kept ↦ atBody current kept.1)

theorem reached {op : (OracleProtocol.Interface model).Op}
    {after : ((OracleProtocol.Interface model).Reply op → PIR.Process (OracleProtocol.Interface model) A) → Prop}
    {body : PIR.Process (OracleProtocol.Interface model) A} (atOp : OracleProtocol.AtMarkedCall op after body)
    (before : State) (post : A → State → Prop) {step : (OracleProtocol.Interface model).Reply op → State → Prop}
    {charge later : ENNReal}
    (atAction : ∀ current : State, current.oracle = before.oracle → ReturnBound (action op current) step charge)
    (tail : ∀ next, after next → ∀ reply current, step reply current → ReturnBound ((next reply).runM action current) post later) :
    ReturnBound (body.runM action before) post (charge + later) := by
  obtain ⟨labels, next, rfl, selected⟩ := atOp
  apply marks oracles ordinary base publish labels before _ post _
  intro current same
  exact (atAction current same).bind (tail next selected)

/-- Source frame entry and exit preserve the store. Failures at either
boundary suppress the continuation. -/
theorem withinFrame (before : State) (op : (OracleProtocol.Interface model).Op)
    (enter : ReceiverForwarding.Keeps oracles ordinary base publish before.oracle
      (.call op (fun _ ↦ .done ())) ())
    (body : PIR.Process (OracleProtocol.Interface model) A)
    (post : A → OracleRuntimeState model snapshot domains math Aux → Prop) (error : ENNReal)
    (atBody : ∀ current : State, current.oracle = before.oracle →
      ReturnBound (body.runM action current) (fun a s ↦ post a s.oracle) error) :
    ReturnBound ((OracleProtocol.enter model op body).runM action before)
      (fun a s ↦ post a s.oracle) error := by
  apply ReturnBound.afterExact (head := enter.onReturn rfl)
  intro _ entered kept
  apply ReturnBound.beforeExact (head := atBody entered kept.1)
  intro a current valid
  apply PIR.Process.OnReturn.bind (first := PIR.Process.call (I := OracleProtocol.Interface model) .leave .done) (next := fun _ ↦ .done a)
    (head := (ReceiverForwarding.leaveCall oracles ordinary base publish current.oracle).onReturn rfl)
  intro _ final left
  exact PIR.Process.OnReturn.done (left.1 ▸ valid)

theorem application (before : State) (labels : List (String × String)) (signature : ProtocolSignature) (site : String)
    (body : PIR.Process (OracleProtocol.Interface model) A)
    (post : A → OracleRuntimeState model snapshot domains math Aux → Prop) (error : ENNReal)
    (atBody : ∀ current : State, current.oracle = before.oracle →
      ReturnBound (body.runM action current) (fun a s ↦ post a s.oracle) error) :
    ReturnBound (((OracleProtocol.withMarks labels (.done ())).bind fun _ ↦
      OracleProtocol.enter model (.application signature site) body).runM action before) (fun a s ↦ post a s.oracle) error := by
  apply ReturnBound.afterExact (head := (ReceiverForwarding.marks oracles ordinary base publish before.oracle labels).onReturn rfl)
  intro _ marked kept
  exact withinFrame oracles ordinary base publish marked _ (ReceiverForwarding.enterCall _ _ _ _ _ _ _) body post error
    (fun entered same ↦ atBody entered (same.trans kept.1))

end ZkcSecurity.SourceReturnBound
