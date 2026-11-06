module

public import ZkcExamples.Structured.FriCommitTerminal
public import Zkc.Source.RegionReturnProjection
public import Zkc.Source.Structured.ReceiverMetadata
public meta import Zkc.Source.RegionReturnProjection

@[expose] public section

/-! Interpret the receiver's terminal vector at its actual source uses.
Exhausted vector length, a false singleton guard, or a refused metadata
operation prevents a return. -/
set_option autoImplicit false
namespace ZkcExamples.Structured.FriCommitReply
open Zkc.Source Zkc.Source.Structured
open FriSource FriSourceBodies FriSourceViews FriCommitTerminal FriBinding
open OracleProtocol (concrete)
attribute [local implicit_reducible] Op.arguments Op.results Op.regions ProtocolOp.arguments ProtocolOp.results ProtocolOp.regions

variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec} {math : OracleMathEnvironment}
  {M : Type → Type} [Monad M] [LawfulMonad M] {S E : Type}
  (oracles : List (CheckedOracle snapshot domains math))
  (ordinary : PIR.MonadHandler M (participantInterfaceOn model.toCarriers) S E)
  (base : PIR.MonadHandler M (oracleReadInterface model.toCarriers) S E)
  (publish : PIR.MonadHandler M (OraclePublication.Interface model) S E)
  (original : OracleRuntimeState model snapshot domains math S)

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1600000 in
theorem installed (context : ProtocolContext) (receiver : context.roles 1 = 1) (separate : 1 ≠ context.roles 0)
    (role : original.self = 1) (live : Values (Value model) delivery.context)
    (initial : OracleAnchor) (later folds : List OracleAnchor) (shift : model.Field extension)
    (layers : live.get layersPort = concrete model layersSort.type (initial :: later))
    (views : live.get foldsPort = concrete model layersSort.type folds)
    (offset : live.get shiftPort = concrete model (.field extension) shift)
    (rows : live.get rowsPort = concrete model .index 32) (count : live.get countPort = concrete model .index 3)
    (cs : List (model.Field extension)) :
    Region.ReturnsSatisfying (OraclePublication.actionM model oracles ordinary base publish)
      (fun state ↦ state.oracle = original) ((verifierAlgebra model).meaning (verifierTable model) context 1)
      FriCommitTerminal.finish ((Values.cons (Value := Value model) (ty := .vector extension)
        (concrete model (.vector extension) cs) .nil).append live).get
      (fun out ↦ cs.length = 1 ∧ out = FriCommitTerminal.output model initial (initial :: later) folds shift cs) := by
  have size := FriIndexCollections.coefficientLength model cs
  have lengthCall (site : String) :
      ((verifierAlgebra model).meaning (verifierTable model) context 1).operation (.localCall helper0Helper rfl 1 site)
        (.cons (concrete model (.vector extension) cs) .nil) .nil =
        (if cs.length < indexLimit then .done (.cons (concrete model .index cs.length) .nil) else .halt .exhausted) := by
    change OracleProtocol.owned model 1 (context.roles 1) (FriIndexCollections.helpers model) helper0Helper
      (.cons (concrete model (.vector extension) cs) .nil) = _
    rw [receiver]
    exact size
  have passing (one : cs.length = 1) (site : String) :
      ((verifierAlgebra model).meaning (verifierTable model) context 1).operation (.guard 1 site)
        (.cons (concrete model .boolean (decide (cs.length = 1))) .nil) .nil = .done .nil := by
    rw [decide_eq_true one]
    change ((Participant.guard (services := services) (Value := model.Value) 1 (context.roles 1)
      ((concrete model .boolean true).bind ProtocolValue.toConcrete)).interpret (OracleProtocol.actions model)).bind _ = _
    simp [OracleProtocol.concrete, Participant.guard, PIR.Process.interpret, PIR.Process.bind]
  have picked {location : OracleLocation} : ReceiverForwarding.Keeps oracles ordinary base publish original
      (.call (.oracle ⟨.sequenceAt FriCommitRound.kind 3 [0,1], location, 1, context.roles,
        .cons (live.get layersPort) (.cons (concrete model .index 0) .nil)⟩) .done)
      (.cons (concrete model initialSort.type initial) .nil) := by
    rw [layers]
    exact ReceiverForwarding.sequenceAtReturned role (by simp [receiver]) rfl
  have pair {location : OracleLocation} (sort : OracleLogicalSort) (anchors : model.Value sort.type)
      (supplied : Value model sort.type) (correct : supplied = concrete model sort.type anchors) :
      ReceiverForwarding.Keeps oracles ordinary base publish original
        (.call (.oracle ⟨.components sort 0 [1], location, 1, context.roles, .cons supplied .nil⟩) .done)
        (.cons none (.cons (concrete model sort.type anchors) .nil)) := by
    rw [correct]
    exact ReceiverForwarding.componentsAt role separate (by simp [receiver])
  by_cases fits : cs.length < indexLimit <;> by_cases one : cs.length = 1
  all_goals
    repeat' first
      | (project_step ProtocolOp.mark
         apply PIR.Process.ReturnsUnder.call
         exact ReceiverForwarding.mark oracles ordinary base publish original _ _
         apply PIR.Process.ReturnsUnder.done)
      | (project_step ProtocolOp.restrict
         exact PIR.Process.ReturnsUnder.ofEquation (OracleProtocol.restrictActive model receiver _) (.done _))
      | (project_halt ProtocolOp.localCall
         exact (lengthCall _).trans (ite_eq_right (by assumption)))
      | (project_step ProtocolOp.localCall
         exact PIR.Process.ReturnsUnder.ofEquation ((lengthCall _).trans (ite_eq_left (by assumption))) (.done _))
      | (project_step ProtocolOp.calculate [Op.indexConstant]
         apply PIR.Process.ReturnsUnder.done)
      | (project_step ProtocolOp.calculate [Op.indexEqual]
         exact PIR.Process.ReturnsUnder.ofEquation (OracleProtocol.compareIndex model cs.length 1) (.done _))
      | (project_halt ProtocolOp.guard
         apply Eq.trans _ (OracleProtocol.guardFalse model receiver)
         exact congrArg (fun flag ↦ ((verifierAlgebra model).meaning (verifierTable model) context 1).operation
           (.guard 1 _) (.cons (concrete model .boolean flag) .nil) .nil) (decide_eq_false (by assumption)))
      | (project_step ProtocolOp.guard
         exact PIR.Process.ReturnsUnder.ofEquation (passing (by assumption) _) (.done _))
      | (project_step ProtocolOp.assemble
         exact PIR.Process.ReturnsUnder.ofEquation (OracleProtocol.assembleSecond model separate.symm receiver _ _) (.done _))
      | (project_step ProtocolOp.oracle [OracleOp.sequenceAt]
         exact picked)
      | (project_step ProtocolOp.oracle [OracleOp.components]
         first | exact pair initialSort initial _ rfl | exact pair layersSort _ _ layers | exact pair layersSort _ _ views)
  all_goals
    apply Region.ReturnsSatisfying.ret
    refine ⟨one, ?_⟩
    change FriPhaseCalls.prependPairs (FriPhaseCalls.pairs none (concrete model initialSort.type initial)
      none (concrete model layersSort.type (initial :: later)) none (concrete model layersSort.type folds))
      (.cons (live.get shiftPort) (.cons (live.get rowsPort) (.cons (concrete model (.vector extension) cs)
        (.cons (live.get countPort) .nil)))) = _
    rw [offset, rows, count]
    rfl

end ZkcExamples.Structured.FriCommitReply
