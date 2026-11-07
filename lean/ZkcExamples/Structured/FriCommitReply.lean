module

public import ZkcExamples.Structured.FriCommitTerminal
public import Zkc.Source.Structured.OracleReturnConstruction
public import Zkc.Source.Structured.ReceiverMetadata
public meta import Zkc.Source.Structured.OracleReturnConstruction

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
  derive_oracle_returns [size, picked, pair, layers, views]
  refine ⟨?_, ?_⟩
  · simpa only [decide_eq_true_eq] using (by assumption : decide (cs.length = 1) = true)
  · change FriPhaseCalls.prependPairs (FriPhaseCalls.pairs none (concrete model initialSort.type initial)
      none (concrete model layersSort.type (initial :: later)) none (concrete model layersSort.type folds))
      (.cons (live.get shiftPort) (.cons (live.get rowsPort) (.cons (concrete model (.vector extension) cs)
        (.cons (live.get countPort) .nil)))) = _
    rw [offset, rows, count]
    rfl

end ZkcExamples.Structured.FriCommitReply
