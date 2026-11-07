module

public import ZkcExamples.Structured.FriPhaseCalls
public import Zkc.Source.Structured.ReceiverCall

@[expose] public section

/-! Receiver transfer laws for the three ordered logical handles used by
the low-degree and query callers. They use the same checked mark, input
and component operations as standalone binding. -/
set_option autoImplicit false
namespace ZkcExamples.Structured.FriPhaseCalls
open Zkc.Source Zkc.Source.Structured
open FriBinding
open OracleProtocol (concrete)
variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec} {math : OracleMathEnvironment}
  {S E : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
  {oracles : List (CheckedOracle snapshot domains math)}
  {ordinary : PIR.MonadHandler m (participantInterfaceOn model.toCarriers) S E}
  {base : PIR.MonadHandler m (oracleReadInterface model.toCarriers) S E}
  {publish : PIR.MonadHandler m (OraclePublication.Interface model) S E}
  {store : OracleRuntimeState model snapshot domains math S}
local notation "Keeps" => ReceiverForwarding.Keeps oracles ordinary base publish store

def receiverPair (model : DomainModel) (sort : OracleLogicalSort) (anchors : model.Value sort.type) : Pair model sort :=
  .cons none (.cons (concrete model sort.type anchors) .nil)

def receiverPairs (model : DomainModel) (hs : FriBindingExecution.Handles) : Pairs model :=
  ⟨receiverPair model initialSort hs.initial, receiverPair model layersSort hs.layers, receiverPair model layersSort hs.folds⟩

def receiverHandles (model : DomainModel) (hs : FriBindingExecution.Handles) : Handles model :=
  ⟨concrete model initialSort.type hs.initial, concrete model layersSort.type hs.layers, concrete model layersSort.type hs.folds⟩

variable (caller : Caller) (receiver : caller.context.roles 1 = 1) (separate : 1 ≠ caller.context.roles 0)
  (role : store.self = 1)

include receiver separate role in
private theorem oneInput (site : TransferSite) (sort : OracleLogicalSort) (anchors : model.Value sort.type) :
    Keeps (caller.input site sort (receiverPair model sort anchors)) (concrete model sort.type anchors) := by
  apply (ReceiverForwarding.marks oracles ordinary base publish store _).bind
  apply PIR.Process.ReturnsUnder.bind (a := Values.cons (Value := Value model) (concrete model sort.type anchors) .nil)
  · exact ReceiverForwarding.inputAt role separate (by simp [receiver])
  · exact PIR.Process.ReturnsUnder.done _

include receiver separate role in
private theorem oneProjection (site : TransferSite) (sort : OracleLogicalSort) (anchors : model.Value sort.type) :
    Keeps (caller.project site sort (concrete model sort.type anchors)) (receiverPair model sort anchors) := by
  apply (ReceiverForwarding.marks oracles ordinary base publish store _).bind
  exact ReceiverForwarding.componentsAt role separate (by simp [receiver])

include receiver separate role in
theorem inputsKeep (sites : Transfers) (hs : FriBindingExecution.Handles) :
    Keeps (caller.inputs sites (receiverPairs model hs)) (receiverHandles model hs) := by
  unfold Caller.inputs
  apply (oneInput caller receiver separate role sites.initial initialSort hs.initial).bind
  apply (oneInput caller receiver separate role sites.layers layersSort hs.layers).bind
  apply (oneInput caller receiver separate role sites.folds layersSort hs.folds).bind
  exact PIR.Process.ReturnsUnder.done _

include receiver separate role in
theorem projectionsKeep (sites : Transfers) (hs : FriBindingExecution.Handles) :
    Keeps (caller.projections sites (receiverHandles model hs)) (receiverPairs model hs) := by
  unfold Caller.projections
  apply (oneProjection caller receiver separate role sites.initial initialSort hs.initial).bind
  apply (oneProjection caller receiver separate role sites.layers layersSort hs.layers).bind
  apply (oneProjection caller receiver separate role sites.folds layersSort hs.folds).bind
  exact PIR.Process.ReturnsUnder.done _

variable (oracles ordinary base publish)
theorem Caller.callReturns (caller : Caller) (selected : CallSite)
    (args : Values (Value model) selected.signature.inputs) (found : (caller.callMarks selected).isSome)
    (before : OracleProtocol.State model snapshot domains math S)
    (post : Values (Value model) selected.signature.outputs → OracleRuntimeState model snapshot domains math S → Prop)
    (law : ∀ entered : OracleProtocol.State model snapshot domains math S, entered.oracle = before.oracle →
      PIR.Process.OnReturn (OraclePublication.actionM model oracles ordinary base publish) entered
        (invokeProtocol (FriSource.verifierTable model) selected.signature (selected.childContext caller.context) 1 args)
        (fun out state ↦ post out state.oracle)) :
    PIR.Process.OnReturn (OraclePublication.actionM model oracles ordinary base publish) before
      (caller.call selected args found) (fun out state ↦ post out state.oracle) :=
  ReceiverForwarding.atApplication oracles ordinary base publish before _ selected.signature selected.site _ post law

end ZkcExamples.Structured.FriPhaseCalls
