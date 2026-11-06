module

public import ZkcExamples.Structured.FriBinding
public import Zkc.Source.Structured.ReceiverForwarding

@[expose] public section

/-! The verifier binds the original ordered handles, geometry and sampled
positions. Its source cursor and trace advance through the original checks.
A missing table, a bad layout or an invalid source mark can still stop it. -/
set_option autoImplicit false
namespace ZkcExamples.Structured.FriBindingExecution
open Zkc.Source Zkc.Source.Structured
open FriSource FriSourceBodies FriBinding
open OracleProtocol (concrete)
variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment} {S E : Type}
  {m : Type → Type} [Monad m] [LawfulMonad m]
  (oracles : List (CheckedOracle snapshot domains math))
  (ordinary : PIR.MonadHandler m (participantInterfaceOn model.toCarriers) S E)
  (base : PIR.MonadHandler m (oracleReadInterface model.toCarriers) S E)
  (publish : PIR.MonadHandler m (OraclePublication.Interface model) S E)
  (original : OracleRuntimeState model snapshot domains math S)
  (role : original.self = 1)

structure Handles where
  initial : OracleAnchor
  layers : List OracleAnchor
  folds : List OracleAnchor

/-- The three public handles are concrete receiver values. Geometry, terminal
coefficients and the round count are forwarded without interpretation. -/
def Handles.attach (handles : Handles) (rest : Committed model) : Committed model :=
  {rest with
    initial := concrete model initialSort.type handles.initial
    layers := concrete model layersSort.type handles.layers
    folds := concrete model layersSort.type handles.folds}

def output (committed : Committed model) (xs : FriScalarLoop.Positions) :
    Values (Value model) protocol2Signature.outputs :=
  .cons none (.cons committed.initial (.cons none (.cons committed.layers (.cons none
    (.cons committed.folds (.cons committed.shift (.cons committed.size (.cons committed.coefficients
      (.cons (concrete model .indices (xs.map Fin.val)) (.cons committed.rounds
        (.cons (concrete model .index 8) .nil)))))))))))

private theorem marksKeep (sites : List String) :
    ReceiverForwarding.Keeps oracles ordinary base publish original (marks model sites) () := by
  induction sites with
  | nil => exact PIR.Process.ReturnsUnder.done _
  | cons name names ih =>
    exact (ReceiverForwarding.mark oracles ordinary base publish original name _).bind
      (next := fun _ ↦ marks model names) ih

include role in
private theorem inputKeep (sort : OracleLogicalSort) (row : Nat) (anchors : model.Value sort.type) :
    ReceiverForwarding.Keeps oracles ordinary base publish original
      (input model sort row (concrete model sort.type anchors)) (concrete model sort.type anchors) := by
  have head := ReceiverForwarding.input oracles ordinary base publish original (location row)
    context.roles sort 0 [1] anchors (by rw [role]; decide) (by rw [role]; decide) [("rows", 32)]
  rw [role] at head
  exact head.bind (next := fun out ↦ .done (out.get .here)) (PIR.Process.ReturnsUnder.done _)

include role in
private theorem projectKeep (sort : OracleLogicalSort) (row : Nat) (anchors : model.Value sort.type) :
    ReceiverForwarding.Keeps oracles ordinary base publish original
      (project model sort row (concrete model sort.type anchors))
      (.cons none (.cons (concrete model sort.type anchors) .nil)) := by
  have head := ReceiverForwarding.components oracles ordinary base publish original (location row)
    context.roles sort 0 [1] anchors (by rw [role]; decide) (by rw [role]; decide)
  rw [role] at head
  exact head

include role in
theorem program (handles : Handles) (rest : Committed model) (xs : FriScalarLoop.Positions) :
    ReceiverForwarding.Keeps oracles ordinary base publish original
      (FriBinding.program model (handles.attach rest) xs) (output (handles.attach rest) xs) := by
  unfold FriBinding.program
  repeat' first
    | apply PIR.Process.ReturnsUnder.bind (marksKeep oracles ordinary base publish original _)
    | apply PIR.Process.ReturnsUnder.bind (inputKeep oracles ordinary base publish original role _ _ _)
    | apply PIR.Process.ReturnsUnder.bind (projectKeep oracles ordinary base publish original role _ _ _)
  exact PIR.Process.ReturnsUnder.done _

include role in
/-- A subsequent phase may rely on these exact handles and positions at every
returned invocation under the configured publication handler. A stopped
invocation retains its original execution record. -/
theorem installed (handles : Handles) (rest : Committed model) (xs : FriScalarLoop.Positions)
    (count : xs.length = 8) :
    ReceiverForwarding.Keeps oracles ordinary base publish original
      (invokeProtocol (verifierTable model) protocol2Signature context 1
        (inputs model (handles.attach rest) xs))
      (output (handles.attach rest) xs) := by
  rw [FriBinding.installed model _ xs count]
  exact (program oracles ordinary base publish original role handles rest xs).bind
    (next := fun values ↦ .done (maskValues 1 (context.mapScopes protocol2Signature.outputScopes) values))
    (PIR.Process.ReturnsUnder.done _)

end ZkcExamples.Structured.FriBindingExecution
