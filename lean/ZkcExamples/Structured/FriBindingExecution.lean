module

public import ZkcExamples.Structured.FriBinding
public import Zkc.Source.Structured.DeriveReceiver

@[expose] public section

/-! The verifier binds the original ordered handles, geometry and sampled
positions. Its source cursor and trace advance through the original checks.
A missing table, a bad layout or an invalid source mark can still stop it. -/
set_option autoImplicit false
namespace ZkcExamples.Structured.FriBindingExecution
open Zkc.Source Zkc.Source.Structured
open FriSource FriSourceBodies FriSourceViews FriBinding
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

set_option maxHeartbeats 2000000 in
include role in
/-- One theorem for every qualified call of the admitted binding component.
The generic derivation obtains mark locations, receiver operations and SSA
results from the selected body. The named field plan fixes the correspondence. -/
theorem installed (parent : Option String) (handles : Handles) (rest : Committed model)
    (xs : FriScalarLoop.Positions) (count : xs.length = 8) :
    ReceiverForwarding.Keeps oracles ordinary base publish original
      (invokeProtocol (verifierTable model) protocol2Signature (frame parent) 1
        (inputs model (handles.attach rest) xs))
      (output (handles.attach rest) xs) := by
  refine PIR.Process.ReturnsUnder.ofEquation
    ((verifierAlgebra model).invokePresented unit.protocolsLinked protocol2Definition protocol2_member
      (frame parent) 1 _ _ (presentation model parent (handles.attach rest) xs count).property) ?_
  apply PIR.Process.ReturnsUnder.bind (a := output (handles.attach rest) xs)
  · derive_receiver_returns oracles ordinary base publish original role
  · exact PIR.Process.ReturnsUnder.done _

end ZkcExamples.Structured.FriBindingExecution
