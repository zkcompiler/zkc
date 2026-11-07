module

public import ZkcExamples.Structured.FriBinding
public import Zkc.Source.Structured.OracleReturnConstruction
public import Zkc.Source.Structured.ProtocolReturnSpecification
public meta import Zkc.Source.Structured.OracleReturnConstruction

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
theorem installed (context : ProtocolContext) (receiver : context.roles 1 = 1)
    (separate : 1 ≠ context.roles 0) (handles : Handles) (rest : Committed model)
    (xs : FriScalarLoop.Positions) (count : xs.length = 8) :
    ReceiverForwarding.Keeps oracles ordinary base publish original
      (invokeProtocol (verifierTable model) protocol2Signature context 1
        (inputs model (handles.attach rest) xs))
      (output (handles.attach rest) xs) := by
  have placement (ss : List (List Nat)) (used : ∀ s ∈ ss, s = [0] ∨ s = [1] ∨ s = [0, 1]) :
      ∀ s ∈ ss, (s.map context.roles).contains 1 = s.contains 1 := by
    intro s member
    rcases used s member with rfl | rfl | rfl <;> simp [receiver, separate]
  have inputMask := maskValues_mapScopes context 1 1 protocol2Signature.inputScopes
    (inputs model (handles.attach rest) xs) (placement _ (by decide +kernel))
  have outputMask := maskValues_mapScopes context 1 1 protocol2Signature.outputScopes
    (output (handles.attach rest) xs) (placement _ (by decide +kernel))
  change maskValues 1 (context.mapScopes protocol2Signature.inputScopes)
    (inputs model (handles.attach rest) xs) = inputs model (handles.attach rest) xs at inputMask
  change maskValues 1 (context.mapScopes protocol2Signature.outputScopes)
    (output (handles.attach rest) xs) = output (handles.attach rest) xs at outputMask
  rw [← outputMask]
  apply (verifierAlgebra model).invokeReturns unit.protocolsLinked protocol2Definition protocol2_member
  change Region.ReturnsSatisfying _ _
    ((verifierAlgebra model).meaning (verifierTable model) context 1) protocol2Body
    (maskValues 1 (context.mapScopes protocol2Signature.inputScopes)
      (inputs model (handles.attach rest) xs)).get _
  rw [inputMask]
  have input {location : OracleLocation} {sort : OracleLogicalSort}
      {anchors : model.Value sort.type} {bounds : List (String × Nat)} :=
    ReceiverForwarding.inputAt (oracles := oracles) (ordinary := ordinary) (base := base)
      (publish := publish) (location := location) (sort := sort) (anchors := anchors)
      (bounds := bounds) (roles := context.roles) (receivers := [1]) role separate
      (by simp [receiver])
  have components {location : OracleLocation} {sort : OracleLogicalSort}
      {anchors : model.Value sort.type} :=
    ReceiverForwarding.componentsAt (oracles := oracles) (ordinary := ordinary) (base := base)
      (publish := publish) (location := location) (sort := sort) (anchors := anchors)
      (roles := context.roles) (receivers := [1]) role separate (by simp [receiver])
  derive_oracle_returns [input, components, lengthStep model context receiver xs count,
    boundsStep model context receiver xs count]
  rfl

end ZkcExamples.Structured.FriBindingExecution
