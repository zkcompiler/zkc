module

public import Zkc.Source.Structured.DeriveReceiver
public import Zkc.Source.Structured.OracleMetadata

@[expose] public section

/-! Return laws for receiver-side metadata in the publication interpreter.
Visibility and registry lookup are required precisely at operations that
inspect a registered table. A cursor refusal remains observable. -/
set_option autoImplicit false
namespace Zkc.Source.Structured.ReceiverForwarding
variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment} {S E : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
  {oracles : List (CheckedOracle snapshot domains math)}
  {ordinary : PIR.MonadHandler m (participantInterfaceOn model.toCarriers) S E}
  {base : PIR.MonadHandler m (oracleReadInterface model.toCarriers) S E}
  {publish : PIR.MonadHandler m (OraclePublication.Interface model) S E}
  {original : OracleRuntimeState model snapshot domains math S} {location : OracleLocation}

private theorem fromCursor {request : OracleRequest model.toCarriers}
    {value : (oracleInterface model.toCarriers).Reply request}
    (law : ∀ state : OracleProtocol.State model snapshot domains math S, state.oracle = original →
      OraclePublication.actionM model oracles ordinary base publish (.oracle request) state =
        pure (OraclePublication.cursorReply location state value state.oracle [])) :
    Keeps oracles ordinary base publish original (.call (.oracle request) .done) value := by
  apply PIR.Process.ReturnsUnder.action
  intro state same
  rw [law state same]
  apply Zkc.MonadicPostcondition.pure
  unfold OraclePublication.cursorReply
  split
  · exact ⟨same, fun _ eq ↦ (PIR.Outcome.returned.inj eq).symm⟩
  · exact ⟨same, by intro _ eq; cases eq⟩

theorem sequenceLengthAt {self maximum : Nat} {roles : Nat → Nat} {kind : OracleKind} {anchors : List OracleAnchor}
    (role : original.self = self) (fits : anchors.length ≤ maximum) (limit : maximum < indexLimit) :
    Keeps oracles ordinary base publish original
      (.call (.oracle ⟨.sequenceLength kind maximum, location, self, roles,
        .cons (some (ProtocolValue.ofConcrete (.oracleSequence kind maximum) anchors)) .nil⟩) .done)
      (.cons (some (ProtocolValue.ofConcrete .index anchors.length)) .nil) := by
  apply fromCursor (location := location)
  intro state same
  exact OraclePublication.sequenceLength oracles ordinary base publish kind maximum roles location state self
    ((same ▸ role).symm) anchors fits limit

theorem rowsAt {self : Nat} {roles : Nat → Nat} {row : Ty} {fixed : Option Nat} {anchor : OracleAnchor}
    {table : OracleStoredTable model snapshot domains math row} (role : original.self = self)
    (lookup : OracleStore.find original.entries row anchor = some table)
    (valid : OracleStore.validRows (.table row fixed) table.rows = true)
    (visible : OracleStore.visible original.self table.holder table.receivers = true) :
    Keeps oracles ordinary base publish original
      (.call (.oracle ⟨.shape (.table row fixed) "rows", location, self, roles,
        .cons (some (ProtocolValue.ofConcrete (.oracle (.table row fixed)) anchor)) .nil⟩) .done)
      (.cons (some (ProtocolValue.ofConcrete .index table.rows)) .nil) := by
  apply fromCursor (location := location)
  intro state same
  exact OraclePublication.rows oracles ordinary base publish row fixed anchor roles location state self
    ((same ▸ role).symm) table (same ▸ lookup) valid (same ▸ visible)

end Zkc.Source.Structured.ReceiverForwarding
