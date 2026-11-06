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

theorem sequenceEmptyAt {self maximum : Nat} {roles : Nat → Nat} {owners : List Nat} {kind : OracleKind}
    (role : original.self = self) (active : self ∈ owners.map roles) (limit : maximum < indexLimit) :
    Keeps oracles ordinary base publish original
      (.call (.oracle ⟨.sequenceEmpty kind maximum owners, location, self, roles, .nil⟩) .done)
      (.cons (some (ProtocolValue.ofConcrete (.oracleSequence kind maximum) [])) .nil) := by
  apply fromCursor (location := location)
  intro state same
  exact OraclePublication.sequenceEmpty oracles ordinary base publish kind maximum owners roles location state
    self ((same ▸ role).symm) ((same ▸ role) ▸ active) limit

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

/-- A returned active append has the original sequence followed by the
supplied handle. Capacity, visibility and the source cursor can each stop
the execution. All of these outcomes preserve the oracle state. -/
theorem sequenceAppendAction {self maximum : Nat} {roles : Nat → Nat} {owners : List Nat}
    {kind : OracleKind} {anchors : List OracleAnchor} {anchor : OracleAnchor}
    (role : original.self = self) (active : self ∈ owners.map roles)
    (state : OracleProtocol.State model snapshot domains math S) (same : state.oracle = original) :
    let op : OracleProtocolAction model.toCarriers := .oracle ⟨.sequenceAppend kind maximum owners, location,
      self, roles, .cons (some (ProtocolValue.ofConcrete (.oracleSequence kind maximum) anchors))
        (.cons (some (ProtocolValue.ofConcrete (.oracle kind) anchor)) .nil)⟩
    let expected : (OracleProtocol.Interface model).Reply op :=
      .cons (some (ProtocolValue.ofConcrete (.oracleSequence kind maximum) (anchors ++ [anchor]))) .nil
    Std.Do.Internal.Ensures (fun record ↦ record.state.oracle = original ∧
      ∀ value, record.outcome = .returned value → value = expected)
      (OraclePublication.actionM model oracles ordinary base publish op state) := by
  dsimp only
  rw [OraclePublication.actionM_local _ _ _ _ _ _ rfl]
  apply Zkc.MonadicPostcondition.pure
  simp only [OracleProtocol.handler]
  split
  · exact ⟨same, by intro _ eq; cases eq⟩
  · simp [OracleExecution.operation, same, role, active, ProtocolValue.toConcrete_ofConcrete,
      OracleExecution.refusal, OracleExecution.returned]
    split <;> first | split <;> simp_all | simp_all
    exact fun _ eq ↦ (PIR.Outcome.returned.inj eq).symm

theorem sequenceAppendReturned {self maximum : Nat} {roles : Nat → Nat} {owners : List Nat}
    {kind : OracleKind} {anchors : List OracleAnchor} {anchor : OracleAnchor}
    (role : original.self = self) (active : self ∈ owners.map roles) :
    Keeps oracles ordinary base publish original
      (.call (.oracle ⟨.sequenceAppend kind maximum owners, location, self, roles,
        .cons (some (ProtocolValue.ofConcrete (.oracleSequence kind maximum) anchors))
          (.cons (some (ProtocolValue.ofConcrete (.oracle kind) anchor)) .nil)⟩) .done)
      (.cons (some (ProtocolValue.ofConcrete (.oracleSequence kind maximum) (anchors ++ [anchor]))) .nil) := by
  apply PIR.Process.ReturnsUnder.action
  exact sequenceAppendAction role active

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
