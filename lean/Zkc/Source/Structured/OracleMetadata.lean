module

public import Zkc.Source.Structured.OracleLocalAction

@[expose] public section

/-! Selection and shape observe registered handles without contacting the
prover or reading their cells. The actual source frame still checks the site. -/
set_option autoImplicit false
namespace Zkc.Source.Structured.OraclePublication
variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment} {S E : Type}
  {m : Type → Type} [Monad m] [LawfulMonad m]
  (oracles : List (CheckedOracle snapshot domains math))
  (ordinary : PIR.MonadHandler m (participantInterfaceOn model.toCarriers) S E)
  (base : PIR.MonadHandler m (oracleReadInterface model.toCarriers) S E)
  (publish : PIR.MonadHandler m (Interface model) S E)

def cursorReply {A : Type} (site : OracleLocation)
    (state : OracleProtocol.State model snapshot domains math S)
    (reply : A) (post : OracleRuntimeState model snapshot domains math S)
    (trace : List (OracleProtocol.Event E)) :
    PIR.Execution (OracleProtocol.State model snapshot domains math S) (OracleProtocol.Event E) A :=
  if site.definition = state.frame.definition ∧ site.row = state.frame.row then
    ⟨.returned reply, {state with oracle := post}, trace⟩
  else ⟨.stopped .refused, state, []⟩

private theorem metadataReply (request : OracleRequest model.toCarriers)
    (closed : localAction (.oracle request) = true)
    (state : OracleProtocol.State model snapshot domains math S)
    (reply : (oracleInterface model.toCarriers).Reply request)
    (localLaw : ∀ loc, OracleExecution.operation model oracles (OracleProcess.refusingBase (E := E))
        loc request.self request.roles request.operation request.arguments state.oracle =
      ⟨.returned reply, state.oracle, []⟩) :
    actionM model oracles ordinary base publish (.oracle request) state =
      pure (cursorReply request.location state reply state.oracle []) := by
  rw [actionM_local _ _ _ _ _ _ closed]
  by_cases aligned : request.location.definition = state.frame.definition ∧ request.location.row = state.frame.row
  · simp [cursorReply, OracleProtocol.handler, aligned.1, aligned.2, localLaw]
  · simp only [cursorReply, aligned, ↓reduceIte, OracleProtocol.handler]
    split
    · rfl
    · rename_i valid
      exact False.elim (aligned (by simpa using valid))

/-- A visible, in-range sequence projects its own anchor. Capacity and
visibility are over the entire sequence, as required by the source handler. -/
theorem sequenceAt (row : Ty) (fixed : Option Nat) (maximum : Nat) (owners : List Nat)
    (roles : Nat → Nat) (site : OracleLocation)
    (state : OracleProtocol.State model snapshot domains math S)
    (self : Nat) (atSelf : self = state.oracle.self) (anchors : List OracleAnchor) (index : Fin anchors.length)
    (active : state.oracle.self ∈ owners.map roles) (fits : anchors.length ≤ maximum)
    (limit : maximum < indexLimit)
    (visible : anchors.all (OracleExecution.visibleReference state.oracle (.table row fixed)) = true) :
    let kind := OracleKind.table row fixed
    let op : OracleProtocolAction model.toCarriers := .oracle ⟨.sequenceAt kind maximum owners, site,
      self, roles, .cons (some (ProtocolValue.ofConcrete (.oracleSequence kind maximum) anchors))
        (.cons (some (ProtocolValue.ofConcrete .index index.val)) .nil)⟩
    let reply := Values.cons (some (ProtocolValue.ofConcrete (.oracle kind) anchors[index.val])) .nil
    actionM model oracles ordinary base publish op state = pure (cursorReply site state reply state.oracle []) := by
  subst self
  dsimp only
  apply metadataReply _ _ _ _ _ rfl
  intro loc
  have inside : index.val < indexLimit := lt_of_lt_of_le index.isLt (le_trans fits limit.le)
  simp [OracleExecution.operation, active, ProtocolValue.toConcrete_ofConcrete, Nat.not_lt.mpr fits,
    Nat.not_le.mpr limit, Nat.not_le.mpr inside, visible,
    OracleExecution.returned]

/-- A shape query uses the same table that is visible at this anchor.
The state and counters are unchanged at both outcomes. -/
theorem rows (row : Ty) (fixed : Option Nat) (anchor : OracleAnchor) (roles : Nat → Nat)
    (site : OracleLocation) (state : OracleProtocol.State model snapshot domains math S)
    (self : Nat) (atSelf : self = state.oracle.self) (table : OracleStoredTable model snapshot domains math row)
    (lookup : OracleStore.find state.oracle.entries row anchor = some table)
    (valid : OracleStore.validRows (.table row fixed) table.rows = true)
    (visible : OracleStore.visible state.oracle.self table.holder table.receivers = true) :
    let kind := OracleKind.table row fixed
    let op : OracleProtocolAction model.toCarriers := .oracle ⟨.shape kind "rows", site, self, roles,
      .cons (some (ProtocolValue.ofConcrete (.oracle kind) anchor)) .nil⟩
    let reply := Values.cons (some (ProtocolValue.ofConcrete .index table.rows)) .nil
    actionM model oracles ordinary base publish op state = pure (cursorReply site state reply state.oracle []) := by
  subst self
  dsimp only
  apply metadataReply _ _ _ _ _ rfl
  intro loc
  simp [OracleExecution.operation, ProtocolValue.toConcrete_ofConcrete, OracleKind.answer, lookup, valid, visible,
    OracleExecution.returned]

end Zkc.Source.Structured.OraclePublication
