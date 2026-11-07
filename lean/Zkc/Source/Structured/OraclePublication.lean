module

public import Zkc.Source.Structured.OracleProcessTotal

@[expose] public section

/-! An explicit causal publication profile on the original source action signature.

The existing handler owns every validation and its order. Its send result is a candidate:
only a returned present base table reaches publication. Provider events precede successful
logical delivery. A stopped publication retains the old logical state and its own provider
poststate/events. Source coordinates identify requests; they are not authentication premises.
No word immutability, sampling law, or cryptographic realization is asserted here.
-/

set_option autoImplicit false
namespace Zkc.Source.Structured.OraclePublication

/-- Original kind, complete construction identity, and the actual optional holder payload. -/
structure Request (model : DomainModel) where
  kind : OracleKind
  anchor : OracleAnchor
  rows : Nat
  holder : Nat
  receivers : List Nat
  location : OracleLocation
  holderData : Option (List (model.Value kind.answer))

abbrev Interface (model : DomainModel) : PIR.Signature where
  Op := Request model
  Reply _ := Unit

variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment} {S E A : Type}

/-- Inspect the existing result, without rechecking or reordering source-owned validation.
The current frame supplies the reached invocation, as in the original action handler. -/
def request? (action : OracleProtocolAction model.toCarriers)
    (before : OracleProtocol.State model snapshot domains math S)
    (candidate : PIR.Execution (OracleProtocol.State model snapshot domains math S)
      (OracleProtocol.Event E) ((OracleProtocol.Interface model).Reply action)) :
    Option (Request model) :=
  match action with
  | .oracle request =>
    match request, candidate with
    | ⟨.send kind .., location, _, _, _⟩, candidate =>
      match candidate.outcome with
      | .returned values => do
        let anchor ← (values.get .here).bind ProtocolValue.toConcrete
        let table ← OracleStore.find candidate.state.oracle.entries kind.answer anchor
        match table.payload with
        | .base data => some ⟨kind, anchor, table.rows, table.holder, table.receivers,
            {location with invocation := before.frame.invocation}, data⟩
        | .virtual .. => none
      | .stopped _ => none
    | _, _ => none
  | _ => none

/-- Validation failures, including duplicate construction, cannot reach publication. -/
theorem request?_stopped (action : OracleProtocolAction model.toCarriers)
    (before after : OracleProtocol.State model snapshot domains math S)
    (reason : PIR.Stop) (events : List (OracleProtocol.Event E)) :
    request? action before ⟨.stopped reason, after, events⟩ = none := by
  cases action <;> try rfl
  case oracle request =>
    cases request with
    | mk operation location self roles arguments => cases operation <;> rfl

/-- A skipped send returns an absent handle, even if an older entry has the same anchor. -/
theorem request?_absent (kind : OracleKind) (holder : Nat) (receivers : List Nat)
    (bounds : List (String × Nat)) (location : OracleLocation) (self : Nat) (roles : Nat → Nat)
    (arguments : Values (Component (ProtocolValue model.toCarriers))
      (OracleOp.send kind holder receivers bounds).arguments)
    (before after : OracleProtocol.State model snapshot domains math S)
    (events : List (OracleProtocol.Event E)) :
    request? (.oracle ⟨.send kind holder receivers bounds, location, self, roles, arguments⟩)
      before ⟨.returned (.cons none .nil), after, events⟩ = none := rfl

/-- Publication events use the same provider audit injection as logical base reads. -/
def providerEvents (events : List E) : List (OracleProtocol.Event E) :=
  events.map (fun event ↦ .logical (.provider event))

/-- Commit the candidate only after publication returns; every stop discards its deliveries. -/
def complete (before : OracleProtocol.State model snapshot domains math S)
    (candidate : PIR.Execution (OracleProtocol.State model snapshot domains math S)
      (OracleProtocol.Event E) A) (publication : PIR.Execution S E Unit) :
    PIR.Execution (OracleProtocol.State model snapshot domains math S) (OracleProtocol.Event E) A :=
  match publication.outcome with
  | .returned () => ⟨candidate.outcome,
      {candidate.state with oracle.provider := publication.state},
      providerEvents publication.events ++ candidate.events⟩
  | .stopped reason => ⟨.stopped reason, {before with oracle.provider := publication.state},
      providerEvents publication.events⟩

theorem complete_stopped (before : OracleProtocol.State model snapshot domains math S)
    (candidate : PIR.Execution (OracleProtocol.State model snapshot domains math S)
      (OracleProtocol.Event E) A) (reason : PIR.Stop) (state : S) (events : List E) :
    complete before candidate ⟨.stopped reason, state, events⟩ =
      ⟨.stopped reason, {before with oracle.provider := state}, providerEvents events⟩ := rfl

theorem complete_returned (before : OracleProtocol.State model snapshot domains math S)
    (candidate : PIR.Execution (OracleProtocol.State model snapshot domains math S)
      (OracleProtocol.Event E) A) (state : S) (events : List E) :
    complete before candidate ⟨.returned (), state, events⟩ =
      ⟨candidate.outcome, {candidate.state with oracle.provider := state},
        providerEvents events ++ candidate.events⟩ := rfl

variable {m : Type → Type} [Monad m]

/-- A mathematical specialization, adding no event or provider update. -/
def noop : PIR.MonadHandler m (Interface model) S E :=
  fun _ state ↦ pure ⟨.returned (), state, []⟩

/-- Output instrumentation of one existing action. Sends have no provider effect before
this boundary, so the candidate's provider is the actual publication prestate. -/
def afterM (publish : PIR.MonadHandler m (Interface model) S E)
    (action : OracleProtocolAction model.toCarriers)
    (before : OracleProtocol.State model snapshot domains math S)
    (candidate : PIR.Execution (OracleProtocol.State model snapshot domains math S)
      (OracleProtocol.Event E) ((OracleProtocol.Interface model).Reply action)) := do
  match request? action before candidate with
  | none => pure candidate
  | some request =>
    let publication ← publish request candidate.state.oracle.provider
    pure (complete before candidate publication)

variable [LawfulMonad m]

set_option smartUnfolding false in
/-- The existing send action is local, even when the external handlers are monadic. -/
theorem send_actionM (model : DomainModel)
    (oracles : List (CheckedOracle snapshot domains math))
    (ordinary : PIR.MonadHandler m (participantInterfaceOn model.toCarriers) S E)
    (base : PIR.MonadHandler m (oracleReadInterface model.toCarriers) S E)
    (kind : OracleKind) (holder : Nat) (receivers : List Nat) (bounds : List (String × Nat))
    (location : OracleLocation) (self : Nat) (roles : Nat → Nat)
    (arguments : Values (Component (ProtocolValue model.toCarriers))
      (OracleOp.send kind holder receivers bounds).arguments)
    (state : OracleProtocol.State model snapshot domains math S) :
    OracleProcess.actionM model oracles ordinary base
        (.oracle ⟨.send kind holder receivers bounds, location, self, roles, arguments⟩) state =
      pure (OracleProtocol.handler model oracles OracleProcess.refusingOrdinary
        OracleProcess.refusingBase
        (.oracle ⟨.send kind holder receivers bounds, location, self, roles, arguments⟩)
        state) := by
  unfold OracleProcess.actionM
  simp only [OracleProcess.action, OracleProtocol.handler]
  split
  · rw [OracleProcess.executeM_done]
  · cases kind
    exact OracleProcess.executeM_done _ _ _

/-- Every validation path of the original send preserves the provider prestate. -/
theorem send_provider (model : DomainModel)
    (oracles : List (CheckedOracle snapshot domains math))
    (base : PIR.Handler (oracleReadInterface model.toCarriers) S E)
    (kind : OracleKind) (holder : Nat) (receivers : List Nat) (bounds : List (String × Nat))
    (location : OracleLocation) (self : Nat) (roles : Nat → Nat)
    (arguments : Values (Component (ProtocolValue model.toCarriers))
      (OracleOp.send kind holder receivers bounds).arguments)
    (state : OracleRuntimeState model snapshot domains math S) :
    (OracleExecution.operation model oracles base location self roles
      (.send kind holder receivers bounds) arguments state).state.provider = state.provider := by
  cases kind with
  | table row fixed =>
    change Values (Component (ProtocolValue model.toCarriers))
      [(OracleKind.table row fixed).data, .index] at arguments
    cases arguments with
    | cons data rest =>
      cases rest with
      | cons dimension rest =>
        cases rest
        dsimp only [OracleExecution.operation, OracleOp.results]
        repeat' (split <;> try dsimp only [OracleExecution.returned, OracleExecution.refusal])

/-- The candidate provider passed to publication is the actual pre-action provider state. -/
theorem send_actionM_prestate (model : DomainModel)
    (oracles : List (CheckedOracle snapshot domains math))
    (ordinary : PIR.MonadHandler m (participantInterfaceOn model.toCarriers) S E)
    (base : PIR.MonadHandler m (oracleReadInterface model.toCarriers) S E)
    (kind : OracleKind) (holder : Nat) (receivers : List Nat) (bounds : List (String × Nat))
    (location : OracleLocation) (self : Nat) (roles : Nat → Nat)
    (arguments : Values (Component (ProtocolValue model.toCarriers))
      (OracleOp.send kind holder receivers bounds).arguments)
    (state : OracleProtocol.State model snapshot domains math S) :
    (OracleProcess.actionM model oracles ordinary base
        (.oracle ⟨.send kind holder receivers bounds, location, self, roles, arguments⟩) state >>=
      fun candidate ↦ pure candidate.state.oracle.provider) = pure state.oracle.provider := by
  rw [send_actionM]
  simp only [pure_bind, OracleProtocol.handler]
  split
  · rfl
  · exact congrArg pure (send_provider model oracles OracleProcess.refusingBase
      kind holder receivers bounds _ self roles arguments state.oracle)

/-- All action semantics, including every non-send arm, come from the original handler. -/
def actionM (model : DomainModel) (oracles : List (CheckedOracle snapshot domains math))
    (ordinary : PIR.MonadHandler m (participantInterfaceOn model.toCarriers) S E)
    (base : PIR.MonadHandler m (oracleReadInterface model.toCarriers) S E)
    (publish : PIR.MonadHandler m (Interface model) S E) :
    PIR.MonadHandler m (OracleProtocol.Interface model)
      (OracleProtocol.State model snapshot domains math S) (OracleProtocol.Event E) :=
  fun action state ↦ do
    let candidate ← OracleProcess.actionM model oracles ordinary base action state
    afterM publish action state candidate

/-- The same original Process, under an explicit publication profile. -/
def runM (model : DomainModel) (oracles : List (CheckedOracle snapshot domains math))
    (ordinary : PIR.MonadHandler m (participantInterfaceOn model.toCarriers) S E)
    (base : PIR.MonadHandler m (oracleReadInterface model.toCarriers) S E)
    (publish : PIR.MonadHandler m (Interface model) S E)
    (process : PIR.Process (OracleProtocol.Interface model) A)
    (state : OracleProtocol.State model snapshot domains math S) :=
  process.runM (actionM model oracles ordinary base publish) state

/-- A publication stop forbids every suffix, including later draws and reads. -/
theorem runM_call_stopped (model : DomainModel)
    (oracles : List (CheckedOracle snapshot domains math))
    (ordinary : PIR.MonadHandler m (participantInterfaceOn model.toCarriers) S E)
    (base : PIR.MonadHandler m (oracleReadInterface model.toCarriers) S E)
    (publish : PIR.MonadHandler m (Interface model) S E)
    (action : (OracleProtocol.Interface model).Op)
    (next : (OracleProtocol.Interface model).Reply action →
      PIR.Process (OracleProtocol.Interface model) A)
    (before after : OracleProtocol.State model snapshot domains math S)
    (reason : PIR.Stop) (events : List (OracleProtocol.Event E))
    (stopped : actionM model oracles ordinary base publish action before =
      pure ⟨.stopped reason, after, events⟩) :
    runM model oracles ordinary base publish (.call action next) before =
      pure ⟨.stopped reason, after, events⟩ := by
  simp [runM, PIR.Process.runM, stopped, PIR.Execution.followM]

/-- Checked source association and ingress are retained from the existing source API. -/
def sourceRunM {subject : OracleSubject snapshot} {self : Nat}
    (start : OracleStart subject model self S)
    (ordinary : PIR.MonadHandler m (participantInterfaceOn model.toCarriers) S E)
    (base : PIR.MonadHandler m (oracleReadInterface model.toCarriers) S E)
    (publish : PIR.MonadHandler m (Interface model) S E) :=
  runM model subject.unit.oracles ordinary base publish
    (subject.imported.program.oracleParticipant model self start.installed.inputs) start.state

theorem afterM_noop (action : OracleProtocolAction model.toCarriers)
    (before : OracleProtocol.State model snapshot domains math S)
    (candidate : PIR.Execution (OracleProtocol.State model snapshot domains math S)
      (OracleProtocol.Event E) ((OracleProtocol.Interface model).Reply action)) :
    afterM (noop (m := m)) action before candidate = pure candidate := by
  unfold afterM
  split
  · simp
  · simp [noop, complete, providerEvents]

theorem actionM_noop (model : DomainModel)
    (oracles : List (CheckedOracle snapshot domains math))
    (ordinary : PIR.MonadHandler m (participantInterfaceOn model.toCarriers) S E)
    (base : PIR.MonadHandler m (oracleReadInterface model.toCarriers) S E) :
    actionM model oracles ordinary base noop =
      OracleProcess.actionM model oracles ordinary base := by
  funext action state
  simp [actionM, afterM_noop]

/-- Equality of the complete monadic record, for every stop, state, cursor, stack and event. -/
theorem runM_noop (model : DomainModel)
    (oracles : List (CheckedOracle snapshot domains math))
    (ordinary : PIR.MonadHandler m (participantInterfaceOn model.toCarriers) S E)
    (base : PIR.MonadHandler m (oracleReadInterface model.toCarriers) S E)
    (process : PIR.Process (OracleProtocol.Interface model) A)
    (state : OracleProtocol.State model snapshot domains math S) :
    runM model oracles ordinary base noop process state =
      OracleProcess.runM model oracles ordinary base process state := by
  rw [runM, actionM_noop, OracleProcess.runM_actions]

theorem sourceRunM_noop {subject : OracleSubject snapshot} {self : Nat}
    (start : OracleStart subject model self S)
    (ordinary : PIR.MonadHandler m (participantInterfaceOn model.toCarriers) S E)
    (base : PIR.MonadHandler m (oracleReadInterface model.toCarriers) S E) :
    sourceRunM start ordinary base noop = OracleProcess.sourceRunM start ordinary base :=
  runM_noop model subject.unit.oracles ordinary base _ start.state

/-- A nonpublication result leaves the original execution intact and calls no provider. -/
theorem afterM_none (publish : PIR.MonadHandler m (Interface model) S E)
    (action : OracleProtocolAction model.toCarriers)
    (before : OracleProtocol.State model snapshot domains math S)
    (candidate : PIR.Execution (OracleProtocol.State model snapshot domains math S)
      (OracleProtocol.Event E) ((OracleProtocol.Interface model).Reply action))
    (absent : request? action before candidate = none) :
    afterM publish action before candidate = pure candidate := by
  simp [afterM, absent]

/-- A source refusal before publication returns its original record. The
chooser cannot observe a failed construction or change its state. -/
theorem send_stopped (model : DomainModel) (oracles : List (CheckedOracle snapshot domains math))
    (ordinary : PIR.MonadHandler m (participantInterfaceOn model.toCarriers) S E)
    (base : PIR.MonadHandler m (oracleReadInterface model.toCarriers) S E)
    (publish : PIR.MonadHandler m (Interface model) S E)
    (kind : OracleKind) (holder : Nat) (receivers : List Nat) (bounds : List (String × Nat))
    (site : OracleLocation) (self : Nat) (roles : Nat → Nat)
    (args : Values (Component (ProtocolValue model.toCarriers)) (OracleOp.send kind holder receivers bounds).arguments)
    (state : OracleProtocol.State model snapshot domains math S) (why : PIR.Stop) :
    let action : OracleProtocolAction model.toCarriers :=
      .oracle ⟨.send kind holder receivers bounds, site, self, roles, args⟩
    let candidate := OracleProtocol.handler model oracles OracleProcess.refusingOrdinary
      (OracleProcess.refusingBase (E := E)) action state
    candidate.outcome = .stopped why → actionM model oracles ordinary base publish action state = pure candidate := by
  intro action candidate stopped
  unfold actionM
  rw [send_actionM, pure_bind]
  change afterM publish action state candidate = pure candidate
  apply afterM_none
  cases equation : candidate with
  | mk outcome after events =>
    rw [equation] at stopped
    dsimp only at stopped
    subst outcome
    exact request?_stopped action state after why events

/-- Exactly one provider call, with the complete result determining the committed record. -/
theorem afterM_some (publish : PIR.MonadHandler m (Interface model) S E)
    (action : OracleProtocolAction model.toCarriers)
    (before : OracleProtocol.State model snapshot domains math S)
    (candidate : PIR.Execution (OracleProtocol.State model snapshot domains math S)
      (OracleProtocol.Event E) ((OracleProtocol.Interface model).Reply action))
    (request : Request model) (present : request? action before candidate = some request) :
    afterM publish action before candidate =
      (publish request candidate.state.oracle.provider >>= fun publication ↦
        pure (complete before candidate publication)) := by
  simp [afterM, present]

end Zkc.Source.Structured.OraclePublication
