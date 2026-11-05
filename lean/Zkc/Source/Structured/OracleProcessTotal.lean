module

public import Zkc.Source.Structured.OracleProcessSource
public import Zkc.Source.Structured.OracleProcessLaws

@[expose] public section

/-! Outer totality for every source presentation, including all stopped inner executions.
No handler losslessness, honest-reply or source-success hypothesis is used.
-/

set_option autoImplicit false
namespace Zkc.Source.Structured.OracleProcess
variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment} {S E A : Type}

theorem answer_nonStopping (model : DomainModel) (self : Nat)
    (entries : OracleEntries model snapshot domains math) (request : OracleRead) (state : S × Nat) :
    NonStopping (answer (E := E) model self entries request state) := by
  induction entries generalizing request state with
  | nil => trivial
  | cons entry older ih =>
    rcases entry with ⟨row, table⟩
    simp only [answer]
    split
    · split
      · split
        · trivial
        · cases table.payload with
          | base data => exact nonStopping_map _ _ (fun _ ↦ trivial)
          | virtual checked answerType captures =>
            dsimp only
            split
            · apply nonStopping_map
              apply nonStopping_present
              intro child current
              exact ih _ current
            · trivial
      · exact ih request state
    · exact ih request state

theorem read_nonStopping (model : DomainModel) (request : OracleRead)
    (state : OracleRuntimeState model snapshot domains math S) :
    NonStopping (read (E := E) model request state) :=
  nonStopping_map _ _ (answer_nonStopping model state.self state.entries request _)

theorem query_nonStopping (model : DomainModel) (location : OracleLocation)
    (self : Nat) (roles : Nat → Nat) (kind : OracleKind) (owner : Nat)
    (handle : Component (ProtocolValue model.toCarriers) (.oracle kind))
    (position : Component (ProtocolValue model.toCarriers) kind.query)
    (state : OracleRuntimeState model snapshot domains math S) :
    NonStopping (query (E := E) model location self roles kind owner handle position state) := by
  unfold query
  split
  · trivial
  · split
    · trivial
    · split
      · exact nonStopping_map _ _ (read_nonStopping model _ state)
      · trivial

set_option smartUnfolding false in
theorem operation_nonStopping (model : DomainModel)
    (oracles : List (CheckedOracle snapshot domains math))
    (location : OracleLocation) (self : Nat) (roles : Nat → Nat) (op : OracleOp)
    (arguments : Values (Component (ProtocolValue model.toCarriers)) op.arguments)
    (state : OracleRuntimeState model snapshot domains math S) :
    NonStopping (operation (E := E) model oracles location self roles op arguments state) := by
  cases op <;> try trivial
  case query kind owner =>
    cases owner with
    | none => trivial
    | some owner => exact query_nonStopping model location self roles kind owner _ _ state

theorem action_nonStopping (model : DomainModel)
    (oracles : List (CheckedOracle snapshot domains math))
    (sourceAction : OracleProtocolAction model.toCarriers)
    (state : OracleProtocol.State model snapshot domains math S) :
    NonStopping (action (E := E) model oracles sourceAction state) := by
  cases sourceAction <;> try trivial
  case ordinary ordinaryAction => exact nonStopping_map _ _ (fun _ ↦ trivial)
  case oracle request =>
    simp only [action]
    split
    · trivial
    · exact nonStopping_map _ _ (operation_nonStopping model oracles _ _ _ _ _ state.oracle)

theorem protocol_nonStopping (model : DomainModel)
    (oracles : List (CheckedOracle snapshot domains math))
    (process : PIR.Process (OracleProtocol.Interface model) A)
    (state : OracleProtocol.State model snapshot domains math S) :
    NonStopping (protocol (E := E) model oracles process state) :=
  nonStopping_present _ (action_nonStopping model oracles) process state

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- One source action interpreted by the same checked presentation and provider pair. -/
def actionM (model : DomainModel) (oracles : List (CheckedOracle snapshot domains math))
    (ordinary : PIR.MonadHandler m (participantInterfaceOn model.toCarriers) S E)
    (base : PIR.MonadHandler m (oracleReadInterface model.toCarriers) S E) :
    PIR.MonadHandler m (OracleProtocol.Interface model)
      (OracleProtocol.State model snapshot domains math S) (OracleProtocol.Event E) :=
  fun operation state ↦ executeM (externalHandlerM ordinary base)
    (action model oracles operation state) state

/-- Expose the original source signature for generic state-relational handler reasoning. -/
theorem runM_actions (model : DomainModel)
    (oracles : List (CheckedOracle snapshot domains math))
    (ordinary : PIR.MonadHandler m (participantInterfaceOn model.toCarriers) S E)
    (base : PIR.MonadHandler m (oracleReadInterface model.toCarriers) S E)
    (process : PIR.Process (OracleProtocol.Interface model) A)
    (state : OracleProtocol.State model snapshot domains math S) :
    runM model oracles ordinary base process state =
      process.runM (actionM model oracles ordinary base) state :=
  executeM_present _ _ (action_nonStopping model oracles) process state

/-- The public monadic API is exactly generic execution of the free presentation. -/
theorem runM_envelope (model : DomainModel)
    (oracles : List (CheckedOracle snapshot domains math))
    (ordinary : PIR.MonadHandler m (participantInterfaceOn model.toCarriers) S E)
    (base : PIR.MonadHandler m (oracleReadInterface model.toCarriers) S E)
    (process : PIR.Process (OracleProtocol.Interface model) A)
    (state : OracleProtocol.State model snapshot domains math S) :
    (runM model oracles ordinary base process state >>= fun result ↦ pure (envelope result)) =
      (protocol model oracles process state).runM
        (handlerM (externalHandlerM ordinary base)) () :=
  executeM_envelope _ _ (protocol_nonStopping model oracles process state) state

/-- Source association remains explicit at the total, arbitrary-monad boundary. -/
theorem sourceRunM_envelope {subject : OracleSubject snapshot} {self : Nat}
    (start : OracleStart subject model self S)
    (ordinary : PIR.MonadHandler m (participantInterfaceOn model.toCarriers) S E)
    (base : PIR.MonadHandler m (oracleReadInterface model.toCarriers) S E) :
    (sourceRunM start ordinary base >>= fun result ↦ pure (envelope result)) =
      (source start).runM (handlerM (externalHandlerM ordinary base)) () :=
  runM_envelope model subject.unit.oracles ordinary base _ start.state

end Zkc.Source.Structured.OracleProcess
