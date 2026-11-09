module

public import Zkc.IR.Source.Structured.ProtocolEmbeddingProtocol

@[expose] public section

/-! Source-bound ordinary specialization of the actual lazy Oracle participant. The
premises inspect the exact retained bodies. No alternative program or helper meanings
are supplied. Equality is of free processes, before choosing provider replies. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Zkc.Source.Structured.ProtocolEmbedding
open Zkc.Source

/-- The ordinary fragment is a structural property of the stored closure, including
unused definitions and nested callbacks. Local helpers retain their original semantics. -/
def OrdinaryFragment (payload : UnitPayload) : Prop :=
  MathFragment payload.definitions ∧
    ∀ definition ∈ payload.protocols, Fragment OrdinaryOperation definition.body

theorem ordinary_tables_adequate (payload : UnitPayload) (model : DomainModel) :
    (ordinaryTables payload model).Adequate :=
  Evaluation.ComponentTablesOn.adequate_fold model (.silent _) _
    Evaluation.ComponentTablesOn.adequate_empty payload.definitions

theorem protocol_body_embed (payload : UnitPayload) (model : DomainModel) (self : Nat)
    (math : MathFragment payload.definitions)
    (ordinary : ProtocolTable model.Value (OracleProtocol.Interface model))
    (lazy : ProtocolTable (ProtocolValue model.toCarriers) (OracleProtocol.Interface model))
    (related : ProtocolTablesRelated model self ordinary lazy) (context : ProtocolContext)
    {ts us} (body : Region protocolDialect ts us) (fragment : Fragment OrdinaryOperation body)
    (env : Environment (Component model.Value) ts) :
    (body.denote ((OracleProtocol.algebra model self (ordinaryTables payload model)
      (payload.oracleCalculations model self)).meaning lazy context self)
      (fun {t} ref ↦ component t (env ref))).interpret (eraseInternal model.toCarriers) =
      (body.denote (participantMeaningWithOn model (.silent _) (OracleProtocol.actions model)
        (ordinaryTables payload model) self ordinary context .silent) env).bind
          (fun result ↦ .done (ProtocolValue.embedComponents result)) := by
  simpa only [map_components] using region_naturality
    (participantMeaningWithOn model (.silent _) (OracleProtocol.actions model)
      (ordinaryTables payload model) self ordinary context .silent)
    ((OracleProtocol.algebra model self (ordinaryTables payload model)
      (payload.oracleCalculations model self)).meaning lazy context self)
    component (eraseInternal model.toCarriers) OrdinaryOperation
    (fun op allowed args left right callbacks ↦ by
      simpa only [map_components] using operation_embed model self (ordinaryTables payload model)
        (ordinary_tables_adequate payload model) (ordinary_tables_erase payload model)
        (payload.oracleCalculations model self) (payload_math_related payload model self math)
        ordinary lazy related context op allowed args left right callbacks)
    body fragment env

theorem protocol_definition_embed (payload : UnitPayload) (model : DomainModel) (self : Nat)
    (math : MathFragment payload.definitions)
    (ordinary : ProtocolTable model.Value (OracleProtocol.Interface model))
    (lazy : ProtocolTable (ProtocolValue model.toCarriers) (OracleProtocol.Interface model))
    (related : ProtocolTablesRelated model self ordinary lazy) (definition : CheckedProtocol)
    (fragment : Fragment OrdinaryOperation definition.body) (context : ProtocolContext)
    (args : Values (Component model.Value) definition.inputs) :
    ((OracleProtocol.algebra model self (ordinaryTables payload model)
      (payload.oracleCalculations model self)).denote definition lazy context self
        (ProtocolValue.embedComponents args)).interpret (eraseInternal model.toCarriers) =
      (definition.denoteWithOn model (.silent _) (OracleProtocol.actions model)
        (ordinaryTables payload model) ordinary .silent context self args).bind
          (fun result ↦ .done (ProtocolValue.embedComponents result)) := by
  unfold ProtocolAlgebra.denote CheckedProtocol.denoteWithOn
  dsimp only [CheckedProtocol.signature] at args ⊢
  rw [NormalForm.normalizeActions_process]
  simp only [PIR.Process.interpret_bind, PIR.Process.interpret, mask_embed]
  have environment := mapValues_environment component
    (maskValues self (context.mapScopes definition.inputScopes) args)
  rw [map_components] at environment
  rw [environment, protocol_body_embed payload model self math ordinary lazy related context
    definition.body fragment]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind, mask_embed]

theorem protocol_tables_extend (payload : UnitPayload) (model : DomainModel) (self : Nat)
    (math : MathFragment payload.definitions)
    (ordinary : ProtocolTable model.Value (OracleProtocol.Interface model))
    (lazy : ProtocolTable (ProtocolValue model.toCarriers) (OracleProtocol.Interface model))
    (related : ProtocolTablesRelated model self ordinary lazy) (definition : CheckedProtocol)
    (fragment : Fragment OrdinaryOperation definition.body) :
    ProtocolTablesRelated model self
      (extendProtocolTableOn model (.silent _) (OracleProtocol.actions model)
        (ordinaryTables payload model) ordinary definition .silent)
      (ProtocolAlgebra.extend (OracleProtocol.algebra model self (ordinaryTables payload model)
        (payload.oracleCalculations model self)) lazy definition) := by
  intro signature context args
  by_cases names : definition.signature.name = signature.name
  · by_cases same : definition.signature = signature
    · subst signature
      simp only [extendProtocolTableOn, ProtocolAlgebra.extend]
      erw [invokeProtocol_cons_same, invokeProtocol_cons_same]
      exact protocol_definition_embed payload model self math ordinary lazy related definition
        fragment context args
    · simp only [extendProtocolTableOn, ProtocolAlgebra.extend]
      rw [invokeProtocol_cons_mismatch _ _ _ names same,
        invokeProtocol_cons_mismatch _ _ _ names same]
      rfl
  · simp only [extendProtocolTableOn, ProtocolAlgebra.extend]
    rw [invokeProtocol_cons_other _ _ _ names, invokeProtocol_cons_other _ _ _ names]
    exact related signature context args

theorem protocol_tables_fold (payload : UnitPayload) (model : DomainModel) (self : Nat)
    (math : MathFragment payload.definitions)
    (ordinary : ProtocolTable model.Value (OracleProtocol.Interface model))
    (lazy : ProtocolTable (ProtocolValue model.toCarriers) (OracleProtocol.Interface model))
    (related : ProtocolTablesRelated model self ordinary lazy) (definitions : List CheckedProtocol)
    (fragment : ∀ definition ∈ definitions, Fragment OrdinaryOperation definition.body) :
    ProtocolTablesRelated model self
      (definitions.foldl (fun captured definition ↦ extendProtocolTableOn model (.silent _)
        (OracleProtocol.actions model) (ordinaryTables payload model) captured definition .silent)
        ordinary)
      (definitions.foldl (ProtocolAlgebra.extend (OracleProtocol.algebra model self
        (ordinaryTables payload model) (payload.oracleCalculations model self))) lazy) := by
  induction definitions generalizing ordinary lazy with
  | nil => exact related
  | cons definition rest ih =>
    exact ih _ _ (protocol_tables_extend payload model self math ordinary lazy related definition
      (fragment definition (by simp)))
      (fun definition member ↦ fragment definition (by simp [member]))

/-- Ordinary closures in the Oracle effect interface, by the same source fold. -/
def embeddedOrdinaryTable (payload : UnitPayload) (model : DomainModel) :
    ProtocolTable model.Value (OracleProtocol.Interface model) :=
  payload.protocols.foldl (fun captured definition ↦ extendProtocolTableOn model (.silent _)
    (OracleProtocol.actions model) (ordinaryTables payload model) captured definition .silent) []

theorem payload_protocol_related (payload : UnitPayload) (model : DomainModel) (self : Nat)
    (fragment : OrdinaryFragment payload) :
    ProtocolTablesRelated model self (embeddedOrdinaryTable payload model)
      (payload.oracleProtocolTable model self) :=
  protocol_tables_fold payload model self fragment.1 [] [] (fun _ _ _ ↦ rfl)
    payload.protocols fragment.2

theorem ordinary_table_actions (payload : UnitPayload) (model : DomainModel) :
    ProtocolTable.Interprets (OracleProtocol.actions model)
      (payload.plainProtocolTableOn model) (embeddedOrdinaryTable payload model) :=
  ProtocolTable.foldOn_interpret (OracleProtocol.actions model)
    (SiteObservations.silent_interpret _)
    (fun action ↦ by simp only [participantActionsOn, PIR.Process.interpret, PIR.Process.bind_done])
    (Evaluation.ComponentTablesOn.fold_interpret _ (SiteObservations.silent_interpret _)
      (.empty _) payload.definitions)
    (.empty _) (IterationObservations.silent_interpret _) payload.protocols

/-- Strong ordinary-to-lazy specialization. Inputs may be absent. Every original outcome
and every service request/reply continuation is retained; only internal bookkeeping is erased. -/
theorem program_embedding (program : Program) (model : DomainModel) (self : Nat)
    (fragment : OrdinaryFragment program.payload)
    (inputs : Values (Component model.Value) program.payload.entry.inputs) :
    (program.oracleParticipant model self (ProtocolValue.embedComponents inputs)).interpret
      (eraseInternal model.toCarriers) =
      ((program.participantOn model self inputs).interpret (OracleProtocol.actions model)).bind
        (fun result ↦ .done (ProtocolValue.embedComponents result)) := by
  rw [Program.participantOn_eq_plain]
  erw [ordinary_table_actions program.payload model
    program.payload.entry.signature {} self inputs]
  exact payload_protocol_related program.payload model self fragment
    program.payload.entry.signature {} inputs

/-- Projecting ordinary outputs recovers the original free process exactly. This bind
changes returned values only; it preserves every stopped prefix and effect continuation. -/
theorem program_specialization (program : Program) (model : DomainModel) (self : Nat)
    (fragment : OrdinaryFragment program.payload)
    (inputs : Values (Component model.Value) program.payload.entry.inputs) :
    ((program.oracleParticipant model self (ProtocolValue.embedComponents inputs)).interpret
      (eraseInternal model.toCarriers)).bind
        (fun result ↦ .done (ProtocolValue.concreteComponents result)) =
      (program.participantOn model self inputs).interpret (OracleProtocol.actions model) := by
  rw [program_embedding program model self fragment inputs]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind,
    ProtocolValue.concreteComponents_embedComponents, PIR.Process.bind_done]

/-- Exact executions under every reply/stop handler: original outcome, residual state,
and ordered events, after the fixed internal-event and output interpretations. -/
theorem program_specialization_run (program : Program) (model : DomainModel) (self : Nat)
    (fragment : OrdinaryFragment program.payload)
    (inputs : Values (Component model.Value) program.payload.entry.inputs)
    {S E : Type} (handler : PIR.Handler (OracleProtocol.Interface model) S E) (state : S) :
    (((program.oracleParticipant model self (ProtocolValue.embedComponents inputs)).interpret
      (eraseInternal model.toCarriers)).bind
        (fun result ↦ .done (ProtocolValue.concreteComponents result))).run handler state =
      ((program.participantOn model self inputs).interpret
        (OracleProtocol.actions model)).run handler state := by
  rw [program_specialization program model self fragment inputs]

/-- The source association is the canonical imported program, not an authored replacement.
The runtime-selection guard is retained as an explicit ordinary-source boundary. -/
theorem imported_embedding {snapshot : Snapshot} (imported : Imported snapshot)
    (_ordinarySource : snapshot.requiresOracleRuntime = false)
    (fragment : OrdinaryFragment imported.program.payload) (model : DomainModel) (self : Nat)
    (inputs : Values (Component model.Value) imported.program.payload.entry.inputs) :
    (imported.program.oracleParticipant model self (ProtocolValue.embedComponents inputs)).interpret
      (eraseInternal model.toCarriers) =
      ((imported.program.participantOn model self inputs).interpret
        (OracleProtocol.actions model)).bind
        (fun result ↦ .done (ProtocolValue.embedComponents result)) :=
  program_embedding imported.program model self fragment inputs

/-- Equality holds under every handler, with its exact residual state and ordered history.
This does not identify that state with the canonical source cursor or Oracle store. -/
theorem program_all_replies (program : Program) (model : DomainModel) (self : Nat)
    (fragment : OrdinaryFragment program.payload)
    (inputs : Values (Component model.Value) program.payload.entry.inputs)
    {S E : Type} (handler : PIR.Handler (OracleProtocol.Interface model) S E) (state : S) :
    ((program.oracleParticipant model self (ProtocolValue.embedComponents inputs)).interpret
      (eraseInternal model.toCarriers)).run handler state =
      (((program.participantOn model self inputs).interpret (OracleProtocol.actions model)).bind
        (fun result ↦ .done (ProtocolValue.embedComponents result))).run handler state := by
  rw [program_embedding program model self fragment inputs]

/-- Execute the actual lazy process under the bookkeeping interpretation of an arbitrary
handler. Public operations use that handler without any change to replies, state or events.
The canonical Oracle store/cursor handler is a separate representation boundary. -/
theorem program_bookkeeping_run (program : Program) (model : DomainModel) (self : Nat)
    (fragment : OrdinaryFragment program.payload)
    (inputs : Values (Component model.Value) program.payload.entry.inputs)
    {S E : Type} (handler : PIR.Handler (OracleProtocol.Interface model) S E) (state : S) :
    (program.oracleParticipant model self (ProtocolValue.embedComponents inputs)).run
      (fun op residual ↦ (eraseInternal model.toCarriers op).run handler residual) state =
      (((program.participantOn model self inputs).interpret (OracleProtocol.actions model)).bind
        (fun result ↦ .done (ProtocolValue.embedComponents result))).run handler state := by
  rw [← PIR.Process.run_interpret]
  exact program_all_replies program model self fragment inputs handler state

end Zkc.Source.Structured.ProtocolEmbedding
