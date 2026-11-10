module

public import Zkc.IR.Source.Structured.DomainComponentLinking
public import Zkc.IR.Source.Structured.DomainProtocolLinking
public import Zkc.IR.Source.Structured.DomainParticipantInterpretation
public import Zkc.Protocol.Construction.Component

/-! Structural installation against the actual admitted source. Neither these rules nor
source bindings choose mathematics. They expose the same typed body under its actual complete
linked table, allowing ordinary named specifications to prove it once and serve every call. -/

@[expose] public section
open PIR Zkc.Source Zkc.Source.Structured Std.WP
-- Register the existing operational equations with the upstream construction database.
-- Body selection and helper invocation still use the checked installation rules below.
attribute [spec] protocolOperationWithOn denoteBranch denoteRepeatOn Repeat.stepOn
  Participant.query Participant.guard Participant.owned Participant.exchange
  participantActionsOn Evaluation.operationOn Evaluation.componentOperationOn
  strictComponent Process.interpret Option.elim primitiveOutcome
  Evaluation.denoteLoopOn Evaluation.invokeCallbackOn Finite.execute Finite.admitThen

attribute [spec high] Process.interpret_identity

namespace Zkc.Verification.Construction

@[spec] theorem silentMark (I : Signature) (site : String) :
    (SiteObservations.silent I).mark site = .done () := rfl


variable (model : DomainModel) {I : Signature} {Pred EPred : Type}
  [Assertion Pred] [Assertion EPred] [WPMonad (Process I) Pred EPred]
  (observations : SiteObservations I) (payload : UnitPayload)
  (definition : CheckedDefinition) (member : definition ∈ payload.definitions)

include member

/-- Invocation uses the actual dependency closure and preserves stopping outcomes. -/
theorem helper (arguments : Values model.Value definition.inputs)
    (post : Values model.Value definition.outputs → Pred) (stopped : EPred) :
    ⦃wp (definition.body.denote
      (Evaluation.meaningOn model observations
        (payload.definitions.foldl (Evaluation.extendMeaningsOn model observations) []))
      arguments.get) post stopped⦄
      invoke (payload.definitions.foldl (Evaluation.extendMeaningsOn model observations) [])
        definition.helper arguments ⦃post; stopped⦄ := by
  rw [Evaluation.definitions_invoke_bodyOn model observations payload.definitions
    payload.linked definition member arguments]
  exact ⟨Lean.Order.PartialOrder.rel_refl⟩


/-- Optional operands retain their dependency-precise meaning; they are not all sequenced. -/
theorem componentBody (arguments : Values (Component model.Value) definition.inputs)
    (post : Values (Component model.Value) definition.outputs → Pred) (stopped : EPred) :
    ⦃wp (definition.body.component
      (Evaluation.meaningOn model observations
        (payload.definitions.foldl (Evaluation.ComponentTablesOn.extend model observations) ⟨[], []⟩).closed)
      (Evaluation.componentOperationOn model observations
        (payload.definitions.foldl (Evaluation.ComponentTablesOn.extend model observations) ⟨[], []⟩))
      arguments.get) post stopped⦄
      invoke (payload.definitions.foldl
        (Evaluation.ComponentTablesOn.extend model observations) ⟨[], []⟩).components
        definition.helper arguments ⦃post; stopped⦄ := by
  rw [Evaluation.component_invoke_bodyOn model observations payload.definitions
    payload.linked definition member arguments]
  exact ⟨Lean.Order.PartialOrder.rel_refl⟩

/-- Select closed reuse from the actual optional operands. Failed sequencing does not
change Math semantics: the dependency-precise body interpretation remains available. -/
theorem component (arguments : Values (Component model.Value) definition.inputs)
    (post : Values (Component model.Value) definition.outputs → Pred) (stopped : EPred) :
    ⦃wp ((RoleFamily.sequence arguments).elim
      (definition.body.component
        (Evaluation.meaningOn model observations
          (payload.definitions.foldl (Evaluation.ComponentTablesOn.extend model observations) ⟨[], []⟩).closed)
        (Evaluation.componentOperationOn model observations
          (payload.definitions.foldl (Evaluation.ComponentTablesOn.extend model observations) ⟨[], []⟩))
        arguments.get)
      (fun values => (invoke (payload.definitions.foldl
        (Evaluation.extendMeaningsOn model observations) []) definition.helper values).bind
          (fun results => .done results.present))) post stopped⦄
      invoke (payload.definitions.foldl
        (Evaluation.ComponentTablesOn.extend model observations) ⟨[], []⟩).components
        definition.helper arguments ⦃post; stopped⦄ := by
  cases sequenced : RoleFamily.sequence arguments with
  | none =>
    exact componentBody model observations payload definition member arguments post stopped
  | some values =>
    have same := (RoleFamily.sequence_eq_some arguments values).mp sequenced
    subst arguments
    erw [Evaluation.ComponentTablesOn.adequate_fold model observations _
      Evaluation.ComponentTablesOn.adequate_empty payload.definitions definition.helper values,
      Evaluation.ComponentTablesOn.closed_fold]
    exact ⟨Lean.Order.PartialOrder.rel_refl⟩

omit member in
/-- Participant installation retains actual role substitution and input/output placement. -/
theorem protocol
    (actions : OperationInterpretation (participantInterfaceOn model.toCarriers) I)
    (helpers : Evaluation.ComponentTablesOn model.toCarriers I)
    (iterations : IterationObservations I)
    (declaration : CheckedProtocol) (present : declaration ∈ payload.protocols)
    (context : ProtocolContext) (self : Nat)
    (arguments : Values (Component model.Value) declaration.inputs)
    (post : Values (Component model.Value) declaration.outputs → Pred) (stopped : EPred) :
    ⦃wp (declaration.body.denote
      (participantMeaningWithOn model observations actions helpers self
        (payload.protocols.foldl (fun table definition =>
          extendProtocolTableOn model observations actions helpers table definition iterations) [])
        context iterations)
      (maskValues self (context.mapScopes declaration.inputScopes) arguments).get)
      (fun values => post (maskValues self (context.mapScopes declaration.outputScopes) values))
      stopped⦄
      invokeProtocol (payload.protocols.foldl (fun table definition =>
        extendProtocolTableOn model observations actions helpers table definition iterations) [])
        declaration.signature context self arguments ⦃post; stopped⦄ := by
  erw [protocol_invoke_bodyOn model observations actions helpers iterations payload.protocols
    payload.protocolsLinked declaration present context self arguments]
  unfold CheckedProtocol.denoteWithOn
  exact Triple.bind (m := Process I) (epost := stopped) _ _
    (fun values => post (maskValues self (context.mapScopes declaration.outputScopes) values))
    ⟨Lean.Order.PartialOrder.rel_refl⟩
    (fun values => ProtocolProof.Construction.processDone _ post stopped)

omit member in
/-- The public participant view uses the actual plain table of the admitted program. -/
@[spec] theorem participant (program : Program) (self : Nat)
    [WPMonad (Process (participantInterfaceOn model.toCarriers)) Pred EPred]
    (arguments : Values (Component model.Value) program.payload.entry.inputs)
    (post : Values (Component model.Value) program.payload.entry.outputs → Pred) (stopped : EPred) :
    ⦃wp (invokeProtocol (program.payload.plainProtocolTableOn model)
      program.payload.entry.signature {} self arguments) post stopped⦄
      program.participantOn model self arguments ⦃post; stopped⦄ := by
  rw [Program.participantOn_eq_plain]
  exact ⟨Lean.Order.PartialOrder.rel_refl⟩

end Zkc.Verification.Construction
