module

public import Zkc.Source.Structured.Bindings.Assembly
public import Zkc.Source.Structured.DomainParticipant

@[expose] public section

/-! Exact invocation masks for declaration-built protocol tables. These laws
are independent of helper mathematics, input admission and successful returns.
They retain arbitrary effects, failed lookup, signature mismatch and stops. -/
namespace Zkc.Source.Structured.ProtocolPresentation
open NormalForm Bindings
set_option autoImplicit false

/-- Reconstructing a one-field ABI is the identity, including all stops. -/
theorem bind_single {Value : Ty → Type} {I : PIR.Signature} {ty : Ty}
    (process : PIR.Process I (Values Value [ty])) :
    (process.bind fun out => .done (.cons (out.get .here) .nil)) = process := by
  have same : (fun out : Values Value [ty] =>
      PIR.Process.done (I := I) (.cons (out.get .here) .nil)) = PIR.Process.done := by
    funext out
    cases out with | cons value rest => cases rest; rfl
  rw [same, PIR.Process.bind_done]

def Masked {Value : Ty → Type} {I : PIR.Signature}
    (protocols : ProtocolTable Value I) : Prop :=
  ∀ signature context self input,
    invokeProtocol protocols signature context self input =
      (invokeProtocol protocols signature context self input).bind fun out =>
        .done (maskValues self (context.mapScopes signature.outputScopes) out)

theorem masked_empty (model : DomainModel) (I : PIR.Signature) :
    Masked ([] : ProtocolTable model.Value I) := by
  intro signature context self input
  rfl

theorem masked_extend (model : DomainModel) {I : PIR.Signature}
    (sites : SiteObservations I)
    (actions : PIR.OperationInterpretation (participantInterfaceOn model.toCarriers) I)
    (helpers : Evaluation.ComponentTablesOn model.toCarriers I)
    (protocols : ProtocolTable model.Value I) (masked : Masked protocols)
    (definition : CheckedProtocol) (iterations : IterationObservations I) :
    Masked (extendProtocolTableOn model sites actions helpers protocols definition iterations) := by
  intro signature context self input
  by_cases names : definition.signature.name = signature.name
  · by_cases same : definition.signature = signature
    · subst signature
      rw [extendProtocolTableOn, invokeProtocol_cons_same]
      simp only [CheckedProtocol.signature, CheckedProtocol.denoteWithOn, PIR.Process.bind_assoc, PIR.Process.bind,
        maskValues_idempotent]
    · rw [extendProtocolTableOn, invokeProtocol_cons_mismatch _ _ _ names same]
      rfl
  · rw [extendProtocolTableOn, invokeProtocol_cons_other _ _ _ names]
    exact masked signature context self input

theorem masked_fold (model : DomainModel) {I : PIR.Signature}
    (sites : SiteObservations I)
    (actions : PIR.OperationInterpretation (participantInterfaceOn model.toCarriers) I)
    (helpers : Evaluation.ComponentTablesOn model.toCarriers I)
    (definitions : List CheckedProtocol) (iterations : IterationObservations I)
    (protocols : ProtocolTable model.Value I) (masked : Masked protocols) :
    Masked (definitions.foldl
      (fun captured definition => extendProtocolTableOn model sites actions helpers captured definition iterations)
      protocols) := by
  induction definitions generalizing protocols with
  | nil => exact masked
  | cons definition rest ih =>
    exact ih _ (masked_extend model sites actions helpers protocols masked definition iterations)

def callees (model : DomainModel) {I : PIR.Signature} (keys : List CalleeKey)
    (protocols : ProtocolTable model.Value I) : CalleeProcesses model keys I :=
  fun entry context binders =>
    invokeProtocol protocols (calleeAt keys entry).signature context
      (context.roles (calleeAt keys entry).role)
      ((calleeAt keys entry).pattern.environment model binders)

theorem callees_hold (model : DomainModel) {I : PIR.Signature} (keys : List CalleeKey)
    (protocols : ProtocolTable model.Value I) (masked : Masked protocols)
    (fills : ∀ (entry : Fin keys.length)
      (binders : Binders model (calleeAt keys entry).pattern.scope)
      (others : Values (Component model.Value) (calleeAt keys entry).pattern.absentTypes),
      (calleeAt keys entry).pattern.fill model binders others =
        (calleeAt keys entry).pattern.environment model binders)
    (bounded : ∀ entry : Fin keys.length, ∀ scope ∈ (calleeAt keys entry).signature.outputScopes,
      ∀ other ∈ scope, other < (calleeAt keys entry).signature.roles.length)
    {inputs : List Ty} (input : Values (Component model.Value) inputs) :
    CalleesHold protocols (callees model keys protocols) input := by
  intro entry context binders others _ distinct
  rw [fills entry binders others]
  have equation := masked (calleeAt keys entry).signature context
    (context.roles (calleeAt keys entry).role) ((calleeAt keys entry).pattern.environment model binders)
  refine equation.trans ?_
  apply congrArg (PIR.Process.bind _)
  funext out
  rw [staticMask_identity, mask_context context _ _ distinct _ (bounded entry)]

end Zkc.Source.Structured.ProtocolPresentation
