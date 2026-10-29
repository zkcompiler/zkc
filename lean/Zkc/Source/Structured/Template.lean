module

public import Zkc.Source.Structured.DomainProtocolLinking
public import Zkc.Source.Structured.InputVisibility

@[expose] public section

/-! Install a shared mathematical body law at any linked source declaration.
The full signature and exact raw tree are checked separately from mathematics.
Visibility is handled once here, including absent private input components.
-/
set_option autoImplicit false
namespace Zkc.Source.Structured.Template
open Zkc.Source Zkc.Source.Structured NormalForm

attribute [local implicit_reducible] CheckedProtocol.signature

variable {model : DomainModel}

theorem invoke (payload : UnitPayload) (definition : CheckedProtocol)
    (member : definition ∈ payload.protocols)
    (body : Region protocolDialect definition.inputs definition.outputs)
    (associated : definition.raw = body.erase)
    (role : Nat) (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx role definition.roles.length)
    (pattern : InputPattern definition.inputs)
    (visible : InputVisibility.patternVisible role pattern definition.inputScopes = true)
    (args : Binders model pattern.scope)
    (others : Values (Component model.Value) pattern.absentTypes)
    (reference : PIR.Process (Occurrence.signature model.toCarriers)
      (Values (Component model.Value) definition.outputs))
    (law : body.denote
      (participantMeaningWithOn model (.silent _) Occurrence.actions
        (Occurrence.helpers model payload) (ctx.roles role) (Occurrence.table model payload)
        ctx Occurrence.iterations) (pattern.environment model args).get = reference)
    (inputScopes : InputVisibility.scopesBounded definition.roles.length definition.inputScopes = true)
    (outputScopes : InputVisibility.scopesBounded definition.roles.length definition.outputScopes = true) :
    invokeProtocol (Occurrence.table model payload) definition.signature ctx (ctx.roles role)
      (pattern.fill model args others) = reference.bind fun out =>
        .done (staticMask role out definition.outputScopes
          (Operands.identity definition.outputs)) := by
  rw [Occurrence.invoke_body model payload definition member]
  unfold CheckedProtocol.denoteWithOn
  rw [definition.body_eq_of_raw body associated]
  rw [(InputVisibility.mask_context distinct _ inputScopes _).trans
    (InputVisibility.mask_fill model role pattern _ visible args others), law]
  apply congrArg (PIR.Process.bind reference)
  funext out
  apply congrArg PIR.Process.done
  exact (InputVisibility.mask_context distinct _ outputScopes out).trans
    (InputVisibility.staticMask_identity role definition.outputScopes out).symm

/-- A proposed declaration selection is checked against the entire signature
and raw typed body. Selecting an index or matching a name supplies neither fact.
This permits one reusable body law to serve several admitted declarations. -/
structure Association (payload : UnitPayload) (signature : ProtocolSignature)
    (body : Region protocolDialect signature.inputs signature.outputs) where
  definition : CheckedProtocol
  member : definition ∈ payload.protocols
  signature_eq : definition.signature = signature
  body_eq : definition.raw = body.erase

theorem Association.invoke {payload : UnitPayload} {signature : ProtocolSignature}
    {body : Region protocolDialect signature.inputs signature.outputs}
    (association : Association payload signature body)
    (role : Nat) (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx role signature.roles.length)
    (pattern : InputPattern signature.inputs)
    (visible : InputVisibility.patternVisible role pattern signature.inputScopes = true)
    (args : Binders model pattern.scope)
    (others : Values (Component model.Value) pattern.absentTypes)
    (reference : PIR.Process (Occurrence.signature model.toCarriers)
      (Values (Component model.Value) signature.outputs))
    (law : body.denote
      (participantMeaningWithOn model (.silent _) Occurrence.actions
        (Occurrence.helpers model payload) (ctx.roles role) (Occurrence.table model payload)
        ctx Occurrence.iterations) (pattern.environment model args).get = reference)
    (inputScopes : InputVisibility.scopesBounded signature.roles.length signature.inputScopes = true)
    (outputScopes : InputVisibility.scopesBounded signature.roles.length signature.outputScopes = true) :
    invokeProtocol (Occurrence.table model payload) signature ctx (ctx.roles role)
      (pattern.fill model args others) = reference.bind fun out =>
        .done (staticMask role out signature.outputScopes (Operands.identity signature.outputs)) := by
  rcases association with ⟨definition, member, same, associated⟩
  cases same
  exact Template.invoke payload definition member body associated role ctx distinct pattern visible
    args others reference law inputScopes outputScopes

end Zkc.Source.Structured.Template
