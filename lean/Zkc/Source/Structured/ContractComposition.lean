module

public import Zkc.Source.Structured.ContractCalls
public import Zkc.Source.Structured.ProtocolLinking
public import Zkc.Source.RegionDerivation
public import Zkc.Source.Structured.RepeatLaws

@[expose] public section

/-! Source call substitution at the actual checked application constructor.
The linker supplies the callee body; a local law or a structural derivation
supplies its selected process semantics. The caller's equation then follows
from the existing bind semantics, with actual operands, masks and continuation.
Property-specific quantifiers, logical parameters and experiments stay outside
this exact process rule.
-/
set_option autoImplicit false
namespace Zkc.Source.Structured

/-- A local callee request cannot be discharged by an empty clause list. A user
may provide a law about this exact callee process or inspect its typed body with
existing structural rules. Neither constructor assumes a caller equation. -/
inductive CalleeResolution {I : PIR.Signature} (meaning : RegionMeaning protocolDialect I)
    {Γ out : List Ty} (body : Region protocolDialect Γ out)
    (environment : Environment meaning.Value Γ)
    (target : PIR.Proc I (Values meaning.Value out)) : Prop where
  | localLaw (law : body.denote meaning environment = target)
  | inspect (derivation : Region.Derivation meaning (fun op => .call op .done)
      body (@environment) target)

theorem CalleeResolution.sound {I : PIR.Signature} {meaning : RegionMeaning protocolDialect I}
    {Γ out : List Ty} {body : Region protocolDialect Γ out}
    {environment : Environment meaning.Value Γ} {target : PIR.Proc I (Values meaning.Value out)}
    (resolution : CalleeResolution meaning body (@environment) target) :
    body.denote meaning environment = target := by
  cases resolution with
  | localLaw law => exact law
  | inspect derivation => exact derivation.sound_identity

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- A consumer-selected process interface for one actual inventory element.
Full callee identity and body association are mandatory even without clauses.
Logical experiment parameters can be fixed in `target` by the consumer; this
record never recovers them from runtime operands. -/
structure CallSpecification (payload : UnitPayload) {Γ out : List Ty}
    {caller : Region protocolDialect Γ out} (call : CallOccurrence caller) where
  definition : CheckedProtocol
  member : definition ∈ payload.protocols
  sameSignature : definition.signature = call.callSite.signature
  body : Region protocolDialect call.callSite.signature.inputs call.callSite.signature.outputs
  exactRaw : definition.raw = body.erase
  premise : ProtocolContext → Nat → Values (Component (assignment F G)) call.callSite.signature.inputs → Prop
  target : ProtocolContext → Nat → Values (Component (assignment F G)) call.callSite.signature.inputs →
    PIR.Proc (observedInterface F G) (Values (Component (assignment F G)) call.callSite.signature.outputs)

/-- A required local leaf at every context and actual input tuple. The returned
process is the raw callee body; generic source composition applies output masks.
An unannotated callee has exactly the same request as an annotated one. A false
precondition makes this record vacuous; substitution still requires that
precondition at the actual operands. Resolution alone proves no property. -/
def CallSpecification.Resolved {payload : UnitPayload} {Γ out : List Ty}
    {caller : Region protocolDialect Γ out} {call : CallOccurrence caller}
    (specification : CallSpecification (F := F) (G := G) payload call) : Prop :=
  ∀ context self inputs, specification.premise context self inputs → CalleeResolution
    (participantMeaning (payload.tables F G) self (payload.protocolTable F G) context)
    specification.body
    (maskValues self (context.mapScopes call.callSite.signature.inputScopes) inputs).get
    (specification.target context self inputs)

/-- The inventory generates all local semantic requests. The consumer must
supply a specification for every call, and a proof of every selected local law.
Terminal/property requests belong to the consumer's separate typed inventory. -/
abbrev CallSemanticObligations {payload : UnitPayload} {Γ out : List Ty}
    (caller : Region protocolDialect Γ out)
    (specifications : (call : CallOccurrence caller) → CallSpecification (F := F) (G := G) payload call) :=
  CallObligations caller (fun call => (specifications call).Resolved)

/-- Keep the checked call's exact process as its target. This is a valid local
process law but provides no abstraction or security property. -/
def CallSpecification.identity {payload : UnitPayload} {Γ out : List Ty}
    {caller : Region protocolDialect Γ out} {call : CallOccurrence caller}
    (specification : CallSpecification (F := F) (G := G) payload call) :
    CallSpecification (F := F) (G := G) payload call :=
  { specification with
    premise := fun _ _ _ => True
    target := fun context self inputs => specification.body.denote
      (participantMeaning (payload.tables F G) self (payload.protocolTable F G) context)
      (maskValues self (context.mapScopes call.callSite.signature.inputScopes) inputs).get }

/-- Lexical accounting can always use identity once the actual checked callee
associations are supplied. Coverage alone supplies no new semantic property. -/
theorem CallSemanticObligations.identity {payload : UnitPayload} {Γ out : List Ty}
    (caller : Region protocolDialect Γ out)
    (specifications : (call : CallOccurrence caller) → CallSpecification (F := F) (G := G) payload call) :
    CallSemanticObligations caller (fun call => (specifications call).identity) := by
  intro call context self inputs _
  exact .localLaw rfl

namespace UnitPayload

/-- A checked source application as an occurrence-local derivation rule.
Both observations and action interpretation are explicit, so the same rule
works for observed and plain participant semantics. The local premise is only
needed for an actual participant; outside copies receive the absent tuple.
No law about the caller or its continuation is a premise. -/
theorem protocolApply_operationLaw (payload : UnitPayload)
    {I J : PIR.Signature} (observations : SiteObservations I)
    (actions : PIR.OperationInterpretation (participantInterface F G) I)
    (helpers : Evaluation.ComponentTables F G I)
    (operations : PIR.OperationInterpretation I J)
    (definition : CheckedProtocol) (member : definition ∈ payload.protocols)
    (signature : ProtocolSignature) (sameSignature : definition.signature = signature)
    (body : Region protocolDialect signature.inputs signature.outputs)
    (exactRaw : definition.raw = body.erase)
    (roles : List Nat) (site : String) (context : ProtocolContext) (self : Nat)
    (args : Values (Component (assignment F G)) signature.inputs)
    (target : PIR.Proc J (Values (Component (assignment F G)) signature.outputs))
    (callee : (context.enter site roles).contains signature self = true →
      (body.denote
        (participantMeaningWith observations actions helpers self
          (payload.protocols.foldl (extendProtocolTable observations actions helpers) [])
          (context.enter site roles))
        (maskValues self ((context.enter site roles).mapScopes signature.inputScopes) args).get).interpret
          operations = target) :
    (participantMeaningWith observations actions helpers self
      (payload.protocols.foldl (extendProtocolTable observations actions helpers) []) context).OperationLaw
      operations (.protocolApply signature roles site) args .nil
      (if (context.enter site roles).contains signature self then
        target.bind (fun values => .done (maskValues self
          ((context.enter site roles).mapScopes signature.outputScopes) values))
       else .done (Values.absent (assignment F G) signature.outputs)) := by
  subst signature
  intro callbacks _
  cases callbacks
  change (protocolOperationWith observations actions helpers self
    (.protocolApply definition.signature roles site) args .nil
    (payload.protocols.foldl (extendProtocolTable observations actions helpers) []) context).interpret
      operations = _
  by_cases inside : (context.enter site roles).contains definition.signature self = true
  · simp only [protocolOperationWith, inside, ↓reduceIte]
    erw [protocol_invoke_body_view observations actions helpers payload.protocols
      payload.protocolsLinked definition member body exactRaw]
    erw [PIR.Proc.interpret_bind, callee inside]
    rfl
  · simp only [protocolOperationWith, inside]
    rfl

/-- The actual application, linked to an exact checked callee, composes its
masked returned tuple with the caller's real continuation. This is an equation
of complete open processes, preserving arbitrary replies and stops. -/
theorem protocolApply_body (payload : UnitPayload)
    (definition : CheckedProtocol) (member : definition ∈ payload.protocols)
    (signature : ProtocolSignature) (sameSignature : definition.signature = signature)
    (body : Region protocolDialect signature.inputs signature.outputs)
    (exactRaw : definition.raw = body.erase)
    (roles : List Nat) (site : String) (context : ProtocolContext) (self : Nat)
    {Γ out : List Ty} (operands : Operands Γ signature.inputs)
    (next : Region protocolDialect (signature.outputs ++ Γ) out)
    (environment : Environment (Component (assignment F G)) Γ)
    (inside : (context.enter site roles).contains signature self = true) :
    (Region.letOp (dialect := protocolDialect) (.protocolApply signature roles site) operands .nil next).denote
      (participantMeaning (payload.tables F G) self (payload.protocolTable F G) context) environment =
      (body.denote
        (participantMeaning (payload.tables F G) self (payload.protocolTable F G)
          (context.enter site roles))
        (maskValues self ((context.enter site roles).mapScopes signature.inputScopes)
          (operands.eval environment)).get).bind
        (fun returned => next.denote
          (participantMeaning (payload.tables F G) self (payload.protocolTable F G) context)
          (environment.prepend (maskValues self
            ((context.enter site roles).mapScopes signature.outputScopes) returned))) := by
  change (protocolOperationWith (observedSites F G) observeAction (payload.tables F G) self
    (.protocolApply signature roles site) (operands.eval environment) .nil
    (payload.protocolTable F G) context).bind _ = _
  simp only [protocolOperationWith, inside, ↓reduceIte]
  erw [payload.protocol_body_view_as (F := F) (G := G) definition member signature sameSignature body exactRaw]
  exact PIR.Proc.bind_assoc _ _ _

/-- Substitute a local callee law once at an actual source application. The
premise concerns only the callee at these masked actual operands. -/
theorem protocolApply_substitute (payload : UnitPayload)
    (definition : CheckedProtocol) (member : definition ∈ payload.protocols)
    (signature : ProtocolSignature) (sameSignature : definition.signature = signature)
    (body : Region protocolDialect signature.inputs signature.outputs)
    (exactRaw : definition.raw = body.erase)
    (roles : List Nat) (site : String) (context : ProtocolContext) (self : Nat)
    {Γ out : List Ty} (operands : Operands Γ signature.inputs)
    (next : Region protocolDialect (signature.outputs ++ Γ) out)
    (environment : Environment (Component (assignment F G)) Γ)
    (inside : (context.enter site roles).contains signature self = true)
    (target : PIR.Proc (observedInterface F G) (Values (Component (assignment F G)) signature.outputs))
    (callee : CalleeResolution
      (participantMeaning (payload.tables F G) self (payload.protocolTable F G)
        (context.enter site roles)) body
      (maskValues self ((context.enter site roles).mapScopes signature.inputScopes)
        (operands.eval environment)).get target) :
    (Region.letOp (dialect := protocolDialect) (.protocolApply signature roles site) operands .nil next).denote
      (participantMeaning (payload.tables F G) self (payload.protocolTable F G) context) environment =
      target.bind (fun returned => next.denote
        (participantMeaning (payload.tables F G) self (payload.protocolTable F G) context)
        (environment.prepend (maskValues self
          ((context.enter site roles).mapScopes signature.outputScopes) returned))) := by
  rw [payload.protocolApply_body definition member signature sameSignature body exactRaw
    roles site context self operands next environment inside, callee.sound]

/-- A local callee law may be stated after an operation interpretation, such
as forgetting source marks. This is the same source call substitution, retaining
all interpreted effects and the actual returned tuple in the continuation. -/
theorem protocolApply_interpret_substitute (payload : UnitPayload)
    (definition : CheckedProtocol) (member : definition ∈ payload.protocols)
    (signature : ProtocolSignature) (sameSignature : definition.signature = signature)
    (body : Region protocolDialect signature.inputs signature.outputs)
    (exactRaw : definition.raw = body.erase)
    (roles : List Nat) (site : String) (context : ProtocolContext) (self : Nat)
    {Γ out : List Ty} (operands : Operands Γ signature.inputs)
    (next : Region protocolDialect (signature.outputs ++ Γ) out)
    (environment : Environment (Component (assignment F G)) Γ)
    (inside : (context.enter site roles).contains signature self = true)
    {J : PIR.Signature} (operations : PIR.OperationInterpretation (observedInterface F G) J)
    (target : PIR.Proc J (Values (Component (assignment F G)) signature.outputs))
    (callee : (body.denote
      (participantMeaning (payload.tables F G) self (payload.protocolTable F G)
        (context.enter site roles))
      (maskValues self ((context.enter site roles).mapScopes signature.inputScopes)
        (operands.eval environment)).get).interpret operations = target) :
    ((Region.letOp (dialect := protocolDialect) (.protocolApply signature roles site)
      operands .nil next).denote
      (participantMeaning (payload.tables F G) self (payload.protocolTable F G) context)
      environment).interpret operations =
      target.bind (fun returned => (next.denote
        (participantMeaning (payload.tables F G) self (payload.protocolTable F G) context)
        (environment.prepend (maskValues self
          ((context.enter site roles).mapScopes signature.outputScopes) returned))).interpret operations) := by
  rw [payload.protocolApply_body definition member signature sameSignature body exactRaw
    roles site context self operands next environment inside, PIR.Proc.interpret_bind, callee]

/-- After an actual returning callee execution, the continuation starts at its
residual handler state, with masked outputs and all earlier events retained. -/
theorem protocolApply_run_returned (payload : UnitPayload)
    (definition : CheckedProtocol) (member : definition ∈ payload.protocols)
    (signature : ProtocolSignature) (sameSignature : definition.signature = signature)
    (body : Region protocolDialect signature.inputs signature.outputs)
    (exactRaw : definition.raw = body.erase)
    (roles : List Nat) (site : String) (context : ProtocolContext) (self : Nat)
    {Γ out : List Ty} (operands : Operands Γ signature.inputs)
    (next : Region protocolDialect (signature.outputs ++ Γ) out)
    (environment : Environment (Component (assignment F G)) Γ)
    (inside : (context.enter site roles).contains signature self = true)
    {S E : Type} (handler : PIR.Handler (observedInterface F G) S E)
    (initial middle : S) (events : List E)
    (returned : Values (Component (assignment F G)) signature.outputs)
    (returns : (body.denote
      (participantMeaning (payload.tables F G) self (payload.protocolTable F G)
        (context.enter site roles))
      (maskValues self ((context.enter site roles).mapScopes signature.inputScopes)
        (operands.eval environment)).get).run handler initial = ⟨.returned returned, middle, events⟩) :
    ((Region.letOp (dialect := protocolDialect) (.protocolApply signature roles site)
      operands .nil next).denote
      (participantMeaning (payload.tables F G) self (payload.protocolTable F G) context)
      environment).run handler initial =
      (⟨.returned returned, middle, events⟩ : PIR.Execution S E _).follow
        (fun values => (next.denote
          (participantMeaning (payload.tables F G) self (payload.protocolTable F G) context)
          (environment.prepend (maskValues self
            ((context.enter site roles).mapScopes signature.outputScopes) values))).run handler) := by
  rw [payload.protocolApply_body definition member signature sameSignature body exactRaw
    roles site context self operands next environment inside, PIR.run_bind, returns]

/-- A stopped callee retains its residual handler state and prior events, and
never reaches the source continuation. No returned boundary is invented. -/
theorem protocolApply_run_stopped (payload : UnitPayload)
    (definition : CheckedProtocol) (member : definition ∈ payload.protocols)
    (signature : ProtocolSignature) (sameSignature : definition.signature = signature)
    (body : Region protocolDialect signature.inputs signature.outputs)
    (exactRaw : definition.raw = body.erase)
    (roles : List Nat) (site : String) (context : ProtocolContext) (self : Nat)
    {Γ out : List Ty} (operands : Operands Γ signature.inputs)
    (next : Region protocolDialect (signature.outputs ++ Γ) out)
    (environment : Environment (Component (assignment F G)) Γ)
    (inside : (context.enter site roles).contains signature self = true)
    {S E : Type} (handler : PIR.Handler (observedInterface F G) S E)
    (initial finalState : S) (events : List E) (reason : PIR.Stop)
    (stops : (body.denote
      (participantMeaning (payload.tables F G) self (payload.protocolTable F G)
        (context.enter site roles))
      (maskValues self ((context.enter site roles).mapScopes signature.inputScopes)
        (operands.eval environment)).get).run handler initial =
        ⟨.stopped reason, finalState, events⟩) :
    ((Region.letOp (dialect := protocolDialect) (.protocolApply signature roles site) operands .nil next).denote
      (participantMeaning (payload.tables F G) self (payload.protocolTable F G) context)
      environment).run handler initial = ⟨.stopped reason, finalState, events⟩ := by
  rw [payload.protocolApply_body definition member signature sameSignature body exactRaw
    roles site context self operands next environment inside, PIR.run_bind, stops]
  rfl

/-- Nonparticipants skip the body and continue with the existing absent tuple.
This case needs no callee law, and does not assert the callee property. -/
theorem protocolApply_outside (payload : UnitPayload)
    (signature : ProtocolSignature) (roles : List Nat) (site : String)
    (context : ProtocolContext) (self : Nat) {Γ out : List Ty}
    (operands : Operands Γ signature.inputs)
    (next : Region protocolDialect (signature.outputs ++ Γ) out)
    (environment : Environment (Component (assignment F G)) Γ)
    (outside : (context.enter site roles).contains signature self = false) :
    (Region.letOp (dialect := protocolDialect) (.protocolApply signature roles site) operands .nil next).denote
      (participantMeaning (payload.tables F G) self (payload.protocolTable F G) context) environment =
      next.denote (participantMeaning (payload.tables F G) self (payload.protocolTable F G) context)
        (environment.prepend (Values.absent (assignment F G) signature.outputs)) := by
  change (protocolOperationWith (observedSites F G) observeAction (payload.tables F G) self
    (.protocolApply signature roles site) (operands.eval environment) .nil
    (payload.protocolTable F G) context).bind _ = _
  simp only [protocolOperationWith, outside, Bool.false_eq_true, ↓reduceIte, PIR.Proc.bind]
  rfl

end UnitPayload

/-- A retained contract binding supplies callee identity, full ABI and exact
body association directly. The operation rule needs no duplicated link record. -/
theorem ContractBinding.protocolApply_operationLaw {snapshot : Snapshot}
    {imported : Imported snapshot} (binding : ContractBinding imported)
    {I J : PIR.Signature} (observations : SiteObservations I)
    (actions : PIR.OperationInterpretation (participantInterface F G) I)
    (helpers : Evaluation.ComponentTables F G I)
    (operations : PIR.OperationInterpretation I J)
    (roles : List Nat) (site : String) (context : ProtocolContext) (self : Nat)
    (args : Values (Component (assignment F G)) binding.protocol.inputs)
    (target : PIR.Proc J (Values (Component (assignment F G)) binding.protocol.outputs))
    (callee : (context.enter site roles).contains binding.protocol.signature self = true →
      (binding.protocol.body.denote
        (participantMeaningWith observations actions helpers self
          (imported.program.payload.protocols.foldl (extendProtocolTable observations actions helpers) [])
          (context.enter site roles))
        (maskValues self ((context.enter site roles).mapScopes binding.protocol.inputScopes) args).get).interpret
          operations = target) :
    (participantMeaningWith observations actions helpers self
      (imported.program.payload.protocols.foldl (extendProtocolTable observations actions helpers) [])
      context).OperationLaw operations (.protocolApply binding.protocol.signature roles site) args .nil
      (if (context.enter site roles).contains binding.protocol.signature self then
        target.bind (fun values => .done (maskValues self
          ((context.enter site roles).mapScopes binding.protocol.outputScopes) values))
       else .done (Values.absent (assignment F G) binding.protocol.outputs)) :=
  imported.program.payload.protocolApply_operationLaw observations actions helpers operations
    binding.protocol binding.retained.2.1 binding.protocol.signature rfl binding.protocol.body
    binding.protocol.exactBody.symm roles site context self args target callee

/-- Generated local leaves feed the generic source substitution theorem at
the EXACT subtree/continuation recovered from an inventory element. The local
precondition remains an explicit request at the actual evaluated operands. -/
theorem CallSemanticObligations.substitute {payload : UnitPayload} {Γ out : List Ty}
    {caller : Region protocolDialect Γ out}
    (specifications : (call : CallOccurrence caller) → CallSpecification (F := F) (G := G) payload call)
    (resolved : CallSemanticObligations caller specifications)
    (call : CallOccurrence caller) (context : ProtocolContext) (self : Nat)
    (environment : Environment (Component (assignment F G)) call.callSite.context)
    (inside : (context.enter call.callSite.site call.callSite.roles).contains call.callSite.signature self = true)
    (premise : (specifications call).premise (context.enter call.callSite.site call.callSite.roles) self
      (call.callSite.operands.eval environment)) :
    call.application.denote
      (participantMeaning (payload.tables F G) self (payload.protocolTable F G) context) environment =
      ((specifications call).target (context.enter call.callSite.site call.callSite.roles) self
        (call.callSite.operands.eval environment)).bind
        (fun returned => call.continuation.2.denote
          (participantMeaning (payload.tables F G) self (payload.protocolTable F G) context)
          (environment.prepend (maskValues self
            ((context.enter call.callSite.site call.callSite.roles).mapScopes call.callSite.signature.outputScopes)
            returned))) :=
  payload.protocolApply_substitute (specifications call).definition (specifications call).member
    call.callSite.signature (specifications call).sameSignature
    (specifications call).body (specifications call).exactRaw
    call.callSite.roles call.callSite.site context self call.callSite.operands call.continuation.2
    environment inside _ (resolved.resolve call _ _ _ premise)

end Zkc.Source.Structured
