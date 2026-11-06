module

public import Zkc.Source.DerivationLaws
public import Zkc.Source.Structured.DomainProtocolLinking
public import Zkc.Source.Structured.ProtocolAlgebra

@[expose] public section

/-! A conditional protocol law installed at the actual call. The callee
executes in its captured prefix. Role masking on either side of the call
and the algebra's application boundary remain in the generated process. -/

set_option autoImplicit false
namespace Zkc.Source.Structured
variable {V : Ty → Type} {I : PIR.Signature}

structure ProtocolLaw (algebra : ProtocolAlgebra V I) (signature : ProtocolSignature) where
  body : Region protocolDialect signature.inputs signature.outputs
  Requires : ProtocolTable V I → ProtocolContext → Nat →
    Values (Component V) signature.inputs → Prop
  reference : ProtocolTable V I → ProtocolFunction V I signature
  derives : ∀ captured context self args, Requires captured context self args →
    Region.Derivation (algebra.meaning captured context self) (fun op => .call op .done)
      body (maskValues self (context.mapScopes signature.inputScopes) args).get
      (reference captured context self args)

namespace ProtocolLaw
attribute [local implicit_reducible] CheckedProtocol.signature ProtocolOp.results
variable {algebra : ProtocolAlgebra V I} {definition : CheckedProtocol}

theorem invoke (law : ProtocolLaw algebra definition.signature)
    {inventory : List Helper} {definitions before after : List CheckedProtocol}
    (linked : ProtocolDeclarationsLinked inventory [] definitions)
    (placement : definitions = before ++ definition :: after)
    (associated : definition.raw = law.body.erase)
    (context : ProtocolContext) (self : Nat) (args : Values (Component V) definition.inputs)
    (requires : law.Requires (before.foldl algebra.extend []) context self args) :
    invokeProtocol (definitions.foldl algebra.extend []) definition.signature context self args =
      (law.reference (before.foldl algebra.extend []) context self args).bind (fun out =>
        .done (maskValues self (context.mapScopes definition.outputScopes) out)) := by
  rw [show invokeProtocol (definitions.foldl algebra.extend []) definition.signature =
    algebra.denote definition (before.foldl algebra.extend []) from
      ProtocolClosure.invoke_declaration algebra.denote linked before definition after placement]
  unfold ProtocolAlgebra.denote
  rw [NormalForm.normalizeActions_process, definition.body_eq_of_raw law.body associated]
  exact congrArg (fun p : PIR.Process I (Values (Component V) definition.outputs) =>
    p.bind (fun out => .done (maskValues self (context.mapScopes definition.outputScopes) out)))
    (law.derives _ _ _ _ requires).sound_identity

theorem applyStep (law : ProtocolLaw algebra definition.signature)
    {inventory : List Helper} {definitions before after : List CheckedProtocol}
    (linked : ProtocolDeclarationsLinked inventory [] definitions)
    (placement : definitions = before ++ definition :: after)
    (associated : definition.raw = law.body.erase)
    (context : ProtocolContext) (self : Nat) (site : String) (roles : List Nat)
    (args : Values (Component V) definition.inputs)
    (active : (context.enter site roles).contains definition.signature self = true)
    (requires : law.Requires (before.foldl algebra.extend []) (context.enter site roles) self args) :
    (algebra.meaning (definitions.foldl algebra.extend []) context self).OperationLaw
      (fun op => .call op .done) (.protocolApply definition.signature roles site) args .nil
      (algebra.application context definition.signature site
        ((law.reference (before.foldl algebra.extend []) (context.enter site roles) self args).bind
          fun out => .done (maskValues self ((context.enter site roles).mapScopes definition.outputScopes) out))) := by
  apply RegionMeaning.OperationLaw.identity
  simpa only [ProtocolAlgebra.meaning, ProtocolAlgebra.operation, active, ↓reduceIte] using
    congrArg (algebra.application context definition.signature site)
      (law.invoke linked placement associated (context.enter site roles) self args requires)

/-- An absent participant neither invokes the callee nor incurs its application effects. -/
theorem inactive (algebra : ProtocolAlgebra V I) (table : ProtocolTable V I)
    (signature : ProtocolSignature) (context : ProtocolContext) (self : Nat)
    (site : String) (roles : List Nat) (args : Values (Component V) signature.inputs)
    (absent : (context.enter site roles).contains signature self = false) :
    (algebra.meaning table context self).OperationLaw (fun op => .call op .done)
      (.protocolApply signature roles site) args .nil (.done (Values.absent V signature.outputs)) := by
  apply RegionMeaning.OperationLaw.identity
  simp only [ProtocolAlgebra.meaning, ProtocolAlgebra.operation, absent, Bool.false_eq_true, ↓reduceIte]

/-- Install an already linked call equation in the ordinary source semantics.
The occurrence supplies its actual tuple and the elected child's role map. -/
theorem ordinaryApply {model : DomainModel} {signature : ProtocolSignature}
    {observations : SiteObservations I}
    {actions : PIR.OperationInterpretation (participantInterfaceOn model.toCarriers) I}
    {helpers : Evaluation.ComponentTablesOn model.toCarriers I}
    {table : ProtocolTable model.Value I} {context : ProtocolContext} {self : Nat}
    {iterations : IterationObservations I} {site : String} {roles : List Nat}
    {args : Values (Component model.Value) signature.inputs} {reference}
    (active : (context.enter site roles).contains signature self = true)
    (selected : invokeProtocol table signature (context.enter site roles) self args = reference) :
    (participantMeaningWithOn model observations actions helpers self table context iterations).OperationLaw
      (fun op => .call op .done) (.protocolApply signature roles site) args .nil reference := by
  apply RegionMeaning.OperationLaw.identity
  simpa only [participantMeaningWithOn, protocolOperationWithOn, active, ↓reduceIte] using selected

end ProtocolLaw
end Zkc.Source.Structured
