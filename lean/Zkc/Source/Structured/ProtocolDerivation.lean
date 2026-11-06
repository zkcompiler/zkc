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

/-- Inside an admitted body the full immutable table agrees with the captured
prefix on every callee the body can actually name, including its callbacks.
This applies to both the ordinary and the oracle-aware protocol algebra. -/
theorem ProtocolAlgebra.invokeBody (algebra : ProtocolAlgebra V I)
    {inventory : List Helper} {definitions : List CheckedProtocol}
    (linked : ProtocolDeclarationsLinked inventory [] definitions)
    (definition : CheckedProtocol) (member : definition ∈ definitions)
    (context : ProtocolContext) (self : Nat) (args : Values (Component V) definition.inputs) :
    invokeProtocol (definitions.foldl algebra.extend []) definition.signature context self args =
      algebra.denote definition (definitions.foldl algebra.extend []) context self args := by
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp member
  rw [show invokeProtocol (definitions.foldl algebra.extend []) definition.signature =
    algebra.denote definition (before.foldl algebra.extend []) from
      ProtocolClosure.invoke_declaration algebra.denote linked before definition after split]
  unfold ProtocolAlgebra.denote
  apply congrArg (fun p : PIR.Process I (Values (Component V) definition.outputs) =>
    p.bind (fun out => .done (maskValues self (context.mapScopes definition.outputScopes) out)))
  let env : Environment (Component V) definition.inputs :=
    (maskValues self (context.mapScopes definition.inputScopes) args).get
  refine (NormalForm.normalizeActions_process (algebra.meaning (before.foldl algebra.extend []) context self)
    definition.body env).trans (Eq.trans ?_ (NormalForm.normalizeActions_process
      (algebra.meaning (definitions.foldl algebra.extend []) context self) definition.body env).symm)
  apply congrFun
  apply Region.denote_congr
  intro op used
  funext operands callbacks
  cases op with
  | protocolApply signature roles site =>
    have usedRaw : signature ∈ definition.protocols := by
      simpa only [CheckedProtocol.protocols, ← definition.exactBody] using
        (List.mem_flatMap.mpr ⟨_, used, by simp [ProtocolOp.protocols]⟩ :
          signature ∈ definition.body.erase.operations.flatMap ProtocolOp.protocols)
    have inPrefix : signature ∈ before.map CheckedProtocol.signature := by
      rw [split] at linked
      have tail := (ProtocolDeclarationsLinked.append _ [] before (definition :: after)).mp linked |>.2
      simpa using tail.2.2.1 signature usedRaw
    have agrees : invokeProtocol (before.foldl algebra.extend []) signature =
        invokeProtocol (definitions.foldl algebra.extend []) signature :=
      ProtocolClosure.prefix_agrees algebra.denote linked before (definition :: after) split signature inPrefix
    simp only [ProtocolAlgebra.operation, agrees]
  | «repeat» spec site => cases operands; rfl
  | restrict _ _ =>
    cases operands with | cons value rest => cases rest; rfl
  | mark _ => cases operands; rfl
  | assemble | calculate | localCall | oracle | query | draw | exchange | guard | statement => rfl

/-- Present an installed invocation at one reached environment. The source
owns both role masks and the normalization of its selected definition. -/
theorem ProtocolAlgebra.invokePresented (algebra : ProtocolAlgebra V I)
    {inventory : List Helper} {definitions : List CheckedProtocol}
    (linked : ProtocolDeclarationsLinked inventory [] definitions)
    (definition : CheckedProtocol) (member : definition ∈ definitions)
    (context : ProtocolContext) (self : Nat) (args : Values (Component V) definition.inputs)
    (presented : PIR.Process I (Values (Component V) definition.outputs))
    (body : definition.body.denote (algebra.meaning (definitions.foldl algebra.extend []) context self)
      (maskValues self (context.mapScopes definition.inputScopes) args).get = presented) :
    invokeProtocol (definitions.foldl algebra.extend []) definition.signature context self args =
      presented.bind fun out ↦ .done (maskValues self (context.mapScopes definition.outputScopes) out) := by
  rw [algebra.invokeBody linked definition member]
  unfold ProtocolAlgebra.denote
  exact congrArg (fun p : PIR.Process I (Values (Component V) definition.outputs) ↦
    p.bind fun out ↦ .done (maskValues self (context.mapScopes definition.outputScopes) out))
    ((NormalForm.normalizeActions_process _ _ _).trans body)

/-- An active call selects the linked table at the site and role map written
in the caller. This equation composes with a body law at that environment. -/
theorem ProtocolAlgebra.applyActive (algebra : ProtocolAlgebra V I) (table : ProtocolTable V I)
    (signature : ProtocolSignature) (context : ProtocolContext) (self : Nat)
    (site : String) (roles : List Nat) (args : Values (Component V) signature.inputs)
    (active : (context.enter site roles).contains signature self = true) :
    (algebra.meaning table context self).OperationLaw (fun op ↦ .call op .done)
      (.protocolApply signature roles site) args .nil
      (algebra.application context signature site
        (invokeProtocol table signature (context.enter site roles) self args)) := by
  apply RegionMeaning.OperationLaw.identity
  simp only [ProtocolAlgebra.meaning, ProtocolAlgebra.operation, active, ↓reduceIte]

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

/-- Select a law by exact admitted member and erased body. Every callee in
its derivation may itself be selected by membership in this same unit. -/
theorem invokeMember (law : ProtocolLaw algebra definition.signature)
    {inventory : List Helper} {definitions : List CheckedProtocol}
    (linked : ProtocolDeclarationsLinked inventory [] definitions)
    (member : definition ∈ definitions) (associated : definition.raw = law.body.erase)
    (context : ProtocolContext) (self : Nat) (args : Values (Component V) definition.inputs)
    (requires : law.Requires (definitions.foldl algebra.extend []) context self args) :
    invokeProtocol (definitions.foldl algebra.extend []) definition.signature context self args =
      (law.reference (definitions.foldl algebra.extend []) context self args).bind (fun out =>
        .done (maskValues self (context.mapScopes definition.outputScopes) out)) := by
  apply algebra.invokePresented linked definition member
  rw [definition.body_eq_of_raw law.body associated]
  exact (law.derives _ _ _ _ requires).sound_identity

theorem applyMember (law : ProtocolLaw algebra definition.signature)
    {inventory : List Helper} {definitions : List CheckedProtocol}
    (linked : ProtocolDeclarationsLinked inventory [] definitions)
    (member : definition ∈ definitions) (associated : definition.raw = law.body.erase)
    (context : ProtocolContext) (self : Nat) (site : String) (roles : List Nat)
    (args : Values (Component V) definition.inputs)
    (active : (context.enter site roles).contains definition.signature self = true)
    (requires : law.Requires (definitions.foldl algebra.extend []) (context.enter site roles) self args) :
    (algebra.meaning (definitions.foldl algebra.extend []) context self).OperationLaw
      (fun op => .call op .done) (.protocolApply definition.signature roles site) args .nil
      (algebra.application context definition.signature site
        ((law.reference (definitions.foldl algebra.extend []) (context.enter site roles) self args).bind
          fun out => .done (maskValues self ((context.enter site roles).mapScopes definition.outputScopes) out))) := by
  apply RegionMeaning.OperationLaw.identity
  simpa only [ProtocolAlgebra.meaning, ProtocolAlgebra.operation, active, ↓reduceIte] using
    congrArg (algebra.application context definition.signature site)
      (law.invokeMember linked member associated (context.enter site roles) self args requires)

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
