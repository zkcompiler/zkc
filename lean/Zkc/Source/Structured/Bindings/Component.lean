module

public import Zkc.Specification
public import Zkc.Source.Structured.ProtocolContext
public import Zkc.Semantics.Interaction

@[expose] public section

/-! Deterministic binding contracts shared by independent property consumers.
The meaning is the whole open process. In particular no receive, stop, private
return component or caller context is quotiented away. -/

namespace Zkc.Source.Structured.Bindings

abbrev Meaning (I : PIR.Signature) (Input Output : Type) :=
  ProtocolContext → Input → PIR.Process I Output

/-- Caller facts are explicit parameters; neither target truth nor honesty of
received messages is introduced by this contract. -/
def Contract {I : PIR.Signature} {Input Output : Type}
    (pre : ProtocolContext → Input → Prop) (view : Meaning I Input Output)
    (actual : Meaning I Input Output) : Prop :=
  ∀ context input, pre context input → actual context input = view context input

/-- The existing certificate is the sole source-conformance carrier. -/
theorem certificate {Raw Program Error : Type} {decode : Raw → Except Error Program}
    {raw : Raw} (source : Zkc.Verification.Imported decode raw)
    {I : PIR.Signature} {Input Output : Type}
    (denote : Program → Meaning I Input Output)
    (pre : ProtocolContext → Input → Prop) (view : Meaning I Input Output)
    (equation : ∀ context input, pre context input →
      denote source.program context input = view context input) :
    Zkc.Verification.Certificate source denote (Contract pre view) := ⟨equation⟩

/-- A family theorem about this very process transports without any change of
experiment. The property may inspect effects, stops and complete returned state. -/
theorem consumer {I : PIR.Signature} {Input Output : Type}
    (pre : ProtocolContext → Input → Prop) (view : Meaning I Input Output)
    (property : Zkc.Verification.Property (Meaning I Input Output))
    (proved : ∀ actual, Contract pre view actual →
      property.assumptions actual → property.conclusion actual) :
    Zkc.Verification.Consumer (Contract pre view) property := ⟨proved⟩

/-- Both readings use one equation. No independence between their experiments
is needed or asserted. -/
theorem both {I : PIR.Signature} {Input Output : Type}
    {pre : ProtocolContext → Input → Prop} {view actual : Meaning I Input Output}
    (binding : Contract pre view actual)
    (first second : PIR.Process I Output → Prop)
    (context : ProtocolContext) (input : Input) (admitted : pre context input)
    (firstProof : first (view context input)) (secondProof : second (view context input)) :
    first (actual context input) ∧ second (actual context input) := by
  rw [binding context input admitted]
  exact ⟨firstProof, secondProof⟩

end Zkc.Source.Structured.Bindings
