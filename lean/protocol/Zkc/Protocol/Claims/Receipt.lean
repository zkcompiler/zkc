module

public import Zkc.Protocol.Claims.Request
public import Zkc.Protocol.Claims.Extraction
public import Zkc.Protocol.Claims.Simulation

/-!
# Typed claims and receipts

Built-in constructors fix their meaning by a property-specific request. Custom propositions
have a separate constructor. Neither an arbitrary proposition nor an attribution string can
choose the meaning of a built-in claim. A receipt permits any proof of that fixed meaning.
-/

public section

open PIR

namespace ProtocolProof

universe u

/-- Classification is derived from the typed request, not supplied by a reporting method. -/
inductive ClaimKind where
  | promiseSoundness
  | honestCompleteness
  | fixedRecovery
  | boundedExtraction
  | statisticalSimulation
  | distinguisherSimulation
  | custom
  deriving DecidableEq, Repr

/-- Each built-in claim stores its full request, including observation and resource choices. -/
inductive Claim : Type (u + 1) where
  | soundness {E O X : Type u} [MeasurableSpace O] (request : SoundnessRequest E O X)
  | completeness {E O : Type u} [MeasurableSpace O] (request : CompletenessRequest E O)
  | recovery {E O W : Type u} [MeasurableSpace O] (request : RecoveryRequest E O W)
  | extraction {P E S L W X : Type} {I : Signature}
      [∀ op, MeasurableSpace (I.Reply op)] [∀ op, Countable (I.Reply op)]
      [∀ op, MeasurableSingletonClass (I.Reply op)]
      [MeasurableSpace S] [MeasurableSpace L] [MeasurableSpace (Option W)]
      (request : ExtractionRequest P E I S L W X)
  | statisticalSimulation {P C W V S L : Type} {I : Signature}
      [∀ op, MeasurableSpace (I.Reply op)] [∀ op, Countable (I.Reply op)]
      [∀ op, MeasurableSingletonClass (I.Reply op)]
      [MeasurableSpace S] [MeasurableSpace L] [MeasurableSpace V]
      (request : StatisticalSimulationRequest P C W V I S L)
  | distinguisherSimulation {P C W V S L D : Type} {I : Signature}
      [∀ op, MeasurableSpace (I.Reply op)] [∀ op, Countable (I.Reply op)]
      [∀ op, MeasurableSingletonClass (I.Reply op)]
      [MeasurableSpace S] [MeasurableSpace L] [MeasurableSpace V]
      (request : DistinguisherSimulationRequest P C W V I S L D)
  | custom (statement : Prop)

namespace Claim

@[expose] def kind : Claim.{u} → ClaimKind
  | @Claim.soundness _ _ _ _ _ => .promiseSoundness
  | @Claim.completeness _ _ _ _ => .honestCompleteness
  | @Claim.recovery _ _ _ _ _ => .fixedRecovery
  | @Claim.extraction _ _ _ _ _ _ _ _ _ _ _ _ _ _ => .boundedExtraction
  | @Claim.statisticalSimulation _ _ _ _ _ _ _ _ _ _ _ _ _ _ => .statisticalSimulation
  | @Claim.distinguisherSimulation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => .distinguisherSimulation
  | .custom _ => .custom

/-- The schema determines the proposition. Evidence cannot replace it. -/
@[expose] def Meaning : Claim.{u} → Prop
  | @Claim.soundness _ _ _ _ request => request.Holds
  | @Claim.completeness _ _ _ request => request.Holds
  | @Claim.recovery _ _ _ _ request => request.Holds
  | @Claim.extraction _ _ _ _ _ _ _ _ _ _ _ _ _ request => request.Holds
  | @Claim.statisticalSimulation _ _ _ _ _ _ _ _ _ _ _ _ _ request => request.Holds
  | @Claim.distinguisherSimulation _ _ _ _ _ _ _ _ _ _ _ _ _ _ request => request.Holds
  | .custom statement => statement

/-- Canonical means a framework-defined schema, not approval of its application or parameters. -/
@[expose] def IsCanonical (claim : Claim.{u}) : Prop := claim.kind ≠ .custom

@[simp] theorem custom_not_canonical (statement : Prop) :
    ¬ (Claim.custom.{u} statement).IsCanonical := by
  simp [IsCanonical, kind]

end Claim

/-- Closed evidence is indexed by the complete claim, not just its human-readable property name. -/
structure Receipt (claim : Claim.{u}) : Prop where
  proof : claim.Meaning

/-- An open premise remains a premise; storing this value does not establish a closed receipt. -/
structure ConditionalReceipt (claim : Claim.{u}) (Premise : Prop) : Prop where
  proof : Premise → claim.Meaning

namespace ConditionalReceipt

variable {claim : Claim.{u}} {P Q : Prop}

/-- Discharge the premise explicitly. No proof-term route inspection is required. -/
theorem close (conditional : ConditionalReceipt claim P) (premise : P) : Receipt claim :=
  ⟨conditional.proof premise⟩

/-- Replace a premise only through a proved implication. -/
theorem of_implication (conditional : ConditionalReceipt claim P) (implication : Q → P) :
    ConditionalReceipt claim Q := ⟨conditional.proof ∘ implication⟩

end ConditionalReceipt

end ProtocolProof
