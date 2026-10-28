module

public import ZkcExamples.Structured.Generated.Connections.SmallSumcheck
public import ZkcExamples.Structured.Generated.Connections.TwoSums
public import ZkcSecurity.FiatShamir.RootConnectionEndpoint

@[expose] public section

/-! Consume the generated complete connections across the package boundary.
The public reading and observation coherence use the same generated root as
full-value simulation and independent coverage. Source-pair mathematics and
canonical property receipts remain separate consumers. -/
set_option autoImplicit false
noncomputable section
namespace TestsSecurity.GeneratedRootConnections
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured.Generated.Connections
open ZkcSecurity.FiatShamir Zkc.Transcript
open ConnectionOutputSelection

theorem smallNoLocal : SmallSumcheck.validatorRouting.locals = [] := by decide +kernel
theorem twoNoLocal : TwoSums.validatorRouting.locals = [] := by decide +kernel

variable (model : DomainModel) (physical : Domain.Environment model.toCarriers)

def smallBridge := RootConnection.publicBridge SmallSumcheck.validator _ rfl smallNoLocal model physical
def twoBridge := RootConnection.publicBridge TwoSums.validator _ rfl twoNoLocal model physical

theorem smallCoherence :
    DomainReduction.CoherentTo
      (fun reached target => ∃ source, SourceReading.Post reached source ∧
        Original.CompleteReturns SmallSumcheck.program.payload.entry.signature
          SmallSumcheck.validatorRouting.context SmallSumcheck.context.validator SmallSumcheck.validatorArtifact source target)
      (SmallSumcheck.validator.inputs.initial physical).history
      (Domain.participant model SmallSumcheck.program SmallSumcheck.validatorRouting.context
        SmallSumcheck.validatorArtifact physical) :=
  RootConnection.publicCoherent SmallSumcheck.validator _ rfl smallNoLocal model physical
theorem twoCoherence :
    DomainReduction.CoherentTo
      (fun reached target => ∃ source, SourceReading.Post reached source ∧
        Original.CompleteReturns TwoSums.program.payload.entry.signature
          TwoSums.validatorRouting.context TwoSums.context.validator TwoSums.validatorArtifact source target)
      (TwoSums.validator.inputs.initial physical).history
      (Domain.participant model TwoSums.program TwoSums.validatorRouting.context
        TwoSums.validatorArtifact physical) :=
  RootConnection.publicCoherent TwoSums.validator _ rfl twoNoLocal model physical

def smallCoverage := SmallSumcheck.validatorFacts.coverage model physical
def twoCoverage := TwoSums.validatorFacts.coverage model physical

variable {m : Type → Type} [Monad m] [LawfulMonad m]
  (oracle : Domain.History model.toCarriers → (event : Domain.Event model.toCarriers) →
    m (Domain.Raw event)) (proof : Domain.Proof model.toCarriers)

theorem smallReading :
    (fun result => (mapOutcome (fun target => some target.values) result.1, result.2)) <$>
      ZkcSecurity.Endpoint.Domain.readExecution oracle
        (Domain.participant model SmallSumcheck.program SmallSumcheck.validatorRouting.context
          SmallSumcheck.validatorArtifact physical) proof =
    (fun result => (mapOutcome (encodedValues SmallSumcheck.program.payload.entry.signature
        SmallSumcheck.validatorRouting.context SmallSumcheck.context.validator) result.1, result.2)) <$>
      transform NominalDomain.interface oracle
        (RootConnection.publicPresentation SmallSumcheck.validator model physical)
        (SmallSumcheck.validator.inputs.initial physical).history proof :=
  RootConnection.publicReadValues SmallSumcheck.validator _ rfl smallNoLocal model physical oracle proof
theorem twoReading :
    (fun result => (mapOutcome (fun target => some target.values) result.1, result.2)) <$>
      ZkcSecurity.Endpoint.Domain.readExecution oracle
        (Domain.participant model TwoSums.program TwoSums.validatorRouting.context
          TwoSums.validatorArtifact physical) proof =
    (fun result => (mapOutcome (encodedValues TwoSums.program.payload.entry.signature
        TwoSums.validatorRouting.context TwoSums.context.validator) result.1, result.2)) <$>
      transform NominalDomain.interface oracle
        (RootConnection.publicPresentation TwoSums.validator model physical)
        (TwoSums.validator.inputs.initial physical).history proof :=
  RootConnection.publicReadValues TwoSums.validator _ rfl twoNoLocal model physical oracle proof

#print axioms smallBridge
#print axioms twoBridge
#print axioms smallCoherence
#print axioms twoCoherence
#print axioms smallCoverage
#print axioms twoCoverage
#print axioms smallReading
#print axioms twoReading
end TestsSecurity.GeneratedRootConnections
