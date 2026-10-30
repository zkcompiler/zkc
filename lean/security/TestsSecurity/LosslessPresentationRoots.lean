module

import ZkcSecurityExamples.RootProperties.SmallSumcheck.Soundness
import ZkcSecurityExamples.RootProperties.TwoSums.Soundness

/-! Complete Domain returns, source state, incoming histories and unread proof
suffixes survive the actual generated root's public presentation. -/
set_option autoImplicit false
noncomputable section
namespace TestsSecurity.LosslessPresentationRoots
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.FiatShamir
open ZkcExamples.Structured.Generated.Connections

variable (model : DomainModel) (physical : Domain.Environment model.toCarriers)

example :
    DomainReduction.Bridge NominalDomain.interface
      (fun reached target => ∃ source, SourceReading.Post reached source ∧
        Original.CompleteReturns SmallSumcheck.program.payload.entry.signature
          SmallSumcheck.validatorRouting.context SmallSumcheck.context.validator
          SmallSumcheck.validatorArtifact source target)
      (SmallSumcheck.validator.inputs.initial physical).history
      (Domain.participant model SmallSumcheck.program SmallSumcheck.validatorRouting.context
        SmallSumcheck.validatorArtifact physical)
      (RootConnection.losslessPresentation SmallSumcheck.validator
        ZkcSecurity.Examples.RootProperties.SmallSumcheck.Soundness.supported _ rfl
        ZkcSecurity.Examples.RootProperties.SmallSumcheck.noLocal model physical) :=
  RootConnection.losslessBridge SmallSumcheck.validator
    ZkcSecurity.Examples.RootProperties.SmallSumcheck.Soundness.supported _ rfl
    ZkcSecurity.Examples.RootProperties.SmallSumcheck.noLocal model physical

variable {m : Type → Type} [Monad m]
  (query : Domain.History model.toCarriers → (event : Domain.Event model.toCarriers) → m (Domain.Raw event))
  (proof : Domain.Proof model.toCarriers)

example :
    ZkcSecurity.Endpoint.Domain.readExecution query
      (Domain.participant model TwoSums.program TwoSums.validatorRouting.context
        TwoSums.validatorArtifact physical) proof =
      Zkc.Transcript.transform NominalDomain.interface query
        (RootConnection.losslessPresentation TwoSums.validator
          ZkcSecurity.Examples.RootProperties.TwoSums.Soundness.supported _ rfl
          ZkcSecurity.Examples.RootProperties.TwoSums.noLocal model physical)
        (TwoSums.validator.inputs.initial physical).history proof :=
  RootConnection.losslessRead TwoSums.validator
    ZkcSecurity.Examples.RootProperties.TwoSums.Soundness.supported _ rfl
    ZkcSecurity.Examples.RootProperties.TwoSums.noLocal model physical query proof

#print axioms RootConnection.losslessBridge
#print axioms RootConnection.losslessRead
end TestsSecurity.LosslessPresentationRoots
