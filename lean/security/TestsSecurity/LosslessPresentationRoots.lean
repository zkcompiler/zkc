module

import ZkcSecurity.FiatShamir.NominalField
import ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Soundness
import ZkcSecurity.Examples.Generated.OriginalSecurity.TwoSums.Soundness

set_option autoImplicit false
namespace TestsSecurity.LosslessPresentationRoots
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.FiatShamir
open ZkcSecurity.Families.Sumcheck TableComponent
open ZkcSecurity.Examples.Generated
open ZkcSecurity.Examples.Generated.OriginalSecurity
open ZkcSecurity.Examples.Generated.SmallSumcheck
open ZkcSecurity.Examples.Generated.Components.SmallSumcheckABI

/-- The concrete imported SmallSumcheck artifact has a full Domain.Result
presentation. The generated installation selects the actual complete return
relation, including temporary frame data; the global interface law transports it. -/
example (entries : List SmallSumcheck.Installation.Scalar) (claim : SmallSumcheck.Installation.Scalar) (count : Nat)
    (history : Domain.History SmallSumcheck.Installation.carriers) :
    ∃ after : PIR.Process (NominalField.signature SmallSumcheck.Installation.Scalar "bls12-381.fr")
        (Domain.Result SmallSumcheck.Installation.carriers),
      Original.Alignment (SmallSumcheck.Installation.installation.returns)
        (SmallSumcheck.Installation.presentedInputs entries claim count history) after ∧
      DomainReduction.Bridge (NominalField.interface (G := SmallSumcheck.Installation.Group) "bls12-381.fr")
        (fun reached result => ∃ source : ZkcSecurity.Realizations.Sumcheck.OriginalSecurity.Result
            (F := SmallSumcheck.Installation.Scalar) (G := SmallSumcheck.Installation.Group),
          (source.2.history = reached ∧ source.2.frames = []) ∧
          SmallSumcheck.Installation.installation.returns source result) history
        (Domain.participant model validatorCompiled.imported.program
          validatorCompiled.selection.context validatorArtifacts.participant
          (SmallSumcheck.Installation.publicInputs entries claim count ++
            [.transcript validatorCompiled.selection.context.suite history])) after :=
  (SmallSumcheck.Installation.bridgeInputs entries claim count history).exists_lossless_presentation
    (NominalField.lossless "bls12-381.fr")

#print axioms Original.Bridge.exists_lossless_presentation
#print axioms SmallSumcheck.Installation.bridgeInputs

end TestsSecurity.LosslessPresentationRoots
