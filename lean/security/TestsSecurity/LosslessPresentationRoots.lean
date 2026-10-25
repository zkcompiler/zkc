module

import ZkcSecurity.Families.Sumcheck.TableComponentNominalLossless
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
presentation. Its existing RootReturns and temporary frame data are unchanged;
the only new input is the globally proved nominal interface law. -/
example (entries : List SmallSumcheck.Installation.Scalar) (claim : SmallSumcheck.Installation.Scalar) (count : Nat)
    (history : Domain.History SmallSumcheck.Installation.carriers) :
    ∃ after : PIR.Process (Nominal.signature SmallSumcheck.Installation.Scalar "bls12-381.fr")
        (Domain.Result SmallSumcheck.Installation.carriers),
      Original.Alignment (ZkcSecurity.Realizations.Sumcheck.ArtifactRoot.ValidatorReturns OriginalArtifacts.SmallSumcheck.context 8 7)
        (SmallSumcheck.Installation.presentedInputs entries claim count history) after ∧
      DomainReduction.Bridge (Nominal.interface (G := SmallSumcheck.Installation.Group) "bls12-381.fr")
        (fun reached result => ∃ source : ZkcSecurity.Realizations.Sumcheck.OriginalSecurity.Result
            (F := SmallSumcheck.Installation.Scalar) (G := SmallSumcheck.Installation.Group),
          (source.2.history = reached ∧ source.2.frames = []) ∧
          ZkcSecurity.Realizations.Sumcheck.ArtifactRoot.ValidatorReturns OriginalArtifacts.SmallSumcheck.context 8 7 source result) history
        (Domain.participant model validatorCompiled.imported.program
          validatorCompiled.selection.context validatorArtifacts.participant
          (SmallSumcheck.Installation.publicInputs entries claim count ++
            [.transcript validatorCompiled.selection.context.suite history])) after :=
  (SmallSumcheck.Installation.bridgeInputs entries claim count history).exists_lossless_presentation
    (Nominal.lossless "bls12-381.fr")

#print axioms Original.Bridge.exists_lossless_presentation
#print axioms SmallSumcheck.Installation.bridgeInputs

end TestsSecurity.LosslessPresentationRoots
