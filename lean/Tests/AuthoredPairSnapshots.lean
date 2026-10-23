import Zkc.Construction.AuthoredPair
import ZkcExamples.Structured.SumcheckSourceViews
import ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs
import ZkcExamples.Construction.Generated.SmallSumcheckPair
import ZkcExamples.Construction.Generated.TwoSumsPair

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Tests.AuthoredPairSnapshots
open Zkc.Source Zkc.Source.Structured Zkc.Construction.AuthoredPair

-- These are literal exports of the actual native candidate participants.
-- Kernel checks below admit the source independently and run the deterministic
-- producer/validator association rule. They assert no producer projection law.
private def smallOriginal := ZkcExamples.Structured.SumcheckSourceData.snapshot
private def smallImported := ZkcExamples.Structured.SumcheckSourceViews.imported
private def smallArtifacts := ZkcExamples.Construction.Generated.SmallSumcheckPair.artifacts
private def smallSelection : Selection smallOriginal :=
  (select smallOriginal smallArtifacts "public_sum").toOption.get (by decide +kernel)

example : check smallImported smallSelection smallArtifacts = .ok () := by decide +kernel

private def twoOriginal := ZkcExamples.Structured.Generated.Bindings.TwoSumsData.snapshot
-- Reuse the source owner's phased kernel admission of these exact constructor
-- data. No native evaluation, hash premise or opaque receipt admits the source.
private noncomputable def twoImported : Imported twoOriginal :=
  ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs.imported
private def twoArtifacts := ZkcExamples.Construction.Generated.TwoSumsPair.artifacts
private def twoSelection : Selection twoOriginal :=
  (select twoOriginal twoArtifacts "public_sums").toOption.get (by decide +kernel)

example : check twoImported twoSelection twoArtifacts = .ok () := by decide +kernel

-- A valid producer for a different candidate is still the wrong fixed pair.
example : check smallImported smallSelection
    ⟨twoArtifacts.producer, smallArtifacts.validator⟩ = .error "authored-pair-artifacts" :=
  by decide +kernel

example : smallArtifacts.producer.instructions ≠ smallArtifacts.validator.instructions :=
  by decide +kernel
example : twoArtifacts.producer.instructions ≠ twoArtifacts.validator.instructions :=
  by decide +kernel

end Tests.AuthoredPairSnapshots
