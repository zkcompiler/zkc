module

public import ZkcExamples.Structured.Generated.Presentations.Gkr
public meta import ZkcTools.StructuredSource.ProcessReference

@[expose] public section

/-! Complete process references derived from the checked source equations.
Each certificate is shared by its readable value and correspondence theorem.
Roster and protocol masking premises remain on those theorems. -/

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

open Zkc.Source Zkc.Source.Structured

namespace ZkcSecurity.Realizations.Gkr.HonestProducerSource

source_reference roundsPresentation from_equation
  @ZkcExamples.Structured.Generated.Presentations.Gkr.Rounds.proverRounds_observed
  using [] atoms [invoke, denoteRepeatOn]

source_reference rootPresentation from_equation
  @ZkcExamples.Structured.Generated.Presentations.Gkr.Root.prover_observed
  using [] atoms [invoke, denoteRepeatOn]

source_reference layerPresentation from_equation
  @ZkcExamples.Structured.Generated.Presentations.Gkr.Root.proverLayer_observed
  using [ZkcExamples.Structured.Generated.Presentations.Gkr.Root.proverLayerForm,
    zkc_source_structure] atoms [invoke, denoteRepeatOn, invokeProtocol]

end ZkcSecurity.Realizations.Gkr.HonestProducerSource

namespace ZkcSecurity.Realizations.Gkr.CanonicalVerifier

source_reference roundsPresentation from_equation
  @ZkcExamples.Structured.Generated.Presentations.Gkr.Rounds.verifierRounds_observed
  using [ZkcExamples.Structured.Generated.Presentations.Gkr.Rounds.verifierRoundsForm,
    zkc_source_structure] atoms [invoke, denoteRepeatOn, invokeProtocol]

source_reference rootPresentation from_equation
  @ZkcExamples.Structured.Generated.Presentations.Gkr.Root.verifier_observed
  using [ZkcExamples.Structured.Generated.Presentations.Gkr.Root.verifierForm,
    zkc_source_structure] atoms [invoke, denoteRepeatOn, invokeProtocol]

source_reference layerPresentation from_equation
  @ZkcExamples.Structured.Generated.Presentations.Gkr.Root.verifierLayer_observed
  using [ZkcExamples.Structured.Generated.Presentations.Gkr.Root.verifierLayerForm,
    zkc_source_structure] atoms [invoke, denoteRepeatOn, invokeProtocol]

source_reference inputPresentation from_equation
  @ZkcExamples.Structured.Generated.Presentations.Gkr.Input.verifier_observed
  using [ZkcExamples.Structured.Generated.Presentations.Gkr.Input.verifierForm,
    zkc_source_structure] atoms [invoke, denoteRepeatOn, invokeProtocol]

end ZkcSecurity.Realizations.Gkr.CanonicalVerifier
