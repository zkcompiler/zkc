import ZkcExamples.Structured.Generated.Connections.ChaumPedersen
import ZkcExamples.Structured.Generated.Connections.Okamoto

/-! Different retained Sigma families use only artifact/source selections and
the same finite root proposer. These are all-replies structural connections;
knowledge meaning and the fixed extractor remain separate property contracts. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace Tests.RetainedSigmaConnections
open Zkc.Source Zkc.Source.Structured Zkc.Construction ConnectionRoot
open ZkcTools.ConstructionBindings

namespace ChaumPedersen
open ZkcExamples.Structured.Generated.Connections.ChaumPedersen
abbrev artifact := validatorArtifact
abbrev connected := validator

example (model : DomainModel) (physical : Domain.Environment model.toCarriers) :
    Original.Simulation (Original.CompleteReturns program.payload.entry.signature context 1 artifact)
      (InputFrames connected.inputs.abi program.payload.entry.inputs physical)
      (connected.source model physical)
      (Domain.participant model program context artifact physical) := connected.simulation model physical

#print axioms connected
end ChaumPedersen

namespace Okamoto
open ZkcExamples.Structured.Generated.Connections.Okamoto
abbrev artifact := validatorArtifact
abbrev connected := validator

example (model : DomainModel) (physical : Domain.Environment model.toCarriers) :
    Original.Simulation (Original.CompleteReturns program.payload.entry.signature context 1 artifact)
      (InputFrames connected.inputs.abi program.payload.entry.inputs physical)
      (connected.source model physical)
      (Domain.participant model program context artifact physical) := connected.simulation model physical

#print axioms connected
end Okamoto

end Tests.RetainedSigmaConnections
