module

import all Zkc.Tests.Protocol.Construction.Sharing
import all Zkc.Tests.Protocol.Construction.SharedChallengeSource
import all Zkc.Tests.Protocol.Construction.StatefulOracle
import all Zkc.Tests.Protocol.Construction.OracleInstallation
import all Zkc.Tests.Protocol.Construction.Choices.Assembly
public meta import Zkc.Tools.Protocol.ConstructionAudit

/-! Regression limits inspect checked terms and their owner-qualified auxiliary proofs.
Only references in values count. Types, imports and arbitrary theorem dependencies do not.
This audit supplies no proof rule and is not consulted by claim acceptance. -/

meta section
open Lean Meta Elab Command ProtocolProof.Tools.ConstructionAudit

namespace ProtocolProofExamples.ConstructionSharingAudit

run_elab do
  for (owner, count, limit) in [
      (`ProtocolProofExamples.ConstructionSharing.flat1_law, 1, 1500),
      (`ProtocolProofExamples.ConstructionSharing.flat2_law, 2, 2500),
      (`ProtocolProofExamples.ConstructionSharing.flat4_law, 4, 4000),
      (`ProtocolProofExamples.ConstructionSharing.flat8_law, 8, 7000)] do
    requireUses owner `ProtocolProofExamples.ConstructionPilot.helper_law count limit
  for (owner, callee, count) in [
      (`ProtocolProofExamples.ConstructionSharing.nested1_law,
        `ProtocolProofExamples.ConstructionPilot.helper_law, 1),
      (`ProtocolProofExamples.ConstructionSharing.nested2_law,
        `ProtocolProofExamples.ConstructionSharing.nested1_law, 2),
      (`ProtocolProofExamples.ConstructionSharing.nested4_law,
        `ProtocolProofExamples.ConstructionSharing.nested2_law, 2),
      (`ProtocolProofExamples.ConstructionSharing.nested8_law,
        `ProtocolProofExamples.ConstructionSharing.nested4_law, 2)] do
    requireUses owner callee count 2500
  for owner in [
      `ProtocolProofExamples.ConstructionSharing.count0_law,
      `ProtocolProofExamples.ConstructionSharing.count1_law,
      `ProtocolProofExamples.ConstructionSharing.count8_law,
      `ProtocolProofExamples.ConstructionSharing.count1024_law] do
    requireUses owner `ProtocolProofExamples.AdaptiveSource.rounds_upper 1 1000
  for (owner, callee) in [
      (`ProtocolProofExamples.SharedChallengeSource.source_upper,
        `ProtocolProofExamples.SharedChallengeSource.query_upper),
      (`ProtocolProofExamples.SharedChallengeSource.source_lower,
        `ProtocolProofExamples.SharedChallengeSource.query_lower)] do
    requireUses owner callee 2 6000

end ProtocolProofExamples.ConstructionSharingAudit
