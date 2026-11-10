module

import all Zkc.Tests.Verification.Construction.ActualCalls
public meta import Zkc.Tools.Protocol.ConstructionAudit

/-! Two actual invocations must reference one checked mathematical law twice. A successful
root obtained solely by unfolding the helper would not demonstrate author-side reuse. -/

meta section
open ProtocolProof.Tools.ConstructionAudit

run_elab do
  requireUses `ActualSourceConstruction.Twice.participant_law
    `ActualSourceConstruction.Twice.difference_law 2 30000

construction_metrics ActualSourceConstruction.Twice.participant_law
  using ActualSourceConstruction.Twice.difference_law
