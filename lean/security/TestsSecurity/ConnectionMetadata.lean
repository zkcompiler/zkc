module

import Tests.ConstructionBindingsAnalysis
meta import Tests.ConstructionBindingsAnalysis
import ZkcSecurity.Generation.Roots.Catalogue
meta import ZkcSecurity.Generation.Roots.Catalogue

/-! Static accounting proposals remain separate from semantic connections.
The production selections exercise all retained source/SSA refusal controls. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 50000
namespace TestsSecurity.ConnectionMetadata
run_cmd do
  for root in ← ZkcSecurity.Generation.Roots.evaluateSelections do
    let .ok program := Zkc.Source.Structured.check root.snapshot
      | Lean.throwError "source admission"
    Tests.ConstructionBindingsAnalysis.run program root.artifacts.validator root.artifacts.producer
end TestsSecurity.ConnectionMetadata
