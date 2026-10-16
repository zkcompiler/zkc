module

public import Zkc.Source.Structured.UnitViews
public import ZkcExamples.Structured.ApplicationData
public import ZkcExamples.Structured.ApplicationBodies

@[expose] public section

/-! One explicit checked candidate and one complete original admission proof.
Named signature, membership and erasure equalities keep downstream proof types
independent of repeated normalization of whole-unit admission. -/
namespace ZkcExamples.Structured.ApplicationViews
open Zkc.Source Zkc.Source.Structured ApplicationBodies

set_option smartUnfolding false

structured_views ApplicationData.snapshot
  helpers []
  protocols [step, observe, segment, run]

end ZkcExamples.Structured.ApplicationViews
