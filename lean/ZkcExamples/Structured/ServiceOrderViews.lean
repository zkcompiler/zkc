module

public import Zkc.Source.Structured.UnitViews
public import ZkcExamples.Structured.ServiceOrderData
public import ZkcExamples.Structured.ServiceOrderBodies

@[expose] public section

/-! Complete original-source admission with explicit normalized candidates.
The original source order is Run, Draw; the linked order is Draw, Run. -/
namespace ZkcExamples.Structured.ServiceOrderViews
open Zkc.Source Zkc.Source.Structured ServiceOrderBodies

set_option smartUnfolding false

structured_views ServiceOrderData.snapshot
  helpers []
  protocols [draw, run]

end ZkcExamples.Structured.ServiceOrderViews
