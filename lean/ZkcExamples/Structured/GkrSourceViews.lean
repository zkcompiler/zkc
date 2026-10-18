module

public import Zkc.Source.Structured.UnitViews
public import ZkcExamples.Structured.GkrSourceData
public import ZkcExamples.Structured.GkrSourceBodies

@[expose] public section

/-! Complete checked payload and named kernel admission phases of the GKR
source, from the literal bodies of `GkrSourceBodies`. -/
namespace ZkcExamples.Structured.GkrSourceViews
open Zkc.Source Zkc.Source.Structured GkrSourceBodies

set_option smartUnfolding false

-- The unit has 83 helper bodies, the honest prover's included; checking them
-- against the snapshot exceeds the default elaboration budget.
set_option maxHeartbeats 0 in
structured_views GkrSourceData.snapshot
  helpers [empty, append, helper2, helper3, helper4, helper5, helper6, helper7, helper8, helper9, helper10, helper11, helper12, helper13, helper14, helper15, helper16, evaluate, helper18, selectBlock, helper20, helper21, helper22, helper23, helper24, helper25, helper26, helper27, helper28, helper29, helper30, helper31, helper32, helper33, helper34, helper35, helper36, helper37, helper38, helper39, helper40, helper41, helper42, helper43, helper44, helper45, helper46, helper47, helper48, helper49, helper50, helper51, helper52, helper53, helper54, helper55, helper56, helper57, helper58, helper59, helper60, helper61, helper62, helper63, helper64, helper65, helper66, helper67, helper68, helper69, helper70, sum, evaluateWiring, helper73, helper74, helper75, helper76, helper77, helper78, helper79, helper80, evaluateCoefficients, linePoint]
  protocols [rounds, gkr]

end ZkcExamples.Structured.GkrSourceViews
