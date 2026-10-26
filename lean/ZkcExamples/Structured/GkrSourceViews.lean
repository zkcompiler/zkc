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

-- The complete source includes the prover and all private scoped callbacks.
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
structured_views ZkcExamples.Structured.GkrSourceData.snapshot
  helpers [empty, append, helper2, helper3, helper4, helper5, helper6, helper7, helper15, helper18, selectBlock, helper20, helper21, helper22, helper26, helper27, helper31, helper37, helper39, helper42, helper46, helper53, helper54, helper58, helper60, helper67, sum, helper73, helper76, helper16, interpolateRealization, interpolateCallback, helper8, helper9, helper10, helper11, helper12, helper13, helper14, evaluate, helper35, evaluateWiring, scopedHelper42, scopedHelper43, scopedHelper44, scopedHelper45, helper24, helper25, scopedHelper48, helper29, helper30, helper33, helper34, helper36, scopedHelper54, scopedHelper55, scopedHelper56, scopedHelper57, scopedHelper58, scopedHelper59, helper41, lineInterpolationRealization, lineCallback, scopedHelper63, helper44, helper45, scopedHelper66, scopedHelper67, scopedHelper68, scopedHelper69, scopedHelper70, scopedHelper71, scopedHelper72, scopedHelper73, scopedHelper74, helper48, helper49, helper50, helper62, helper63, scopedHelper80, helper52, scopedHelper82, helper56, helper57, helper70, scopedHelper86, helper65, helper66, helper69, helper77, helper74, helper75, helper78, helper79, helper80, evaluateCoefficients, helper43, linePoint]
  protocols [rounds, gkr]
end ZkcExamples.Structured.GkrSourceViews
