module

public import Zkc.Source.Structured.UnitViews
public import ZkcExamples.Structured.GkrSourceData
public import ZkcExamples.Structured.GkrSourceBodies

@[expose] public section

/-! Checked payload and admission phases of the retained original-stage unit,
emitted by `structured_views` from its literal typed bodies. -/
namespace ZkcExamples.Structured.GkrSourceViews
open Zkc.Source Zkc.Source.Structured

set_option smartUnfolding false
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

open ZkcExamples.Structured.GkrSourceBodies in
structured_views GkrSourceData.snapshot
  helpers [helper2, helper3, helper4, sourceHelper4, helper18, empty, append, helper5, helper6, helper7, helper15, sourceHelper19, sourceHelper20, selectBlock, helper20, helper21, helper22, helper26, helper27, helper31, sourceHelper37, sourceHelper39, sourceHelper40, helper37, helper39, helper42, sourceHelper49, sourceHelper50, helper46, helper53, helper54, helper58, helper60, helper67, sum, helper73, helper76, sourceHelper83, sourceHelper82, sourceHelper81, helper16, interpolateRealization, interpolateCallback, helper8, helper9, helper10, helper11, helper12, helper13, helper14, evaluate, helper35, evaluateWiring, sourceHelper84, scopedHelper42, scopedHelper43, scopedHelper44, scopedHelper45, helper24, helper25, scopedHelper48, helper29, helper30, helper33, helper34, helper36, scopedHelper54, scopedHelper55, scopedHelper56, scopedHelper57, scopedHelper58, scopedHelper59, helper41, lineInterpolationRealization, lineCallback, scopedHelper63, helper44, helper45, scopedHelper66, scopedHelper67, scopedHelper68, scopedHelper69, scopedHelper70, scopedHelper71, scopedHelper72, scopedHelper73, scopedHelper74, helper48, helper49, helper50, helper62, helper63, scopedHelper80, helper52, scopedHelper82, helper56, helper57, helper70, scopedHelper86, helper65, helper66, helper69, sourceHelper110, linePoint, helper74, sourceHelper112, helper75, helper78, helper43, helper80, evaluateCoefficients]
  protocols [rounds, sourceProtocol80, gkr]

theorem admitted : check GkrSourceData.snapshot = .ok program := kernel_admission

end ZkcExamples.Structured.GkrSourceViews
