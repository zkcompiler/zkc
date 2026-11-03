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
  helpers [helper0, helper1, helper2, helper3, helper4, empty, append, helper7, helper8, helper9, helper10, helper11, helper12, selectBlock, helper14, helper15, helper16, helper17, helper18, helper19, helper20, helper21, helper22, helper23, helper24, helper25, helper26, helper27, helper28, helper29, helper30, helper31, helper32, helper33, sum, helper35, helper36, helper37, helper38, helper39, helper40, helper41, helper42, helper43, helper44, helper45, helper46, helper47, helper48, helper49, helper50, evaluate, helper52, evaluateWiring, helper54, helper55, helper56, helper57, helper58, helper59, helper60, helper61, helper62, helper63, helper64, helper65, helper66, helper67, helper68, helper69, helper70, helper71, helper72, helper73, helper74, helper75, helper76, helper77, helper78, helper79, helper80, helper81, helper82, helper83, helper84, helper85, helper86, helper87, helper88, helper89, helper90, helper91, helper92, helper93, helper94, helper95, helper96, helper97, helper98, helper99, helper100, helper101, helper102, helper103, linePoint, helper105, helper106, helper107, helper108, helper109, helper110, evaluateCoefficients]
  protocols [rounds, input, gkr]

theorem admitted : check GkrSourceData.snapshot = .ok program := kernel_admission

end ZkcExamples.Structured.GkrSourceViews
