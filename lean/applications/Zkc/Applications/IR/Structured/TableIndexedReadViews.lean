module

public import Zkc.IR.Source.Structured.UnitViews
public import Zkc.Applications.IR.Structured.TableIndexedReadData
public import Zkc.Applications.IR.Structured.TableIndexedReadBodies

@[expose] public section

/-! Exact whole-unit admission of the retained indexed-read subject, including
the callback's checked-read premise and the original realization. -/
namespace ZkcExamples.Structured.TableIndexedReadViews
open Zkc.Source Zkc.Source.Structured TableIndexedReadBodies

set_option smartUnfolding false

structured_views TableIndexedReadData.snapshot
  helpers [readDecision, readStep, indexedRead, realization, formula, checkRead]
  protocols [run]

namespace Associations
structured_associations TableIndexedReadViews
  [readDecision, readStep, indexedRead, realization, formula, checkRead]
end Associations

end ZkcExamples.Structured.TableIndexedReadViews
