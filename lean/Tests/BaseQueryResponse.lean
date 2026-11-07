module

public import Zkc.Realization.BaseQueryResponse

@[expose] public section
set_option autoImplicit false
namespace Tests.BaseQueryResponse
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Realization

def layout : RecordProjection.Layout :=
  ⟨"PublishedWord", "Record", .cons .index (.cons .index (.cons .index (.cons (.vector "F") .nil)))⟩
def selections : List (RecordProjection.Selection layout.fields) :=
  [⟨.index, .here⟩, ⟨.index, .there .here⟩, ⟨.index, .there (.there .here)⟩,
    ⟨.vector "F", .there (.there (.there .here))⟩]
def lookupPlacement : RecordLookup.Placement := ⟨13, 0, 1, 11, "constructor"⟩
def readPlacement : TableRead.Placement := ⟨20, 19, 17, 2, "rows"⟩
def responsePlacement : QueryResumption.Placement :=
  ⟨22, 6, 5, ⟨0, 1, 2, 3, 4⟩, ⟨0, 1, 2, 3, 4⟩, 8, 21,
    "phase", "kind", !["constructor", "instance", "position", "continuation", "frame"]⟩
def body :=
  RecordLookup.instructions ⟨0, layout.type⟩ lookupPlacement ++
  RecordProjection.instructions layout 15 selections ++
  QueryReadResponse.instructions "F" 0 readPlacement responsePlacement

theorem complete_arm_recognized :
    (BaseQueryResponse.recognize body).isSome = true := by decide +kernel

theorem unrelated_record_refused :
    (BaseQueryResponse.recognize
      (RecordLookup.instructions ⟨0, layout.type⟩ lookupPlacement ++
        RecordProjection.instructions layout 12 selections ++
        QueryReadResponse.instructions "F" 0 readPlacement responsePlacement)).isNone = true :=
  by decide +kernel

theorem unrelated_position_refused :
    (BaseQueryResponse.recognize
      (RecordLookup.instructions ⟨0, layout.type⟩ lookupPlacement ++
        RecordProjection.instructions layout 15 selections ++
        QueryReadResponse.instructions "F" 0 { readPlacement with position := 7 }
          responsePlacement)).isNone = true := by decide +kernel

theorem stale_answer_refused :
    (BaseQueryResponse.recognize
      (RecordLookup.instructions ⟨0, layout.type⟩ lookupPlacement ++
        RecordProjection.instructions layout 15 selections ++
        QueryReadResponse.instructions "F" 0 readPlacement
          { responsePlacement with answer := 7 })).isNone = true := by decide +kernel

#print axioms complete_arm_recognized
end Tests.BaseQueryResponse
