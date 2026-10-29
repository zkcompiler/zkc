module

public import Tests.ConnectionLibraryBuilder
public import ZkcExamples.Structured.GkrSourceViews

@[expose] public section

/-! The same finite source-library builder handles the retained GKR declaration
closure. This checks shared source normalization and linking, not the target
alignment or GKR's mathematical properties. Keeping the result in an imported
module also exercises code generation for its noncomputable proof-data constants.
-/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
noncomputable section
namespace Tests.ConnectionGkrLibrary
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction ConnectionLibrary

abbrev payload := ZkcExamples.Structured.GkrSourceViews.program.payload

def library : Σ keys, Library payload keys := by build_test_library payload roles [0,1]

example (model : DomainModel) {types : List Ty}
    (inputs : Values (Component model.Value) types) :
    CalleesHold (Occurrence.table model payload) (library.2.processes model) inputs :=
  library.2.holds model inputs

#print axioms library
end Tests.ConnectionGkrLibrary
