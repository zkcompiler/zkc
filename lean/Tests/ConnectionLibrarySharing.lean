module

public import Tests.ConnectionLibraryBuilder

@[expose] public section

/-! Imported libraries must retain reducible keys and checked body references.
The same library is reused for several calls without rerunning discovery. -/
set_option autoImplicit false
noncomputable section
namespace Tests.ConnectionLibrarySharing
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction ConnectionLibrary
open Tests.ConnectionLibraryBuilder

example : smallLibrary.1.length = 2 := by decide +kernel
example : twoLibrary.1.map (·.role) = [1, 0] := by decide +kernel

example (model : DomainModel) {types : List Ty}
    (inputs : Values (Component model.Value) types) :
    CalleesHold
      (Occurrence.table model ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs.program.payload)
      (twoLibrary.2.processes model) inputs :=
  twoLibrary.2.holds model inputs

end Tests.ConnectionLibrarySharing
