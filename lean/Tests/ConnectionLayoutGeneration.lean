import Tests.ConnectionLayout
import ZkcTools.ConstructionBindings.Generate

/-! Fresh generic connection generation for changed internal SSA coordinates.
Both roles use the ordinary constructed-view printer and finite root engine.
Candidate frame metadata alone never establishes the source connection. -/
set_option autoImplicit false
namespace Tests.ConnectionLayoutGeneration
open Lean Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcTools.ConstructionBindings

private def frames (artifact : Participant) : Except String (List Frames.Repeat) :=
  Frames.analyze artifact

private def checkShift (before after : Participant) : Except String Unit := do
  let original ← frames before
  let shifted ← frames after
  unless original.length == shifted.length && !original.isEmpty do throw "shifted-loop-inventory"
  for (left, right) in original.zip shifted do
    unless left.yielded != right.yielded && left.site == right.site do throw "shifted-loop-yields"
    let replace (yielded : List Nat) :=
      { after with instructions := after.instructions.mapIdx fun index instruction =>
        if right.path == [index] then
          { instruction with operation := .loop right.site right.maximum yielded }
        else instruction }
    for yielded in [right.yielded.tail, [1000000]] do
      match Frames.analyze (replace yielded) with
      | .error "construction-binding-frame-yield" => pure ()
      | _ => throw "changed-yield-accepted"

def sources : Except String (List (Name × String)) := do
  checkShift ZkcExamples.Construction.Generated.SmallSumcheckPair.Producer.participant
    Tests.ConnectionLayout.Producer.participant
  checkShift ZkcExamples.Construction.Generated.SmallSumcheckPair.Validator.participant
    Tests.ConnectionLayout.Validator.participant
  Generate.bundle
    ⟨`ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs,
      `ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs.program⟩
    `ConnectionLayoutControl.Connection [
      (⟨.producer, `Tests.ConnectionLayout, `Tests.ConnectionLayout.Producer.participant,
        `ConnectionLayoutControl.Producer⟩, Tests.ConnectionLayout.Producer.participant),
      (⟨.validator, `Tests.ConnectionLayout, `Tests.ConnectionLayout.Validator.participant,
        `ConnectionLayoutControl.Validator⟩, Tests.ConnectionLayout.Validator.participant)]

end Tests.ConnectionLayoutGeneration

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected output directory")
  let .ok sources := Tests.ConnectionLayoutGeneration.sources
    | throw (IO.userError "generic shifted-layout generation refused")
  for (name, source) in sources do
    let path := System.FilePath.mk directory / (name.toString.replace "." "/" ++ ".lean")
    IO.FS.createDirAll path.parent.get!
    IO.FS.writeFile path source
