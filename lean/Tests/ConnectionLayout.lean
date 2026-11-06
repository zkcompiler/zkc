module

public import ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs
public import ZkcExamples.Construction.Generated.SmallSumcheckPair
public import ZkcTools.ConstructionBindings.Frames

@[expose] public section

/-! A callback SSA layout control. An extra pure result shifts every computed
callback coordinate while preserving source calls, messages and query routing.
This is a candidate artifact; the generated full simulation must still check. -/
set_option autoImplicit false
namespace Tests.ConnectionLayout
open Zkc.Source Zkc.Source.Structured Zkc.Construction

noncomputable abbrev program := ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs.imported.program

/-- Insert one pure SSA result before the callback and rename every later
computed reference, including the actual loop yields. Outer references stay put. -/
def shiftCallback (artifact : Participant) : Participant := Id.run do
  let mut offset := artifact.inputs.length
  let mut instructions := []
  for instruction in artifact.instructions do
    let updated := match instruction.operation, instruction.regions with
      | .loop _ _, [region] => Id.run do
          let boundary := offset + 1 + instruction.results.length
          let shift (reference : Nat) := if boundary ≤ reference then reference + 1 else reference
          let body := region.instructions.map fun step =>
            { step with operands := step.operands.map shift }
          return { instruction with
            regions := [{ region with yielded := region.yielded.map shift, instructions := ⟨.calculate (.indexConstant 0), [], [.data .index], []⟩ :: body }] }
      | _, _ => instruction
    instructions := instructions ++ [updated]
    offset := offset + instruction.results.length
  return { artifact with instructions := instructions }

namespace Validator
def participant := shiftCallback ZkcExamples.Construction.Generated.SmallSumcheckPair.Validator.participant
end Validator
namespace Producer
def participant := shiftCallback ZkcExamples.Construction.Generated.SmallSumcheckPair.Producer.participant
end Producer

end Tests.ConnectionLayout
