module

public import ZkcSecurity.Realizations.Sumcheck.OriginalProducer

@[expose] public section

/-! Read typed callback outputs from actual artifact yields. These checks are
independent of proof proposal and code generation. -/
set_option autoImplicit false
namespace ZkcSecurity.Realizations.Sumcheck.ArtifactOutputs
open Zkc.Source Zkc.Source.Structured Zkc.Construction

/-- Recover the exact callback yield coordinates and their nominal sorts from
an actual loop. Capture sorts are the input frame, independently of the yields.
The result is untrusted layout data, never a callback correspondence proof. -/
def loopYieldLayout (artifact : Participant) (index : Nat) :
    Except String (List Nat × List ValueSort) := do
  let some instruction := artifact.instructions[index]?
    | throw "construction-binding-loop-index"
  let .loop _ _ yielded := instruction.operation
    | throw "construction-binding-loop-operation"
  let captured := (artifact.instructions.take index).foldl
    (fun frame step => frame ++ step.results) artifact.inputs
  let count :: initial := instruction.operands
    | throw "construction-binding-loop-operands"
  unless captured[count]? == some (.data .index) do
    throw "construction-binding-loop-count-sort"
  let some initialSorts := initial.mapM (captured[·]?)
    | throw "construction-binding-loop-initial-reference"
  unless initialSorts == instruction.results do
    throw "construction-binding-loop-initial-sort"
  let final := instruction.body.foldl (fun frame step => frame ++ step.results)
    (captured ++ .data .index :: instruction.results)
  let some sorts := yielded.mapM (final[·]?)
    | throw "construction-binding-loop-yield-reference"
  unless sorts == instruction.results do
    throw "construction-binding-loop-yield-sort"
  return (yielded, sorts)

def verifierOutputs (suite : String) (artifact : Participant) (index : Nat) :
    Except String (ZkcSecurity.Realizations.Sumcheck.ArtifactBinding.VerifierOutputs suite) := do
  let (yielded, sorts) ← loopYieldLayout artifact index
  let some outputs := ZkcSecurity.Realizations.Sumcheck.ArtifactBinding.VerifierOutputs.ofYields suite yielded sorts
    | throw "construction-binding-verifier-output-abi"
  return outputs

def producerOutputs (suite : String) (artifact : Participant) (index : Nat) :
    Except String (ZkcSecurity.Realizations.Sumcheck.OriginalProducer.Outputs suite) := do
  let (yielded, sorts) ← loopYieldLayout artifact index
  let some outputs := ZkcSecurity.Realizations.Sumcheck.OriginalProducer.Outputs.ofYields suite yielded sorts
    | throw "construction-binding-producer-output-abi"
  return outputs

end ZkcSecurity.Realizations.Sumcheck.ArtifactOutputs
