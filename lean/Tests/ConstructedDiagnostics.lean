import ZkcTools.StructuredSource.Constructed

/-! Refusals retain their stable code, complete nested source path and actual
operation/operand/result shape, including malformed supported operations. -/
namespace Tests.ConstructedDiagnostics
open Zkc.Construction ZkcTools.StructuredSource.Constructed

private def emptyIndices : Instruction := ⟨.indicesEmpty, [], [.indices], []⟩
private def unsupported : Instruction := ⟨.unsupported "diagnostic-control", [3, 7], [.indices], []⟩
private def loop (body : List Instruction) : Instruction := ⟨.loop "round" 2 [], [0], [], body⟩

private def refusal (instructions : List Instruction) : String :=
  match block 4 instructions "body" "artifact.instructions" with
  | .error reason => reason
  | .ok _ => "unexpected-success"

#guard refusal [unsupported] ==
  "constructed-view-unsupported-shape: operation=(Zkc.Construction.Operation.unsupported \"diagnostic-control\"); operands=([3, 7]); results=([Zkc.Construction.ValueSort.indices]); body-instructions=0; path=(artifact.instructions)[0]'(by decide +kernel)"

#guard (refusal [emptyIndices, unsupported]).endsWith
  "; path=(artifact.instructions)[1]'(by decide +kernel)"

#guard (refusal [loop [emptyIndices, loop [emptyIndices, unsupported]]]).endsWith
  "; path=(((((artifact.instructions)[0]'(by decide +kernel)).body)[1]'(by decide +kernel)).body)[1]'(by decide +kernel)"

#guard (refusal [⟨.indicesEmpty, [9], [.indices], [emptyIndices]⟩]).startsWith
  "constructed-view-unsupported-shape: operation=(Zkc.Construction.Operation.indicesEmpty); operands=([9]); results=([Zkc.Construction.ValueSort.indices]); body-instructions=1;"

#guard (block 4 [loop [emptyIndices]] "body" "artifact.instructions").isOk
#guard (block 0 [] "body" "artifact.instructions").toOption.isNone

end Tests.ConstructedDiagnostics
