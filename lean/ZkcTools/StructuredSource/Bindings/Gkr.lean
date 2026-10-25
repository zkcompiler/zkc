module

public import ZkcTools.StructuredSource.Bindings.Callbacks
public import Zkc.Protocols.AlgebraicRounds.Gate

@[expose] public section

/-! Exact gate arithmetic bindings. Indices select candidate admitted helpers;
selection is not a semantic assertion. Every emitted full-body component
equation is independently checked, including every operand's order. -/

namespace ZkcTools.StructuredSource.Bindings
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm
open ZkcTools.StructuredSource.Presentation

structure GateOutput where
  valueIndex : Nat
  quadraticIndex : Nat

def gateSource (program : Program) (output : Output) (gate : GateOutput) : Except String String := do
  let some value := program.payload.definitions[gate.valueIndex]? | throw "gate-value-index"
  let some quadratic := program.payload.definitions[gate.quadraticIndex]? | throw "gate-quadratic-index"
  let [.field domain] := value.outputs | throw "gate-value-output"
  unless value.inputs == List.replicate 4 (.field domain) &&
      quadratic.inputs == List.replicate 8 (.field domain) && quadratic.outputs == value.outputs do
    throw "gate-helper-signature"
  let mut text := "module\n\npublic import " ++ output.moduleName ++ "Callbacks\n" ++
    "public import Zkc.Protocols.AlgebraicRounds.Gate\n\n@[expose] public section\n\n" ++
    "/-! Generated actual-helper gate equations. This is not a full GKR theorem. -/\nnamespace " ++ output.moduleName ++ "Gate\n" ++
    "open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm Zkc.Source.Structured.Bindings\n" ++
    "open Zkc.Protocols.AlgebraicRounds\nopen " ++ output.moduleName ++ "\nset_option maxRecDepth 50000\nset_option maxHeartbeats 8000000\n" ++
    "set_option smartUnfolding false\nnoncomputable section\n" ++
    "variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]\n\n"
  for (name, index, arguments, expression) in [
      ("value", gate.valueIndex, ["add", "mul", "left", "right"], "Gate.value add mul left right"),
      ("quadratic", gate.quadraticIndex, ["a0", "a1", "m0", "m1", "l0", "l1", "r0", "r1"],
        "Gate.quadratic a0 a1 m0 m1 l0 l1 r0 r1")] do
    let args := valuesText (arguments.map fun argument => app "some" [argument])
    let result := ".done (.cons (some (" ++ expression ++ ")) .nil)"
    let parameters := "(" ++ " ".intercalate arguments ++ " : F)"
    text := text ++ "abbrev " ++ name ++ "Definition : CheckedDefinition := payload.definitions.get ⟨" ++
      toString index ++ ", by decide +kernel⟩\n\n" ++
      "theorem " ++ name ++ "_body " ++ parameters ++ " :\n" ++
      "    " ++ name ++ "Definition.body.component\n" ++
      "      (Evaluation.meaning (.silent (participantInterface F G)) (helpers payload).closed)\n" ++
      "      (Evaluation.componentOperation (.silent _) (helpers payload)) " ++
      "(" ++ paren (args ++ " : Values (Component (assignment F G)) " ++ name ++ "Definition.inputs") ++ ".get) =\n" ++
      "      " ++ result ++ " := by\n  kernel_rfl\n\n" ++
      "theorem " ++ name ++ "_invoke " ++ parameters ++ " :\n" ++
      "    invoke (helpers (F := F) (G := G) payload).components " ++ name ++ "Definition.helper " ++ args ++ " =\n" ++
      "      " ++ result ++ " :=\n" ++
      "  (helper_body payload " ++ name ++ "Definition (List.get_mem _ _) " ++ args ++ ").trans\n" ++
      "    (" ++ name ++ "_body " ++ " ".intercalate arguments ++ ")\n\n"
  return text ++ "end\nend " ++ output.moduleName ++ "Gate\n"

end ZkcTools.StructuredSource.Bindings
