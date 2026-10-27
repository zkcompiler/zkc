module

public import ZkcTools.ConstructionBindings.Analysis

@[expose] public section

/-! Controls for untrusted source/SSA layout proposals. Callers supply the
production selections; this test owns no root or mathematical installation. -/
set_option autoImplicit false
namespace Tests.ConstructionBindingsAnalysis
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcTools.ConstructionBindings

def refusal {α : Type} (label expected : String) (result : Except String α) : IO Unit :=
  match result with
  | .error reason => unless reason == expected do throw (IO.userError (label ++ ": " ++ reason))
  | .ok _ => throw (IO.userError (label ++ ": accepted"))

def accepted {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

def run (program : Program) (validator producer : Participant) : IO Unit := do
  let layout ← accepted (analyze program validator)
  let produced ← accepted (analyzeWithContext program layout.context producer)
  unless layout.calls.map (·.application) == produced.calls.map (·.application) do
    throw (IO.userError "role source associations")
  refusal "missing source root" "construction-binding-source-root"
    (analyzeWithContext program { layout.context with entry := "absent" } validator)
  refusal "missing source delivery" "construction-binding-source-delivery"
    (analyzeWithContext program (layout.context.mapReplacement (fun replacement => { replacement with draws := [] })) validator)
  refusal "absent association" "construction-binding-test" (unique "test" ([] : List Nat))
  refusal "ambiguous association" "construction-binding-test" (unique "test" [0, 0])
  refusal "missing artifact loop" "construction-binding-call-order"
    (analyzeWithContext program layout.context { validator with instructions := [] })
  refusal "forward result reference" "construction-binding-return-reference"
    (analyzeWithContext program layout.context { validator with returned := [layout.arity] })
  let some first := validator.instructions.head? | throw (IO.userError "empty artifact")
  refusal "unclaimed region" "construction-binding-unclaimed-region"
    (analyzeWithContext program layout.context
      { validator with instructions := { first with body := [first] } :: validator.instructions.tail })
  refusal "forward operand" "construction-binding-forward-reference"
    (analyzeWithContext program layout.context
      { validator with instructions := { first with operands := [validator.inputs.length] } :: validator.instructions.tail })
  let some loop := layout.loops.head? | throw (IO.userError "no source loop")
  let rewritten := validator.instructions.mapIdx fun index instruction =>
    if index == loop.instruction then { instruction with body := [] } else instruction
  refusal "erased nominal path" "construction-binding-loop-source-association"
    (analyzeWithContext program layout.context { validator with instructions := rewritten })
  -- Instruction count is deliberately not an analysis authority. This proposal
  -- is still obliged to pass the full generated callback equation/simulation.
  let longer := validator.instructions.mapIdx fun index instruction =>
    if index == loop.instruction then
      { instruction with body := instruction.body ++ [⟨.calculate (.booleanConstant true), [], [.data .boolean], []⟩] }
    else instruction
  let _ ← accepted (analyzeWithContext program layout.context { validator with instructions := longer })
  if let [left, right] := layout.loops then
    let swapped := validator.instructions.mapIdx fun index instruction =>
      if index == left.instruction then { instruction with body := right.body }
      else if index == right.instruction then { instruction with body := left.body }
      else instruction
    refusal "source call order" "construction-binding-call-order"
      (analyzeWithContext program layout.context { validator with instructions := swapped })
  IO.println "PASS construction-binding source/SSA controls"

end Tests.ConstructionBindingsAnalysis
