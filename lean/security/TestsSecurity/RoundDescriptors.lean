module

public import ZkcSecurity.Generation.RoundDescriptors
public import ZkcSecurity.Examples.Generated.Components.SmallSumcheckRounds
public import ZkcSecurity.Examples.Generated.Components.TwoSumsRounds

@[expose] public section

/-! Actual-pair discovery and refusal controls. These expected coordinates are
test assertions, not generator configuration or root authoring obligations. -/
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace TestsSecurity.RoundDescriptors
open Zkc.Construction ZkcSecurity.Generation.RoundDescriptors
namespace Small
open ZkcExamples.Construction.Generated.SmallSumcheckPair
abbrev producer := Producer.participant
abbrev validator := Validator.participant
end Small
namespace Two
open ZkcExamples.Construction.Generated.TwoSumsPair
abbrev producer := Producer.participant
abbrev validator := Validator.participant
end Two

def accepted (producer validator : Participant) : Bool :=
  match discover producer validator with | .ok _ => true | .error _ => false

def modifyLoop (artifact : Participant) (transform : Instruction → Instruction) : Participant :=
  match loops artifact with
  | [] => artifact
  | loop :: _ => { artifact with instructions := artifact.instructions.modify loop.index transform }

def duplicateQuery (artifact : Participant) : Participant :=
  match loops artifact with
  | first :: second :: _ =>
      let instructions := artifact.instructions.modify second.index
        (fun instruction => { instruction with body := (first.instruction artifact).body })
      { artifact with instructions := instructions }
  | _ => artifact

def refusal (producer validator : Participant) : Option String :=
  match discover producer validator with | .ok _ => none | .error reason => some reason

example : (discover Small.producer Small.validator).toOption.map List.length = some 1 := by decide +kernel
example : (discover Two.producer Two.validator).toOption.map List.length = some 2 := by decide +kernel
example : (loops Small.producer).map (fun loop => (loop.index, loop.capture)) = [(10, 13)] := by decide +kernel
example : (loops Small.validator).map (fun loop => (loop.index, loop.capture)) = [(1, 5)] := by decide +kernel
example : (loops Two.producer).map (fun loop => (loop.index, loop.capture)) = [(10, 14), (21, 29)] := by decide +kernel
example : (loops Two.validator).map (fun loop => (loop.index, loop.capture)) = [(1, 7), (4, 12)] := by decide +kernel

-- Counts, missing query shapes, nested bodies and mismatched source sites.
example : accepted { Small.producer with instructions := [] } Small.validator = false := by decide +kernel
example : accepted Small.producer Two.validator = false := by decide +kernel
example : accepted (modifyLoop Small.producer fun loop => { loop with body := [] }) Small.validator = false := by decide +kernel
example : accepted Small.producer (modifyLoop Small.validator fun loop => { loop with body := [] }) = false := by decide +kernel
example : accepted (modifyLoop Small.producer fun loop =>
    { loop with body := loop.body.modify 0 fun call => { call with body := [call] } })
    Small.validator = false := by decide +kernel
example : accepted (modifyLoop Small.producer fun loop =>
    { loop with operation := .loop "wrong-source-repeat" 2 [34, 35, 36, 37, 33] })
    Small.validator = false := by decide +kernel
example : accepted (modifyLoop Small.producer fun loop =>
    { loop with operation := .loop "apply_18_label_726564756365_s15" 2 [34, 36, 35, 37, 33] })
    Small.validator = false := by decide +kernel
example : accepted (modifyLoop Small.producer fun loop =>
    { loop with operation := .loop "apply_18_label_726564756365_s15" 3 [34, 35, 36, 37, 33] })
    Small.validator = false := by decide +kernel

-- Equal types do not authorize swapping source calls. The unchanged first
-- producer occurrence has no counterpart after dropping the first validator.
example : accepted Two.producer { Two.validator with
    instructions := Two.validator.instructions.drop 2 } = false := by decide +kernel

example : refusal { Small.producer with instructions := [] } Small.validator =
    some "round-descriptors-loop-count" := by decide +kernel
example : refusal (modifyLoop Small.producer fun loop => { loop with body := [] }) Small.validator =
    some "round-descriptors-producer-query" := by decide +kernel
example : refusal Small.producer (modifyLoop Small.validator fun loop => { loop with body := [] }) =
    some "round-descriptors-query-match" := by decide +kernel
example : refusal (duplicateQuery Two.producer) Two.validator =
    some "round-descriptors-duplicate-query" := by decide +kernel
example : refusal (modifyLoop Small.producer fun loop =>
    { loop with body := loop.body.modify 0 fun call => { call with body := [call] } }) Small.validator =
    some "round-descriptors-family-mismatch" := by decide +kernel

-- Recognition intentionally does not prove operand correspondence. The
-- separate mutation driver checks that the full kernel block equation refuses
-- this same-typed operand permutation, even though candidate search accepts it.
example : accepted (modifyLoop Small.producer fun loop =>
    { loop with body := loop.body.modify 0 fun call => { call with operands := [14, 16, 15] } })
    Small.validator = true := by decide +kernel

#print axioms ZkcSecurity.Examples.Generated.Components.SmallSumcheckRounds.round0.checked
#print axioms ZkcSecurity.Examples.Generated.Components.SmallSumcheckRounds.round0.producer_actual_block
#print axioms ZkcSecurity.Examples.Generated.Components.SmallSumcheckRounds.round0.validator_actual_block
#print axioms ZkcSecurity.Examples.Generated.Components.SmallSumcheckRounds.round0.origins_checked
#print axioms ZkcSecurity.Examples.Generated.Components.TwoSumsRounds.round1.checked
#print axioms ZkcSecurity.Examples.Generated.Components.TwoSumsRounds.round1.producer_actual_block
#print axioms ZkcSecurity.Examples.Generated.Components.TwoSumsRounds.round1.validator_actual_block
#print axioms ZkcSecurity.Examples.Generated.Components.TwoSumsRounds.round1.origins_checked

end TestsSecurity.RoundDescriptors
