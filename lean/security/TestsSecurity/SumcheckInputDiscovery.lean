module

public import ZkcSecurity.Generation.SumcheckInputs
public import ZkcSecurity.Examples.Generated.SmallSumcheck
public import ZkcSecurity.Examples.Generated.TwoSums
public import ZkcSecurity.Examples.Generated.Components.SmallSumcheckRounds
public import ZkcSecurity.Examples.Generated.Components.TwoSumsRounds

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
namespace TestsSecurity.SumcheckInputDiscovery
open Zkc.Construction ZkcSecurity.Generation
open ZkcSecurity.Generation.SumcheckInputs
open ZkcSecurity.Examples.Generated

noncomputable def small := SubjectABI.metadata SmallSumcheck.subject
noncomputable def two := SubjectABI.metadata TwoSums.subject
abbrev smallProducer := ZkcExamples.Construction.Generated.SmallSumcheckPair.Producer.participant
abbrev smallValidator := ZkcExamples.Construction.Generated.SmallSumcheckPair.Validator.participant
abbrev twoProducer := ZkcExamples.Construction.Generated.TwoSumsPair.Producer.participant
abbrev twoValidator := ZkcExamples.Construction.Generated.TwoSumsPair.Validator.participant

example : propose small smallProducer smallValidator = .ok [0] := by decide +kernel
example : propose two twoProducer twoValidator = .ok [0, 1] := by decide +kernel

-- Def-use discovery follows the actual helper operands, even if its name is
-- unchanged. This is a candidate change, never evidence that the swap is valid.
example : propose two { twoProducer with instructions := twoProducer.instructions.modify 1 (fun instruction => { instruction with operands := [1, 2, 4] }) } twoValidator =
    .ok [1, 1] := by decide +kernel

example : (propose two { twoProducer with instructions := twoProducer.instructions.modify 1 (fun instruction => { instruction with operands := [0, 1, 2, 4] }) } twoValidator).toOption =
    none := by decide +kernel

example : (propose small { smallProducer with instructions := smallProducer.instructions.modify 1 (fun instruction => { instruction with operation := .unsupported "hidden-helper" }) }
      smallValidator).toOption = none := by decide +kernel

example : (propose { small with publicPositions := [1, 2] } smallProducer smallValidator).toOption =
    none := by decide +kernel

example : (propose { small with producerPositions := none } smallProducer smallValidator).toOption =
    none := by decide +kernel

example : dependencies [some [1], none] [0, 1] = none := rfl
example : dependencies [some [1]] [4] = none := rfl
example : dependencies [some [1], some [1, 2]] [0, 1] = some [1, 2] := by decide +kernel

end TestsSecurity.SumcheckInputDiscovery
