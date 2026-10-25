import ZkcSecurity.Examples.Generated.SmallSumcheck
import ZkcSecurity.Examples.Generated.TwoSums
import ZkcSecurity.Claims.SourceChargeSites

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
namespace TestsSecurity.SourceChargeSites
open Zkc.Construction ZkcSecurity.Claims
open ZkcSecurity.Examples.Generated

example : Zkc.Source.Structured.encodedLabel "α" = "label_ceb1" := by decide +kernel

example : (Domain.ChargeSite.selectLabel SmallSumcheck.validatorCompiled
    "reduce.challenge").map (·.native) =
      .ok "apply_18_label_726564756365_label_6368616c6c656e6765" := by decide +kernel
example : (Domain.ChargeSite.selectLabel TwoSums.validatorCompiled
    "left.challenge").map (·.native) =
      .ok "apply_14_label_6c656674_label_6368616c6c656e6765" := by decide +kernel
example : (Domain.ChargeSite.selectLabel TwoSums.validatorCompiled
    "right.challenge").map (·.native) =
      .ok "apply_16_label_7269676874_label_6368616c6c656e6765" := by decide +kernel

example : (Domain.ChargeSite.selectLabel TwoSums.validatorCompiled
    "challenge").toOption.isNone = true := by decide +kernel
example : (Domain.ChargeSite.selectLabel TwoSums.validatorCompiled
    "left.delivery").toOption.isNone = true := by decide +kernel
example : (Domain.ChargeSite.selectLabel TwoSums.validatorCompiled
    "left..challenge").toOption.isNone = true := by decide +kernel
example : (Domain.ChargeSite.selectLabel TwoSums.validatorCompiled
    "missing.left.challenge").toOption.isNone = true := by decide +kernel

def occurrences := Domain.challengeOccurrences TwoSums.artifacts.validator.instructions
example : Domain.ChargeSite.resolveLabel (occurrences ++ occurrences)
    "left.challenge" = none := by decide +kernel

/-- Changing a labelled call derives its complete native prefix; no numeric
prefix or parent encoding is supplied by the author. Selection against the
original admitted participant still refuses this renamed occurrence. -/
def renamed : Domain.ChallengeOccurrence := {
  suite := "suite", field := "field"
  template := ⟨"entry", [⟨"apply", "entry", Zkc.Source.Structured.encodedLabel "longer"⟩],
    ["query", "callee", Zkc.Source.Structured.encodedLabel "challenge", "input_0", "random", "draw", "V"]⟩ }
example : Domain.ChargeSite.resolveLabel [renamed] "longer.challenge" =
    renamed.template.querySite? := by decide +kernel
example : (Domain.ChargeSite.selectLabel TwoSums.validatorCompiled
    "longer.challenge").toOption.isNone = true := by decide +kernel

end TestsSecurity.SourceChargeSites
