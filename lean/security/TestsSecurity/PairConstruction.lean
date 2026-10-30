import ZkcSecurityExamples.Generated.SmallSumcheck
import ZkcSecurityExamples.Generated.TwoSums

/-! The production subjects are generated through the shared builder. These
controls import those same checked declarations instead of copying their
admission proofs into a second fixture. -/

namespace TestsSecurity.PairConstruction
open ZkcSecurity.Examples.Generated

example : (SmallSumcheck.subject.target.owner.contract.clauses.filter
    (fun clause => clause.kind == .input)).map (·.name) = ["shape"] := by decide +kernel
example : (TwoSums.subject.target.owner.contract.clauses.filter
    (fun clause => clause.kind == .input)).map (·.name) = ["left_shape", "right_shape"] := by decide +kernel

example : SmallSumcheck.subject.originalExport ≠ TwoSums.subject.originalExport := by
  decide +kernel
example : SmallSumcheck.subject.producerExport ≠ SmallSumcheck.subject.validatorExport := by
  decide +kernel
example : TwoSums.subject.producerExport ≠ TwoSums.subject.validatorExport := by
  decide +kernel

-- Both properties name exactly the same admitted validator and target data.
example : SmallSumcheck.validatorSubject.compiled.selection = SmallSumcheck.subject.selection := rfl
example : TwoSums.validatorSubject.compiled.selection = TwoSums.subject.selection := rfl
example : SmallSumcheck.validatorArtifacts.participant = SmallSumcheck.artifacts.validator := rfl
example : TwoSums.validatorArtifacts.participant = TwoSums.artifacts.validator := rfl
example : SmallSumcheck.validatorSites.map (·.label) = ["reduce.challenge"] := rfl
example : TwoSums.validatorSites.map (·.label) = ["left.challenge", "right.challenge"] := rfl

-- A friendly name cannot manufacture a selected construction occurrence.
example : (ZkcSecurity.Claims.Domain.ChargeSite.select SmallSumcheck.validatorCompiled
    "reduce.challenge" "missing").toOption.isNone = true := by decide +kernel
example : (ZkcSecurity.Claims.Domain.ChargeSite.select SmallSumcheck.validatorCompiled
    "reduce.challenge" "apply_18_label_726564756365_label_64656c6976657279_0").toOption.isNone = true := by
  decide +kernel
example : (ZkcSecurity.Claims.Domain.ChargeSite.select TwoSums.validatorCompiled
    "left.challenge" "apply_18_label_726564756365_label_6368616c6c656e6765").toOption.isNone = true := by
  decide +kernel

#print axioms SmallSumcheck.subject
#print axioms TwoSums.subject
#print axioms SmallSumcheck.validatorSubject
#print axioms TwoSums.validatorSubject
end TestsSecurity.PairConstruction
