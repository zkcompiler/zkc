module

import ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheckProducerRoot
import ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheckValidatorRoot
import ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSumsProducerRoot
import ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSumsValidatorRoot

/-! Kernel checks of the exact outputs. These imports have no dependency on the
legacy per-root component certificates. False callback/root equations must fail. -/
set_option autoImplicit false
namespace TestsSecurity.ConstructionBindingsCertificates
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Examples.Generated.OriginalArtifacts

example : True := by
  fail_if_success
    have : SmallSumcheck.validatorArtifact.instructions = [] := by kernel_rfl
  fail_if_success
    have : TwoSums.producerArtifact.returned = [] := by kernel_rfl
  fail_if_success
    have : SmallSumcheck.occurrence0.draw = SmallSumcheck.occurrence0.delivery := by kernel_rfl
  fail_if_success
    have : TwoSums.occurrence0.draw = TwoSums.occurrence1.draw := by kernel_rfl
  trivial

#print axioms ZkcExamples.Structured.Generated.OriginalArtifacts.SmallSumcheckProducerSource.body_binding
#print axioms ZkcExamples.Structured.Generated.OriginalArtifacts.SmallSumcheckProducerSource.participant_binding
#print axioms ZkcExamples.Structured.Generated.OriginalArtifacts.TwoSumsProducerSource.body_binding
#print axioms ZkcExamples.Structured.Generated.OriginalArtifacts.TwoSumsProducerSource.participant_binding
#print axioms SmallSumcheck.context_checked
#print axioms SmallSumcheck.policy_checked
#print axioms SmallSumcheck.occurrence0_delivery_checked
#print axioms SmallSumcheck.ValidatorCall0.capture_size
#print axioms SmallSumcheck.ValidatorCall0.loop_operands
#print axioms SmallSumcheck.ValidatorCall0.loop_operation
#print axioms SmallSumcheck.ValidatorCall0.callback
#print axioms SmallSumcheck.ProducerCall0.callback
#print axioms TwoSums.ValidatorCall0.callback
#print axioms TwoSums.ValidatorCall1.callback
#print axioms TwoSums.ProducerCall0.callback
#print axioms TwoSums.ProducerCall1.callback
#print axioms SmallSumcheckProducerRoot.producer_source
#print axioms TwoSumsProducerRoot.producer_source
#print axioms SmallSumcheckProducerRoot.producer
#print axioms SmallSumcheckValidatorRoot.validator
#print axioms TwoSumsProducerRoot.producer
#print axioms TwoSumsValidatorRoot.validator

end TestsSecurity.ConstructionBindingsCertificates
