module

import ZkcExamples.Structured.OriginalArtifacts.SmallSumcheck
import ZkcExamples.Structured.OriginalArtifacts.TwoSums

/-! These equations check the selected typed outputs against the actual retained
loop yields and nominal sorts. The full callback/root simulations are audited
by ConstructionBindingsCertificates and ArtifactBinding. -/
open ZkcExamples.Structured.OriginalArtifacts

#print axioms SmallSumcheck.ValidatorCall0.outputs_derived
#print axioms SmallSumcheck.ProducerCall0.outputs_derived
#print axioms TwoSums.ValidatorCall0.outputs_derived
#print axioms TwoSums.ValidatorCall1.outputs_derived
#print axioms TwoSums.ProducerCall0.outputs_derived
#print axioms TwoSums.ProducerCall1.outputs_derived
