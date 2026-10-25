module

public import ZkcExamples.Structured.OriginalSumcheckRoots

@[expose] public section

/-! Emitted original roots retain the admitted input identity and their exact
source-body/whole-participant equations. No compiled certificate is selected. -/
namespace Tests.OriginalRootBindings
open ZkcExamples.Structured

example : OriginalSumcheckInstances.Small.imported = Generated.Bindings.SmallSumcheck.sourceImported := rfl
example : OriginalSumcheckInstances.Two.imported = Generated.Bindings.TwoSums.sourceImported := rfl
example : OriginalSumcheckInstances.Small.reduceDefinition = Generated.Bindings.SmallSumcheck.definition0 := rfl
example : OriginalSumcheckInstances.Two.reduceDefinition = Generated.Bindings.TwoSums.definition0 := rfl
example : OriginalSumcheckRoots.Small.context = OriginalSumcheckInstances.Small.context := rfl
example : OriginalSumcheckRoots.Two.leftContext = OriginalSumcheckInstances.Two.leftContext := rfl
example : OriginalSumcheckRoots.Two.rightContext = OriginalSumcheckInstances.Two.rightContext := rfl

#print axioms Generated.Original.SmallSumcheck.sourceProtocol0_body
#print axioms Generated.Original.TwoSums.sourceProtocol0_body
#print axioms Generated.Original.SmallSumcheck.root_body
#print axioms Generated.Original.TwoSums.root_body
#print axioms Generated.Original.SmallSumcheck.body_binding
#print axioms Generated.Original.TwoSums.body_binding
#print axioms Generated.Original.SmallSumcheck.participant_binding
#print axioms Generated.Original.TwoSums.participant_binding
#print axioms OriginalSumcheckRoots.Small.root_binding
#print axioms OriginalSumcheckRoots.Two.root_binding

end Tests.OriginalRootBindings
