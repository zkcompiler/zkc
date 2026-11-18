module

public import Zkc.Core.Facts.Body.BoundsOwnership
public import Zkc.Core.Transform.FunctionComparison

@[expose] public section

namespace Zkc.Core.BodyAnalysis
variable {V : Vocabulary} {hs : List (FnHeader V)} {hdr : FnHeader V}

/-- Each bound admitted for a typed function has its header key and role `none`. -/
theorem FunctionContracts.checkFunction_places (contracts : FunctionContracts hs)
    (f : TypedFn V hs hdr) {lemmas notes bounds}
    (accepted : contracts.checkFunction f lemmas notes = .ok bounds) :
    ∀ q ∈ bounds, q.1.definition = hdr.key ∧ q.1.role = none := by
  obtain ⟨summary, _, checked⟩ := contracts.checkedBody f accepted
  exact checkFacts_places (contracts.config hdr.key lemmas hdr.summary.ensures) notes summary f.inputs f.body
    checked

/-- Each bound admitted for a typed replacement belongs to the shared function header. -/
theorem FunctionContracts.compareFunctions_places (contracts : FunctionContracts hs)
    (source candidate : TypedFn V hs hdr) {lemmas notes notes' bounds}
    (accepted : contracts.compareFunctions source candidate lemmas notes notes' = .ok bounds) :
    ∀ q ∈ bounds, q.1.definition = hdr.key ∧ q.1.role = none := by
  obtain ⟨summary, _, checked⟩ := contracts.checkedPair source candidate accepted
  exact followChecked_places (contracts.config hdr.key lemmas hdr.summary.ensures) (localRules hs).skel hdr.key
    notes notes' summary source.inputs candidate.inputs source.body
    candidate.body checked

#print axioms FunctionContracts.checkFunction_places
#print axioms FunctionContracts.compareFunctions_places
end Zkc.Core.BodyAnalysis
