module

public import ZkcSecurityExamples.Components.KoalaBearSumcheckCompiledChallenge
public import ZkcSecurityExamples.Components.KoalaBearSumcheckGenerated.Components

@[expose] public section

/-! Association and query laws for the actual compiled nominal endpoint.
Whole-root canonical security requires a separate complete execution bridge. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace TestsSecurity.KoalaBearSumcheckCompiled
open ZkcSecurity.Domains.KoalaBear (Base)
open ZkcSecurity.Examples.Components.KoalaBearSumcheckCompiled

example : subject.ConstructionChecked := construction_links

example (a b claim : Base) (witness : subject.Witness) :
    subject.Holds (statement a b claim) witness ↔ claim = a + b := holds_iff a b claim witness

example (a b claim : Base) :
    subject.FalseStatement (statement a b claim) ↔ claim ≠ a + b := falseStatement_iff a b claim

#print axioms ZkcSecurity.Examples.Components.KoalaBearSumcheckGenerated.Association.associated
#print axioms ZkcSecurity.Examples.Components.KoalaBearSumcheckCompiled.compiled
#print axioms ZkcSecurity.Examples.Components.KoalaBearSumcheckCompiled.holds_iff
#print axioms ZkcSecurity.Examples.Components.KoalaBearSumcheckCompiled.construction_links
#print axioms ZkcSecurity.Examples.Components.KoalaBearSumcheckCompiled.target_helper_link
#print axioms ZkcSecurity.Examples.Components.KoalaBearSumcheckCompiledChallenge.source_origin_link
#print axioms ZkcSecurity.Examples.Components.KoalaBearSumcheckCompiledChallenge.bridge

end TestsSecurity.KoalaBearSumcheckCompiled
