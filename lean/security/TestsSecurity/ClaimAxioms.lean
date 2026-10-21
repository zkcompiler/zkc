import ZkcSecurity.Claims.Endpoint
import ZkcSecurity.Claims.Knowledge
import ZkcSecurity.Claims.Arithmetic
import ZkcSecurity.Claims.StageLinks
import Zkc.Claims.Receipt

/-! The kernel reports the actual transitive axioms of each public proof route.
Serialized declaration closure records are audit data, not proof substitutes. -/

#print axioms ZkcSecurity.Claims.worstCaseCostBound_mono_charge
#print axioms ZkcSecurity.Claims.fixedIdealEndpoint
#print axioms ZkcSecurity.Claims.adaptiveIdealEndpoint
#print axioms ZkcSecurity.Claims.fixedBytesEndpoint
#print axioms ZkcSecurity.Claims.adaptiveBytesEndpoint
#print axioms ZkcSecurity.Claims.weightedFixedIdealEndpoint
#print axioms ZkcSecurity.Claims.weightedAdaptiveIdealEndpoint
#print axioms ZkcSecurity.Claims.weightedFixedBytesEndpoint
#print axioms ZkcSecurity.Claims.weightedAdaptiveBytesEndpoint
#print axioms ZkcSecurity.Claims.chargedExport
#print axioms ZkcSecurity.Claims.knowledgeEndpoint
#print axioms ZkcSecurity.Claims.ReplayClass.ofEvidence
#print axioms ZkcSecurity.Claims.Subject.stageLinkProofs
#print axioms ZkcSecurity.Claims.chargedCostBound_mono_bound
#print axioms ZkcSecurity.Claims.requestedCost_of_equal_charge
#print axioms Zkc.Claims.Receipt.ofTheorem
#print axioms Zkc.Claims.Receipt.ofEndpoint
#print axioms Zkc.Claims.Receipt.ofDerivation
