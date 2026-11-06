module

public import ZkcSecurity.Bindings.Transcript.FieldSourceProperties
public import ZkcSecurity.Bindings.Transcript.PublicSourceSupport
public import ZkcSecurity.Bindings.Source.PublicProperties
public import ZkcSecurity.ProgramLogic.Oracle.StructuredUniform

@[expose] public section

/-! Focused standard-axiom inspection of the ordinary source request laws.
This is not a package declaration audit or an Oracle source certificate. -/
set_option autoImplicit false
namespace TestsSecurity.TypedSourceAxioms
open ZkcSecurity.FiatShamir

#print axioms NominalDomain.losslessOperation
#print axioms NominalDomain.handleReceive_not_lossless
#print axioms DomainSourceReading.queryRequest_draw
#print axioms DomainSourceReading.queryRequest_reading
#print axioms DomainSourceReading.receiveRequest_reading
#print axioms DomainSourceReading.service_reading
#print axioms DomainSourceReading.interpretation
#print axioms DomainSourceReading.reading
#print axioms DomainSourceReading.endpoint
#print axioms DomainSourceReading.presentation_lossless
#print axioms PublicSourceSupport.participant
#print axioms PublicSourceSupport.lossless
#print axioms FieldSourceProperties.charged
#print axioms FieldSourceProperties.cost
#print axioms ServiceProperties.derivation
#print axioms ServiceProperties.cost
#print axioms ZkcSecurity.Source.PublicProperties.install
#print axioms ZkcSecurity.Source.PublicProperties.install_cost

end TestsSecurity.TypedSourceAxioms
