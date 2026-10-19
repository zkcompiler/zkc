import ZkcExamples.Structured.ServiceOrderControls
import ZkcTools.DeclarationAudit

/-! Audit the full-source service-order and wrapper claims separately from the
independent provider controls. Ordinary Lean axioms remain reported by the
repository-wide declaration audit; no new trusted semantic axiom is allowed. -/

open ZkcExamples.Structured
open Zkc.Source Zkc.Source.Structured

namespace Tests.StructuredServiceOrder

/-- Each retained service protocol comes from its complete original declaration. -/
theorem complete_service_protocol_source (definition : CheckedProtocol)
    (member : definition ∈ ServiceOrderViews.unit.protocols) :
    ∃ function domains signatures summaries,
      .function function ∈ ServiceOrderData.snapshot.definitions ∧
      function.kind = .protocol ∧
      checkUnitHeaders ServiceOrderData.snapshot = .ok (domains, signatures, summaries) ∧
      checkProtocol ServiceOrderData.snapshot domains summaries function signatures =
        .ok definition ∧
      resolveProtocolSignature function = .ok definition.signature ∧
      lowerProtocol ServiceOrderData.snapshot domains summaries signatures function
        definition.signature = .ok definition.raw :=
  ServiceOrderViews.imported.protocolSource member

/-- The wrapper retains source association for every transitive child as well. -/
theorem complete_wrapper_protocol_source (definition : CheckedProtocol)
    (member : definition ∈ ApplicationWrapperViews.unit.protocols) :
    ∃ function domains signatures summaries,
      .function function ∈ ApplicationWrapperData.snapshot.definitions ∧
      function.kind = .protocol ∧
      checkUnitHeaders ApplicationWrapperData.snapshot = .ok (domains, signatures, summaries) ∧
      checkProtocol ApplicationWrapperData.snapshot domains summaries function signatures =
        .ok definition ∧
      resolveProtocolSignature function = .ok definition.signature ∧
      lowerProtocol ApplicationWrapperData.snapshot domains summaries signatures function
        definition.signature = .ok definition.raw :=
  ApplicationWrapperViews.imported.protocolSource member

end Tests.StructuredServiceOrder

/-! Every declaration of the service-order and wrapper modules and of their
controls, and both theorems above, has an axiom closure within `propext`,
`Classical.choice` and `Quot.sound`. -/

run_cmd do
  ZkcTools.DeclarationAudit.check
    [`ZkcExamples.Structured.ServiceOrder, `ZkcExamples.Structured.ServiceOrderViews,
     `ZkcExamples.Structured.ApplicationWrapper, `ZkcExamples.Structured.ApplicationWrapperViews,
     `ZkcExamples.Structured.ServiceOrderControls]
    "SERVICE-ORDER-AUDIT-PASS" (exactModules := true)

run_cmd ZkcTools.DeclarationAudit.checkCurrent "SERVICE-ORDER-SOURCE-AXIOM-PASS"
