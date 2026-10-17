import ZkcExamples.Structured.ServiceOrderControls
import Lean

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

run_cmd do
  for name in [
      ``Tests.StructuredServiceOrder.complete_service_protocol_source,
      ``Tests.StructuredServiceOrder.complete_wrapper_protocol_source,
      ``ServiceOrderViews.kernel_admission,
      ``ServiceOrderViews.exact_subject,
      ``ServiceOrderViews.draw_signature,
      ``ServiceOrderViews.run_signature,
      ``ServiceOrderViews.draw_raw,
      ``ServiceOrderViews.run_raw,
      ``ServiceOrderViews.draw_member,
      ``ServiceOrderViews.run_member,
      ``ServiceOrderViews.entry_selection,
      ``ServiceOrderViews.entry_signature,
      ``ServiceOrderViews.entry_raw,
      ``ApplicationWrapperViews.kernel_admission,
      ``ApplicationWrapperViews.exact_subject,
      ``ApplicationWrapperViews.outer_signature,
      ``ApplicationWrapperViews.outer_raw,
      ``ApplicationWrapperViews.draw_member,
      ``ApplicationWrapperViews.run_member,
      ``ApplicationWrapperViews.outer_member,
      ``ApplicationWrapperViews.entry_selection,
      ``ApplicationWrapperViews.entry_signature,
      ``ApplicationWrapperViews.entry_raw,
      ``ServiceOrder.draw_body_view,
      ``ServiceOrder.run_body_view,
      ``ServiceOrder.verifier_forget_marks,
      ``ServiceOrder.receiver_forget_marks,
      ``ServiceOrder.contextual_verifier,
      ``ServiceOrder.contextual_receiver,
      ``ServiceOrder.observed_verifier,
      ``ServiceOrder.observed_receiver,
      ``ServiceOrder.verifier_participant,
      ``ServiceOrder.receiver_participant,
      ``ServiceOrder.false_guard_observed,
      ``ApplicationWrapper.run_body_view,
      ``ApplicationWrapper.draw_body_view,
      ``ApplicationWrapper.outer_body_view,
      ``ApplicationWrapper.observed_verifier,
      ``ApplicationWrapper.observed_receiver,
      ``ApplicationWrapper.verifier_participant,
      ``ApplicationWrapper.receiver_participant,
      ``ApplicationWrapper.nested_exchange_site,
      ``ApplicationWrapper.nested_qualification_is_not_right_associated,
      ``ServiceOrderControls.same_owner_alias,
      ``ServiceOrderControls.distinct_handles,
      ``ServiceOrderControls.false_guard_keeps_first_draw,
      ``ServiceOrderControls.second_child_draw_stops_prefix,
      ``ServiceOrderControls.second_child_mismatch_unconsumed,
      ``ServiceOrderControls.independently_received_value,
      ``ServiceOrderControls.wrapper_receiver_retains_nested_site] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "unexpected axiom in {name}: {axiomName}"
    Lean.logInfo m!"{name}: {axioms.toList}"
