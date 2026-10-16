import ZkcExamples.Structured.RepeatLaws
import ZkcExamples.Structured.RepeatNestedLaws
import ZkcExamples.Structured.RepeatServiceWrapperLaws
import ZkcExamples.Structured.SumcheckReduceLaws
import ZkcExamples.Structured.SumcheckSourceLaws
import ZkcExamples.Structured.ServiceOrderControls
import Mathlib.Tactic.NormNum
import Lean

/-! Independent scripted replies exercise the admitted complete source processes.
These are model controls, not native refinement or cryptographic security. -/
namespace Tests.StructuredRepeatClients
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open ServiceOrderControls

set_option smartUnfolding false

theorem original_repeat_receiver :
    (RepeatViews.program.observed ℚ ℚ 0
      (RepeatLaws.inputs (some 2) (some 10) none none none)).run handler
      { replies := [.value 5, .value 7, .value 99] } =
      ⟨.returned (.cons (some 22) (.cons none .nil)),
        ⟨[.value 99], [], 2, ""⟩,
        [.receive "apply_2_s5_s2_0" 1 5, .receive "apply_2_s5_s2_0" 1 7]⟩ := by
  rw [RepeatLaws.observed_receiver _ (by decide)]
  have total : (10 : ℚ) + 5 + 7 = 22 := by norm_num
  rw [← total]
  rfl

theorem original_repeat_verifier_two :
    (RepeatViews.program.observed ℚ ℚ 1
      (RepeatLaws.inputs (some 2) none (some 100) (some true) (some 7))).run handler
      { replies := [.value 2, .value 3, .value 99] } =
      ⟨.returned (.cons none (.cons (some 105) .nil)),
        ⟨[.value 99], [(7, 2)], 2, ""⟩,
        [.draw "apply_2_s5_s0" 7 2, .send "apply_2_s5_s2_0" 0 2,
         .draw "apply_2_s5_s0" 7 3, .send "apply_2_s5_s2_0" 0 3]⟩ := by
  rw [RepeatLaws.observed_verifier _ (by decide)]
  have total : (100 : ℚ) + 2 + 3 = 105 := by norm_num
  rw [← total]
  rfl

/-- This count is independent of the receiver's two iterations above. -/
theorem original_repeat_verifier_one :
    (RepeatViews.program.observed ℚ ℚ 1
      (RepeatLaws.inputs (some 1) none (some 100) (some true) (some 7))).run handler
      { replies := [.value 2, .value 3, .value 99] } =
      ⟨.returned (.cons none (.cons (some 102) .nil)),
        ⟨[.value 3, .value 99], [(7, 1)], 1, ""⟩,
        [.draw "apply_2_s5_s0" 7 2, .send "apply_2_s5_s2_0" 0 2]⟩ := by
  rw [RepeatLaws.observed_verifier _ (by decide)]
  have total : (100 : ℚ) + 2 = 102 := by norm_num
  rw [← total]
  rfl

/-- The guard has no results, but its stop still bypasses all calls and iterations. -/
theorem zero_result_guard_stops :
    (RepeatViews.program.observed ℚ ℚ 1
      (RepeatLaws.inputs (some 2) none (some 100) (some false) (some 7))).run handler
      { replies := [.value 99] } =
      ⟨.stopped .reject, ⟨[.value 99], [], 0, "s4"⟩, []⟩ := by
  rw [RepeatLaws.observed_verifier _ (by decide)]
  rfl

theorem zero_skips_absent_captures :
    RepeatViews.program.participant ℚ ℚ 1
      (RepeatLaws.inputs (some 0) none (some 100) none none) =
        .done (.cons none (.cons (some 100) .nil)) :=
  RepeatLaws.zero_verifier none (some 100) none none

theorem nested_two_by_two :
    RepeatNestedViews.program.participant ℚ ℚ 0
      (RepeatNestedLaws.inputs (some 2) (some 2) (some 3)) =
        .done (.cons (some 15) .nil) := by
  rw [RepeatNestedLaws.repeated_addition _ _ (by decide) (by decide)]
  norm_num

theorem nested_zero_ignores_inner :
    RepeatNestedViews.program.participant ℚ ℚ 0
      (RepeatNestedLaws.inputs (some 0) none (some 3)) = .done (.cons (some 3) .nil) :=
  RepeatNestedLaws.zero_outer none (some 3)

/-- Aliased lexical ports route all six requests to the same actual provider state. -/
theorem same_owner_alias_six_queries :
    (RepeatServiceViews.program.observed ℚ ℚ 1
      (RepeatServiceLaws.inputs (some 2) (some 7) (some 7))).run handler
      { replies := [.value 2, .value 3, .value 5, .value 7, .value 11, .value 13, .value 99] } =
      ⟨.returned (.cons none (.cons (some 41) .nil)),
        ⟨[.value 99], [(7, 6)], 6, ""⟩,
        [.draw "s0" 7 2,
         .draw "apply_2_s7_s0" 7 3, .draw "apply_2_s7_s2" 7 5,
         .send "apply_2_s7_s5_0" 0 8,
         .draw "apply_2_s7_s0" 7 7, .draw "apply_2_s7_s2" 7 11,
         .send "apply_2_s7_s5_0" 0 18, .draw "s16" 7 13]⟩ := by
  rw [RepeatServiceLaws.observed_verifier _ (by decide)]
  have first : (3 : ℚ) + 5 = 8 := by norm_num
  have second : (7 : ℚ) + 11 = 18 := by norm_num
  have total : (2 : ℚ) + (3 + 5) + (7 + 11) + 13 = 41 := by norm_num
  rw [← first, ← second, ← total]
  rfl

theorem distinct_handles_preserve_order :
    (RepeatServiceViews.program.observed ℚ ℚ 1
      (RepeatServiceLaws.inputs (some 2) (some 7) (some 9))).run handler
      { replies := [.value 2, .value 3, .value 5, .value 7, .value 11, .value 13, .value 99] } =
      ⟨.returned (.cons none (.cons (some 41) .nil)),
        ⟨[.value 99], [(7, 4), (9, 2)], 6, ""⟩,
        [.draw "s0" 7 2,
         .draw "apply_2_s7_s0" 7 3, .draw "apply_2_s7_s2" 9 5,
         .send "apply_2_s7_s5_0" 0 8,
         .draw "apply_2_s7_s0" 7 7, .draw "apply_2_s7_s2" 9 11,
         .send "apply_2_s7_s5_0" 0 18, .draw "s16" 7 13]⟩ := by
  rw [RepeatServiceLaws.observed_verifier _ (by decide)]
  have first : (3 : ℚ) + 5 = 8 := by norm_num
  have second : (7 : ℚ) + 11 = 18 := by norm_num
  have total : (2 : ℚ) + (3 + 5) + (7 + 11) + 13 = 41 := by norm_num
  rw [← first, ← second, ← total]
  rfl

/-- A stop in iteration two preserves completed iteration one and the next first query. -/
theorem later_iteration_stop_keeps_effects :
    (RepeatServiceViews.program.observed ℚ ℚ 1
      (RepeatServiceLaws.inputs (some 3) (some 7) (some 9))).run handler
      { replies := [.value 2, .value 3, .value 5, .value 7, .stop .abort, .value 99] } =
      ⟨.stopped .abort,
        ⟨[.value 99], [(7, 3), (9, 2)], 5, "apply_2_s7_s2"⟩,
        [.draw "s0" 7 2,
         .draw "apply_2_s7_s0" 7 3, .draw "apply_2_s7_s2" 9 5,
         .send "apply_2_s7_s5_0" 0 8,
         .draw "apply_2_s7_s0" 7 7, .drawStop "apply_2_s7_s2" 9 .abort]⟩ := by
  rw [RepeatServiceLaws.observed_verifier _ (by decide)]
  have first : (3 : ℚ) + 5 = 8 := by norm_num
  rw [← first]
  rfl

theorem wrapper_receiver_root_peer_and_nested_site :
    (RepeatServiceWrapperViews.program.observed ℚ ℚ 2
      (RepeatServiceWrapperLaws.inputs (some 1) (some 91) none none)).run handler
      { replies := [.value 19, .value 99] } =
      ⟨.returned (.cons none (.cons none (.cons (some 19) .nil))),
        ⟨[.value 99], [], 1, ""⟩,
        [.receive "apply_13_apply_2_s0_s7_s5_0" 0 19]⟩ := by
  rw [RepeatServiceWrapperLaws.observed_receiver _ (by decide)]
  have total : (0 : ℚ) + 19 = 19 := by norm_num
  conv_rhs => arg 1; rw [← total]
  rfl

theorem wrapper_third_role_independent :
    RepeatServiceWrapperViews.program.participant ℚ ℚ 1
      (RepeatServiceWrapperLaws.inputs none (some 91) none none) =
        .done (.cons none (.cons (some 91) (.cons none .nil))) :=
  RepeatServiceWrapperLaws.outside_participant none (some 91) none none

theorem service_zero_preserves_prelude_and_suffix :
    (RepeatServiceViews.program.observed ℚ ℚ 1
      (RepeatServiceLaws.inputs (some 0) (some 7) none)).run handler
      { replies := [.value 2, .value 13, .value 99] } =
      ⟨.returned (.cons none (.cons (some 15) .nil)),
        ⟨[.value 99], [(7, 2)], 2, ""⟩,
        [.draw "s0" 7 2, .draw "s16" 7 13]⟩ := by
  rw [RepeatServiceLaws.zero_verifier]
  have total : (2 : ℚ) + 13 = 15 := by norm_num
  rw [← total]
  rfl

theorem nested_inner_zero_preserves_state :
    RepeatNestedViews.program.participant ℚ ℚ 0
      (RepeatNestedLaws.inputs (some 1) (some 0) (some 3)) = .done (.cons (some 3) .nil) :=
  RepeatNestedLaws.zero_inner 1 (by decide) (some 3)

theorem nested_reached_missing_inner :
    RepeatNestedViews.program.participant ℚ ℚ 0
      (RepeatNestedLaws.inputs (some 1) none (some 3)) = .halt .incomplete :=
  RepeatNestedLaws.positive_missing_inner (some 3)

theorem wrapper_sender_actual_handles_and_root_peer :
    (RepeatServiceWrapperViews.program.observed ℚ ℚ 0
      (RepeatServiceWrapperLaws.inputs (some 1) (some 91) (some 7) (some 9))).run handler
      { replies := [.value 2, .value 3, .value 5, .value 13, .value 99] } =
      ⟨.returned (.cons (some 23) (.cons none (.cons none .nil))),
        ⟨[.value 99], [(7, 3), (9, 1)], 4, ""⟩,
        [.draw "apply_2_s0_s0" 7 2,
         .draw "apply_13_apply_2_s0_s7_s0" 7 3,
         .draw "apply_13_apply_2_s0_s7_s2" 9 5,
         .send "apply_13_apply_2_s0_s7_s5_0" 2 8,
         .draw "apply_2_s0_s16" 7 13]⟩ := by
  rw [RepeatServiceWrapperLaws.observed_sender _ (by decide)]
  have subtotal : (3 : ℚ) + 5 = 8 := by norm_num
  have total : (2 : ℚ) + (3 + 5) + 13 = 23 := by norm_num
  rw [← subtotal, ← total]
  rfl

theorem reduction_complete_counts :
    SumcheckReduceData.snapshot.definitions.length = 20 ∧
      SumcheckReduceViews.unit.definitions.length = 18 ∧
      SumcheckReduceViews.unit.protocols.length = 2 := by decide +kernel

theorem sumcheck_complete_counts :
    SumcheckSourceData.snapshot.definitions.length = 29 ∧
      SumcheckSourceViews.unit.definitions.length = 27 ∧
      SumcheckSourceViews.unit.protocols.length = 2 := by decide +kernel

/-- A same-signature original-body mutation cannot reuse the old checked tree.
This control checks the mutated complete function; it does not replace the six subjects. -/
private def changedNestedSource : Zkc.Source.Structured.Function :=
  { RepeatNestedData.snapshot.protocolFunctions[0] with body := .block [] (.ret [2]) }

private def changedNestedBody : Region protocolDialect
    RepeatNestedBodies.runSignature.inputs RepeatNestedBodies.runSignature.outputs :=
  .ret (.cons (.there (.there .here)) .nil)

private def changedNestedDefinition : CheckedProtocol :=
  { RepeatNestedViews.runDefinition with
    raw := changedNestedBody.erase
    body := changedNestedBody
    formed := changedNestedBody.elaborate_erase }

theorem changed_source_preserves_signature :
    resolveProtocolSignature changedNestedSource = .ok RepeatNestedBodies.runSignature := rfl

theorem changed_source_checks_new_tree :
    checkProtocol RepeatNestedData.snapshot [] [] changedNestedSource
      [RepeatNestedBodies.runSignature] = .ok changedNestedDefinition := rfl

theorem changed_source_invalidates_old_tree :
    changedNestedDefinition.raw ≠ RepeatNestedBodies.runBody.erase := by
  intro same
  cases same

theorem changed_source_cannot_reuse_admission :
    checkProtocol RepeatNestedData.snapshot [] [] changedNestedSource
      [RepeatNestedBodies.runSignature] ≠ .ok RepeatNestedViews.runDefinition := by
  rw [changed_source_checks_new_tree]
  intro same
  exact changed_source_invalidates_old_tree
    (congrArg CheckedProtocol.raw (Except.ok.inj same))

/-- Missing/excess count observations preserve headers and do not demand state. -/
theorem original_missing_count_header :
    (RepeatViews.program.observed ℚ ℚ 0
      (RepeatLaws.inputs none none none none none)).run handler
      { replies := [.value 99] } =
      ⟨.stopped .incomplete, ⟨[.value 99], [], 0, "s3"⟩, []⟩ := by
  rw [RepeatLaws.missing_count_receiver]
  rfl

theorem original_large_count_header :
    (RepeatViews.program.observed ℚ ℚ 1
      (RepeatLaws.inputs (some (2 ^ 128)) none none none none)).run handler
      { replies := [.value 99] } =
      ⟨.stopped .refused, ⟨[.value 99], [], 0, "s3"⟩, []⟩ := by
  rw [RepeatLaws.excess_count_verifier _ (by decide)]
  rfl

theorem missing_go_before_state_or_service :
    (RepeatViews.program.observed ℚ ℚ 1
      (RepeatLaws.inputs (some 4) none none none none)).run handler
      { replies := [.value 99] } =
      ⟨.stopped .incomplete, ⟨[.value 99], [], 0, "s4"⟩, []⟩ := by
  rw [RepeatLaws.positive_missing_go _ (by decide) (by decide)]
  rfl

theorem nested_large_outer_header :
    (RepeatNestedViews.program.observed ℚ ℚ 0
      (RepeatNestedLaws.inputs (some (2 ^ 128)) none none)).run handler
      { replies := [.value 99] } =
      ⟨.stopped .refused, ⟨[.value 99], [], 0, "s3"⟩, []⟩ := by
  rw [RepeatNestedLaws.observed_excess_outer _ (by decide)]
  rfl

theorem service_missing_count_retains_prelude :
    (RepeatServiceViews.program.observed ℚ ℚ 1
      (RepeatServiceLaws.inputs none (some 7) none)).run handler
      { replies := [.value 2, .value 99] } =
      ⟨.stopped .incomplete, ⟨[.value 99], [(7, 1)], 1, "s6"⟩,
        [.draw "s0" 7 2]⟩ := by
  rw [RepeatServiceLaws.missing_count_verifier]
  rfl

theorem service_large_count_retains_prelude :
    (RepeatServiceViews.program.observed ℚ ℚ 1
      (RepeatServiceLaws.inputs (some (2 ^ 128)) (some 7) none)).run handler
      { replies := [.value 2, .value 99] } =
      ⟨.stopped .refused, ⟨[.value 99], [(7, 1)], 1, "s6"⟩,
        [.draw "s0" 7 2]⟩ := by
  rw [RepeatServiceLaws.excess_count_verifier _ (by decide)]
  rfl

theorem service_absent_prelude_precedes_count :
    (RepeatServiceViews.program.observed ℚ ℚ 1
      (RepeatServiceLaws.inputs (some (2 ^ 128)) none none)).run handler
      { replies := [.value 99] } =
      ⟨.stopped .incomplete, ⟨[.value 99], [], 0, "s0"⟩, []⟩ := by
  rw [RepeatServiceLaws.excess_count_verifier _ (by decide)]
  rfl

theorem service_stopping_prelude_precedes_count :
    (RepeatServiceViews.program.observed ℚ ℚ 1
      (RepeatServiceLaws.inputs (some (2 ^ 128)) (some 7) none)).run handler
      { replies := [.stop .abort, .value 99] } =
      ⟨.stopped .abort, ⟨[.value 99], [(7, 1)], 1, "s0"⟩,
        [.drawStop "s0" 7 .abort]⟩ := by
  rw [RepeatServiceLaws.excess_count_verifier _ (by decide)]
  rfl

end Tests.StructuredRepeatClients

run_cmd do
  let names := [
    ``ZkcExamples.Structured.RepeatViews.round_signature,
    ``ZkcExamples.Structured.RepeatViews.round_raw,
    ``ZkcExamples.Structured.RepeatViews.round_body,
    ``ZkcExamples.Structured.RepeatViews.run_signature,
    ``ZkcExamples.Structured.RepeatViews.run_raw,
    ``ZkcExamples.Structured.RepeatViews.run_body,
    ``ZkcExamples.Structured.RepeatViews.headers_checked,
    ``ZkcExamples.Structured.RepeatViews.helpers_checked,
    ``ZkcExamples.Structured.RepeatViews.protocols_checked,
    ``ZkcExamples.Structured.RepeatViews.native_metadata_checked,
    ``ZkcExamples.Structured.RepeatViews.effective_sites_checked,
    ``ZkcExamples.Structured.RepeatViews.metadata_checked,
    ``ZkcExamples.Structured.RepeatViews.payload_linked,
    ``ZkcExamples.Structured.RepeatViews.kernel_admission,
    ``ZkcExamples.Structured.RepeatViews.exact_subject,
    ``ZkcExamples.Structured.RepeatViews.round_member,
    ``ZkcExamples.Structured.RepeatViews.run_member,
    ``ZkcExamples.Structured.RepeatViews.entry_selection,
    ``ZkcExamples.Structured.RepeatViews.entry_signature,
    ``ZkcExamples.Structured.RepeatViews.entry_raw,
    ``ZkcExamples.Structured.RepeatViews.complete_protocol_source,
    ``ZkcExamples.Structured.RepeatViews.complete_original_protocol,
    ``ZkcExamples.Structured.RepeatLaws.round_body_view,
    ``ZkcExamples.Structured.RepeatLaws.run_body_view,
    ``ZkcExamples.Structured.RepeatLaws.receiver_step,
    ``ZkcExamples.Structured.RepeatLaws.verifier_step,
    ``ZkcExamples.Structured.RepeatLaws.receiver_repeat,
    ``ZkcExamples.Structured.RepeatLaws.verifier_repeat,
    ``ZkcExamples.Structured.RepeatLaws.contextual_receiver,
    ``ZkcExamples.Structured.RepeatLaws.contextual_verifier,
    ``ZkcExamples.Structured.RepeatLaws.observed_receiver,
    ``ZkcExamples.Structured.RepeatLaws.observed_verifier,
    ``ZkcExamples.Structured.RepeatLaws.receiver_participant,
    ``ZkcExamples.Structured.RepeatLaws.verifier_participant,
    ``ZkcExamples.Structured.RepeatLaws.independent_counts,
    ``ZkcExamples.Structured.RepeatLaws.zero_verifier,
    ``ZkcExamples.Structured.RepeatLaws.missing_count_receiver,
    ``ZkcExamples.Structured.RepeatLaws.excess_count_receiver,
    ``ZkcExamples.Structured.RepeatLaws.missing_count_verifier,
    ``ZkcExamples.Structured.RepeatLaws.excess_count_verifier,
    ``ZkcExamples.Structured.RepeatLaws.positive_missing_go,
    ``ZkcExamples.Structured.RepeatNestedViews.run_signature,
    ``ZkcExamples.Structured.RepeatNestedViews.run_raw,
    ``ZkcExamples.Structured.RepeatNestedViews.run_body,
    ``ZkcExamples.Structured.RepeatNestedViews.headers_checked,
    ``ZkcExamples.Structured.RepeatNestedViews.helpers_checked,
    ``ZkcExamples.Structured.RepeatNestedViews.protocols_checked,
    ``ZkcExamples.Structured.RepeatNestedViews.native_metadata_checked,
    ``ZkcExamples.Structured.RepeatNestedViews.effective_sites_checked,
    ``ZkcExamples.Structured.RepeatNestedViews.metadata_checked,
    ``ZkcExamples.Structured.RepeatNestedViews.payload_linked,
    ``ZkcExamples.Structured.RepeatNestedViews.kernel_admission,
    ``ZkcExamples.Structured.RepeatNestedViews.exact_subject,
    ``ZkcExamples.Structured.RepeatNestedViews.run_member,
    ``ZkcExamples.Structured.RepeatNestedViews.entry_selection,
    ``ZkcExamples.Structured.RepeatNestedViews.entry_signature,
    ``ZkcExamples.Structured.RepeatNestedViews.entry_raw,
    ``ZkcExamples.Structured.RepeatNestedViews.complete_protocol_source,
    ``ZkcExamples.Structured.RepeatNestedViews.complete_original_protocol,
    ``ZkcExamples.Structured.RepeatNestedLaws.run_body_view,
    ``ZkcExamples.Structured.RepeatNestedLaws.zero_outer,
    ``ZkcExamples.Structured.RepeatNestedLaws.missing_outer,
    ``ZkcExamples.Structured.RepeatNestedLaws.observed_missing_outer,
    ``ZkcExamples.Structured.RepeatNestedLaws.observed_excess_outer,
    ``ZkcExamples.Structured.RepeatNestedLaws.repeated_addition,
    ``ZkcExamples.Structured.RepeatNestedLaws.zero_inner,
    ``ZkcExamples.Structured.RepeatNestedLaws.positive_missing_inner,
    ``ZkcExamples.Structured.RepeatServiceViews.draw_signature,
    ``ZkcExamples.Structured.RepeatServiceViews.draw_raw,
    ``ZkcExamples.Structured.RepeatServiceViews.draw_body,
    ``ZkcExamples.Structured.RepeatServiceViews.run_signature,
    ``ZkcExamples.Structured.RepeatServiceViews.run_raw,
    ``ZkcExamples.Structured.RepeatServiceViews.run_body,
    ``ZkcExamples.Structured.RepeatServiceViews.headers_checked,
    ``ZkcExamples.Structured.RepeatServiceViews.helpers_checked,
    ``ZkcExamples.Structured.RepeatServiceViews.protocols_checked,
    ``ZkcExamples.Structured.RepeatServiceViews.native_metadata_checked,
    ``ZkcExamples.Structured.RepeatServiceViews.effective_sites_checked,
    ``ZkcExamples.Structured.RepeatServiceViews.metadata_checked,
    ``ZkcExamples.Structured.RepeatServiceViews.payload_linked,
    ``ZkcExamples.Structured.RepeatServiceViews.kernel_admission,
    ``ZkcExamples.Structured.RepeatServiceViews.exact_subject,
    ``ZkcExamples.Structured.RepeatServiceViews.draw_member,
    ``ZkcExamples.Structured.RepeatServiceViews.run_member,
    ``ZkcExamples.Structured.RepeatServiceViews.entry_selection,
    ``ZkcExamples.Structured.RepeatServiceViews.entry_signature,
    ``ZkcExamples.Structured.RepeatServiceViews.entry_raw,
    ``ZkcExamples.Structured.RepeatServiceViews.complete_protocol_source,
    ``ZkcExamples.Structured.RepeatServiceViews.complete_original_protocol,
    ``ZkcExamples.Structured.RepeatServiceViews.callback_application_occurs,
    ``ZkcExamples.Structured.RepeatServiceViews.callback_service_origins,
    ``ZkcExamples.Structured.RepeatServiceViews.callback_origin_transfer,
    ``ZkcExamples.Structured.RepeatServiceViews.callback_original_instruction,
    ``ZkcExamples.Structured.RepeatServiceViews.callback_roles,
    ``ZkcExamples.Structured.RepeatServiceViews.callback_callee,
    ``ZkcExamples.Structured.RepeatServiceViews.callback_callee_statement_free,
    ``ZkcExamples.Structured.RepeatServiceLaws.draw_body_view,
    ``ZkcExamples.Structured.RepeatServiceLaws.run_body_view,
    ``ZkcExamples.Structured.RepeatServiceLaws.receiver_step,
    ``ZkcExamples.Structured.RepeatServiceLaws.verifier_step,
    ``ZkcExamples.Structured.RepeatServiceLaws.receiver_repeat,
    ``ZkcExamples.Structured.RepeatServiceLaws.verifier_repeat,
    ``ZkcExamples.Structured.RepeatServiceLaws.contextual_verifier,
    ``ZkcExamples.Structured.RepeatServiceLaws.contextual_receiver,
    ``ZkcExamples.Structured.RepeatServiceLaws.permuted_verifier,
    ``ZkcExamples.Structured.RepeatServiceLaws.permuted_receiver,
    ``ZkcExamples.Structured.RepeatServiceLaws.observed_verifier,
    ``ZkcExamples.Structured.RepeatServiceLaws.observed_receiver,
    ``ZkcExamples.Structured.RepeatServiceLaws.verifier_participant,
    ``ZkcExamples.Structured.RepeatServiceLaws.receiver_participant,
    ``ZkcExamples.Structured.RepeatServiceLaws.zero_verifier,
    ``ZkcExamples.Structured.RepeatServiceLaws.missing_count_receiver,
    ``ZkcExamples.Structured.RepeatServiceLaws.missing_count_verifier,
    ``ZkcExamples.Structured.RepeatServiceLaws.excess_count_receiver,
    ``ZkcExamples.Structured.RepeatServiceLaws.excess_count_verifier,
    ``ZkcExamples.Structured.RepeatServiceWrapperViews.draw_signature,
    ``ZkcExamples.Structured.RepeatServiceWrapperViews.draw_raw,
    ``ZkcExamples.Structured.RepeatServiceWrapperViews.draw_body,
    ``ZkcExamples.Structured.RepeatServiceWrapperViews.run_signature,
    ``ZkcExamples.Structured.RepeatServiceWrapperViews.run_raw,
    ``ZkcExamples.Structured.RepeatServiceWrapperViews.run_body,
    ``ZkcExamples.Structured.RepeatServiceWrapperViews.outer_signature,
    ``ZkcExamples.Structured.RepeatServiceWrapperViews.outer_raw,
    ``ZkcExamples.Structured.RepeatServiceWrapperViews.outer_body,
    ``ZkcExamples.Structured.RepeatServiceWrapperViews.headers_checked,
    ``ZkcExamples.Structured.RepeatServiceWrapperViews.helpers_checked,
    ``ZkcExamples.Structured.RepeatServiceWrapperViews.protocols_checked,
    ``ZkcExamples.Structured.RepeatServiceWrapperViews.native_metadata_checked,
    ``ZkcExamples.Structured.RepeatServiceWrapperViews.effective_sites_checked,
    ``ZkcExamples.Structured.RepeatServiceWrapperViews.metadata_checked,
    ``ZkcExamples.Structured.RepeatServiceWrapperViews.payload_linked,
    ``ZkcExamples.Structured.RepeatServiceWrapperViews.kernel_admission,
    ``ZkcExamples.Structured.RepeatServiceWrapperViews.exact_subject,
    ``ZkcExamples.Structured.RepeatServiceWrapperViews.draw_member,
    ``ZkcExamples.Structured.RepeatServiceWrapperViews.run_member,
    ``ZkcExamples.Structured.RepeatServiceWrapperViews.outer_member,
    ``ZkcExamples.Structured.RepeatServiceWrapperViews.entry_selection,
    ``ZkcExamples.Structured.RepeatServiceWrapperViews.entry_signature,
    ``ZkcExamples.Structured.RepeatServiceWrapperViews.entry_raw,
    ``ZkcExamples.Structured.RepeatServiceWrapperViews.complete_protocol_source,
    ``ZkcExamples.Structured.RepeatServiceWrapperViews.complete_original_protocol,
    ``ZkcExamples.Structured.RepeatServiceWrapperLaws.outer_body_view,
    ``ZkcExamples.Structured.RepeatServiceWrapperLaws.run_agrees,
    ``ZkcExamples.Structured.RepeatServiceWrapperLaws.observed_sender,
    ``ZkcExamples.Structured.RepeatServiceWrapperLaws.observed_receiver,
    ``ZkcExamples.Structured.RepeatServiceWrapperLaws.outside_participant,
    ``ZkcExamples.Structured.SumcheckReduceViews.less_raw,
    ``ZkcExamples.Structured.SumcheckReduceViews.less_body,
    ``ZkcExamples.Structured.SumcheckReduceViews.rows_raw,
    ``ZkcExamples.Structured.SumcheckReduceViews.rows_body,
    ``ZkcExamples.Structured.SumcheckReduceViews.shape_raw,
    ``ZkcExamples.Structured.SumcheckReduceViews.shape_body,
    ``ZkcExamples.Structured.SumcheckReduceViews.table_raw,
    ``ZkcExamples.Structured.SumcheckReduceViews.table_body,
    ``ZkcExamples.Structured.SumcheckReduceViews.width_raw,
    ``ZkcExamples.Structured.SumcheckReduceViews.width_body,
    ``ZkcExamples.Structured.SumcheckReduceViews.variables_raw,
    ``ZkcExamples.Structured.SumcheckReduceViews.variables_body,
    ``ZkcExamples.Structured.SumcheckReduceViews.empty_raw,
    ``ZkcExamples.Structured.SumcheckReduceViews.empty_body,
    ``ZkcExamples.Structured.SumcheckReduceViews.halves_raw,
    ``ZkcExamples.Structured.SumcheckReduceViews.halves_body,
    ``ZkcExamples.Structured.SumcheckReduceViews.sums_raw,
    ``ZkcExamples.Structured.SumcheckReduceViews.sums_body,
    ``ZkcExamples.Structured.SumcheckReduceViews.interpolate_raw,
    ``ZkcExamples.Structured.SumcheckReduceViews.interpolate_body,
    ``ZkcExamples.Structured.SumcheckReduceViews.map_raw,
    ``ZkcExamples.Structured.SumcheckReduceViews.map_body,
    ``ZkcExamples.Structured.SumcheckReduceViews.first_raw,
    ``ZkcExamples.Structured.SumcheckReduceViews.first_body,
    ``ZkcExamples.Structured.SumcheckReduceViews.append_raw,
    ``ZkcExamples.Structured.SumcheckReduceViews.append_body,
    ``ZkcExamples.Structured.SumcheckReduceViews.values_raw,
    ``ZkcExamples.Structured.SumcheckReduceViews.values_body,
    ``ZkcExamples.Structured.SumcheckReduceViews.reduce_signature,
    ``ZkcExamples.Structured.SumcheckReduceViews.reduce_raw,
    ``ZkcExamples.Structured.SumcheckReduceViews.reduce_body,
    ``ZkcExamples.Structured.SumcheckReduceViews.run_signature,
    ``ZkcExamples.Structured.SumcheckReduceViews.run_raw,
    ``ZkcExamples.Structured.SumcheckReduceViews.run_body,
    ``ZkcExamples.Structured.SumcheckReduceViews.headers_checked,
    ``ZkcExamples.Structured.SumcheckReduceViews.helpers_checked,
    ``ZkcExamples.Structured.SumcheckReduceViews.run_checked,
    ``ZkcExamples.Structured.SumcheckReduceViews.reduce_checked,
    ``ZkcExamples.Structured.SumcheckReduceViews.protocols_checked,
    ``ZkcExamples.Structured.SumcheckReduceViews.native_metadata_checked,
    ``ZkcExamples.Structured.SumcheckReduceViews.effective_sites_checked,
    ``ZkcExamples.Structured.SumcheckReduceViews.metadata_checked,
    ``ZkcExamples.Structured.SumcheckReduceViews.payload_linked,
    ``ZkcExamples.Structured.SumcheckReduceViews.kernel_admission,
    ``ZkcExamples.Structured.SumcheckReduceViews.exact_subject,
    ``ZkcExamples.Structured.SumcheckReduceViews.reduce_member,
    ``ZkcExamples.Structured.SumcheckReduceViews.run_member,
    ``ZkcExamples.Structured.SumcheckReduceViews.entry_selection,
    ``ZkcExamples.Structured.SumcheckReduceViews.entry_signature,
    ``ZkcExamples.Structured.SumcheckReduceViews.entry_raw,
    ``ZkcExamples.Structured.SumcheckReduceViews.complete_protocol_source,
    ``ZkcExamples.Structured.SumcheckReduceViews.complete_original_protocol,
    ``ZkcExamples.Structured.SumcheckReduceLaws.return_indices,
    ``ZkcExamples.Structured.SumcheckReduceLaws.return_equation,
    ``ZkcExamples.Structured.SumcheckReduceLaws.reduce_checked_tree,
    ``ZkcExamples.Structured.SumcheckReduceLaws.original_reduce_return,
    ``ZkcExamples.Structured.SumcheckReduceLaws.run_body_view,
    ``ZkcExamples.Structured.SumcheckReduceLaws.reduce_body_view,
    ``ZkcExamples.Structured.SumcheckReduceLaws.source_protocol_permutation,
    ``ZkcExamples.Structured.SumcheckReduceLaws.map_retained,
    ``ZkcExamples.Structured.SumcheckReduceLaws.map_derived,
    ``ZkcExamples.Structured.SumcheckReduceLaws.map_root_selected,
    ``ZkcExamples.Structured.SumcheckReduceLaws.map_member,
    ``ZkcExamples.Structured.SumcheckReduceLaws.map_body_view,
    ``ZkcExamples.Structured.SumcheckReduceLaws.first_member,
    ``ZkcExamples.Structured.SumcheckReduceLaws.first_body_view,
    ``ZkcExamples.Structured.SumcheckReduceLaws.values_member,
    ``ZkcExamples.Structured.SumcheckReduceLaws.values_body_view,
    ``ZkcExamples.Structured.SumcheckSourceViews.less_raw,
    ``ZkcExamples.Structured.SumcheckSourceViews.less_body,
    ``ZkcExamples.Structured.SumcheckSourceViews.rows_raw,
    ``ZkcExamples.Structured.SumcheckSourceViews.rows_body,
    ``ZkcExamples.Structured.SumcheckSourceViews.shape_raw,
    ``ZkcExamples.Structured.SumcheckSourceViews.shape_body,
    ``ZkcExamples.Structured.SumcheckSourceViews.table_raw,
    ``ZkcExamples.Structured.SumcheckSourceViews.table_body,
    ``ZkcExamples.Structured.SumcheckSourceViews.width_raw,
    ``ZkcExamples.Structured.SumcheckSourceViews.width_body,
    ``ZkcExamples.Structured.SumcheckSourceViews.variables_raw,
    ``ZkcExamples.Structured.SumcheckSourceViews.variables_body,
    ``ZkcExamples.Structured.SumcheckSourceViews.empty_raw,
    ``ZkcExamples.Structured.SumcheckSourceViews.empty_body,
    ``ZkcExamples.Structured.SumcheckSourceViews.halves_raw,
    ``ZkcExamples.Structured.SumcheckSourceViews.halves_body,
    ``ZkcExamples.Structured.SumcheckSourceViews.sums_raw,
    ``ZkcExamples.Structured.SumcheckSourceViews.sums_body,
    ``ZkcExamples.Structured.SumcheckSourceViews.interpolate_raw,
    ``ZkcExamples.Structured.SumcheckSourceViews.interpolate_body,
    ``ZkcExamples.Structured.SumcheckSourceViews.map_raw,
    ``ZkcExamples.Structured.SumcheckSourceViews.map_body,
    ``ZkcExamples.Structured.SumcheckSourceViews.first_raw,
    ``ZkcExamples.Structured.SumcheckSourceViews.first_body,
    ``ZkcExamples.Structured.SumcheckSourceViews.append_raw,
    ``ZkcExamples.Structured.SumcheckSourceViews.append_body,
    ``ZkcExamples.Structured.SumcheckSourceViews.step_raw,
    ``ZkcExamples.Structured.SumcheckSourceViews.step_body,
    ``ZkcExamples.Structured.SumcheckSourceViews.foldStep_raw,
    ``ZkcExamples.Structured.SumcheckSourceViews.foldStep_body,
    ``ZkcExamples.Structured.SumcheckSourceViews.fold_raw,
    ``ZkcExamples.Structured.SumcheckSourceViews.fold_body,
    ``ZkcExamples.Structured.SumcheckSourceViews.foldWrapper_raw,
    ``ZkcExamples.Structured.SumcheckSourceViews.foldWrapper_body,
    ``ZkcExamples.Structured.SumcheckSourceViews.prefix_raw,
    ``ZkcExamples.Structured.SumcheckSourceViews.prefix_body,
    ``ZkcExamples.Structured.SumcheckSourceViews.values_raw,
    ``ZkcExamples.Structured.SumcheckSourceViews.values_body,
    ``ZkcExamples.Structured.SumcheckSourceViews.valuesRealization_raw,
    ``ZkcExamples.Structured.SumcheckSourceViews.valuesRealization_body,
    ``ZkcExamples.Structured.SumcheckSourceViews.checkTable_raw,
    ``ZkcExamples.Structured.SumcheckSourceViews.checkTable_body,
    ``ZkcExamples.Structured.SumcheckSourceViews.check_raw,
    ``ZkcExamples.Structured.SumcheckSourceViews.check_body,
    ``ZkcExamples.Structured.SumcheckSourceViews.reduce_signature,
    ``ZkcExamples.Structured.SumcheckSourceViews.reduce_raw,
    ``ZkcExamples.Structured.SumcheckSourceViews.reduce_body,
    ``ZkcExamples.Structured.SumcheckSourceViews.run_signature,
    ``ZkcExamples.Structured.SumcheckSourceViews.run_raw,
    ``ZkcExamples.Structured.SumcheckSourceViews.run_body,
    ``ZkcExamples.Structured.SumcheckSourceViews.headers_checked,
    ``ZkcExamples.Structured.SumcheckSourceViews.helpers_checked,
    ``ZkcExamples.Structured.SumcheckSourceViews.run_checked,
    ``ZkcExamples.Structured.SumcheckSourceViews.reduce_checked,
    ``ZkcExamples.Structured.SumcheckSourceViews.protocols_checked,
    ``ZkcExamples.Structured.SumcheckSourceViews.native_metadata_checked,
    ``ZkcExamples.Structured.SumcheckSourceViews.effective_sites_checked,
    ``ZkcExamples.Structured.SumcheckSourceViews.metadata_checked,
    ``ZkcExamples.Structured.SumcheckSourceViews.payload_linked,
    ``ZkcExamples.Structured.SumcheckSourceViews.kernel_admission,
    ``ZkcExamples.Structured.SumcheckSourceViews.exact_subject,
    ``ZkcExamples.Structured.SumcheckSourceViews.reduce_member,
    ``ZkcExamples.Structured.SumcheckSourceViews.run_member,
    ``ZkcExamples.Structured.SumcheckSourceViews.entry_selection,
    ``ZkcExamples.Structured.SumcheckSourceViews.entry_signature,
    ``ZkcExamples.Structured.SumcheckSourceViews.entry_raw,
    ``ZkcExamples.Structured.SumcheckSourceViews.complete_protocol_source,
    ``ZkcExamples.Structured.SumcheckSourceViews.complete_original_protocol,
    ``ZkcExamples.Structured.SumcheckSourceLaws.return_indices,
    ``ZkcExamples.Structured.SumcheckSourceLaws.return_equation,
    ``ZkcExamples.Structured.SumcheckSourceLaws.reduce_checked_tree,
    ``ZkcExamples.Structured.SumcheckSourceLaws.original_reduce_return,
    ``ZkcExamples.Structured.SumcheckSourceLaws.run_body_view,
    ``ZkcExamples.Structured.SumcheckSourceLaws.reduce_body_view,
    ``ZkcExamples.Structured.SumcheckSourceLaws.source_protocol_permutation,
    ``ZkcExamples.Structured.SumcheckSourceLaws.map_retained,
    ``ZkcExamples.Structured.SumcheckSourceLaws.map_derived,
    ``ZkcExamples.Structured.SumcheckSourceLaws.map_root_selected,
    ``ZkcExamples.Structured.SumcheckSourceLaws.map_member,
    ``ZkcExamples.Structured.SumcheckSourceLaws.map_body_view,
    ``ZkcExamples.Structured.SumcheckSourceLaws.first_member,
    ``ZkcExamples.Structured.SumcheckSourceLaws.first_body_view,
    ``ZkcExamples.Structured.SumcheckSourceLaws.values_member,
    ``ZkcExamples.Structured.SumcheckSourceLaws.values_body_view,
    ``ZkcExamples.Structured.SumcheckSourceLaws.prefix_member,
    ``ZkcExamples.Structured.SumcheckSourceLaws.prefix_body_view,
    ``ZkcExamples.Structured.SumcheckSourceLaws.valuesRealization_member,
    ``ZkcExamples.Structured.SumcheckSourceLaws.valuesRealization_body_view,
    ``ZkcExamples.Structured.SumcheckSourceLaws.valuesRealization_retained,
    ``ZkcExamples.Structured.SumcheckSourceLaws.valuesRealization_derived,
    ``ZkcExamples.Structured.SumcheckSourceLaws.valuesRealization_root_selected,
    ``Tests.StructuredRepeatClients.original_repeat_receiver,
    ``Tests.StructuredRepeatClients.original_repeat_verifier_two,
    ``Tests.StructuredRepeatClients.original_repeat_verifier_one,
    ``Tests.StructuredRepeatClients.zero_result_guard_stops,
    ``Tests.StructuredRepeatClients.zero_skips_absent_captures,
    ``Tests.StructuredRepeatClients.nested_two_by_two,
    ``Tests.StructuredRepeatClients.nested_zero_ignores_inner,
    ``Tests.StructuredRepeatClients.same_owner_alias_six_queries,
    ``Tests.StructuredRepeatClients.distinct_handles_preserve_order,
    ``Tests.StructuredRepeatClients.later_iteration_stop_keeps_effects,
    ``Tests.StructuredRepeatClients.wrapper_receiver_root_peer_and_nested_site,
    ``Tests.StructuredRepeatClients.wrapper_third_role_independent,
    ``Tests.StructuredRepeatClients.service_zero_preserves_prelude_and_suffix,
    ``Tests.StructuredRepeatClients.nested_inner_zero_preserves_state,
    ``Tests.StructuredRepeatClients.nested_reached_missing_inner,
    ``Tests.StructuredRepeatClients.wrapper_sender_actual_handles_and_root_peer,
    ``Tests.StructuredRepeatClients.reduction_complete_counts,
    ``Tests.StructuredRepeatClients.sumcheck_complete_counts,
    ``Tests.StructuredRepeatClients.changed_source_preserves_signature,
    ``Tests.StructuredRepeatClients.changed_source_checks_new_tree,
    ``Tests.StructuredRepeatClients.changed_source_invalidates_old_tree,
    ``Tests.StructuredRepeatClients.changed_source_cannot_reuse_admission,
    ``Tests.StructuredRepeatClients.original_missing_count_header,
    ``Tests.StructuredRepeatClients.original_large_count_header,
    ``Tests.StructuredRepeatClients.missing_go_before_state_or_service,
    ``Tests.StructuredRepeatClients.nested_large_outer_header,
    ``Tests.StructuredRepeatClients.service_missing_count_retains_prelude,
    ``Tests.StructuredRepeatClients.service_large_count_retains_prelude,
    ``Tests.StructuredRepeatClients.service_absent_prelude_precedes_count,
    ``Tests.StructuredRepeatClients.service_stopping_prelude_precedes_count
  ]
  for name in names do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "unexpected axiom in {name}: {axiomName}"
    Lean.logInfo m!"{name}: {axioms.toList}"
  Lean.logInfo m!"Retained repeat clients: {names.length} declaration axiom closures checked"
