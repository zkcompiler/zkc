import ZkcExamples.Structured.RepeatLaws
import ZkcExamples.Structured.RepeatNestedLaws
import ZkcExamples.Structured.RepeatServiceWrapperLaws
import ZkcExamples.Structured.SumcheckReduceLaws
import ZkcExamples.Structured.SumcheckSourceLaws
import ZkcExamples.Structured.ServiceOrderControls
import Mathlib.Tactic.NormNum
import ZkcTools.DeclarationAudit

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
    SumcheckReduceData.snapshot.definitions.length = 26 ∧
      SumcheckReduceViews.unit.definitions.length = 24 ∧
      SumcheckReduceViews.unit.protocols.length = 2 := by decide +kernel

theorem sumcheck_complete_counts :
    SumcheckSourceData.snapshot.definitions.length = 36 ∧
      SumcheckSourceViews.unit.definitions.length = 34 ∧
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

/-! Every declaration of the exercised law and view modules, and every theorem
of this file, has an axiom closure within `propext`, `Classical.choice` and
`Quot.sound`. Module selection replaces lists of selected theorem names, which
could fall behind renames and additions. -/

run_cmd do
  ZkcTools.DeclarationAudit.check
    [`ZkcExamples.Structured.RepeatLaws, `ZkcExamples.Structured.RepeatViews,
     `ZkcExamples.Structured.RepeatNestedLaws, `ZkcExamples.Structured.RepeatNestedViews,
     `ZkcExamples.Structured.RepeatServiceLaws, `ZkcExamples.Structured.RepeatServiceViews,
     `ZkcExamples.Structured.RepeatServiceWrapperLaws, `ZkcExamples.Structured.RepeatServiceWrapperViews,
     `ZkcExamples.Structured.SumcheckReduceLaws, `ZkcExamples.Structured.SumcheckReduceViews,
     `ZkcExamples.Structured.SumcheckSourceLaws, `ZkcExamples.Structured.SumcheckSourceViews]
    "RETAINED-REPEAT-SUBJECTS-AUDIT-PASS" (exactModules := true)

run_cmd ZkcTools.DeclarationAudit.checkCurrent "RETAINED-REPEAT-CLIENTS-AXIOM-PASS"
