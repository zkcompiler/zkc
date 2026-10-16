import ZkcExamples.Structured.Application
import Mathlib.Data.ZMod.Basic

/-! Complete-source algebraic controls use independently chosen participant
inputs. Other application controls distinguish admission, generic semantics,
abstract bounds and native comparisons; none is a substitute for another. -/
namespace Tests.StructuredApplications
open Zkc.Source Zkc.Source.Structured
open ZkcExamples.Structured.ApplicationBodies
open ZkcExamples.Structured.ApplicationViews
open ZkcExamples.Structured.Application

private abbrev F := ZMod 97

theorem first_participant_result : program.participant F F 0 (inputs (some 2) (some 3)) =
    .done (.cons (some 6) (.cons none .nil)) := by
  have product : (2 : F) * 3 = 6 := by decide +kernel
  simpa [optionalBinary, product] using first_participant (G := F) (some (2 : F)) (some (3 : F))

theorem second_participant_result : program.participant F F 1 (inputs (some 5) (some 7)) =
    .done (.cons none (.cons (some 12) .nil)) := by
  have sum : (5 : F) + 7 = 12 := by decide +kernel
  simpa [optionalBinary, sum] using second_participant (G := F) (some (5 : F)) (some (7 : F))

theorem first_missing_input : program.participant F F 0 (inputs (some 2) none) =
    .done (.cons none (.cons none .nil)) :=
  first_participant (G := F) (some 2) none

theorem second_missing_input : program.participant F F 1 (inputs none (some 7)) =
    .done (.cons none (.cons none .nil)) :=
  second_participant (G := F) none (some 7)

/-- Full source association starts from the exact retained constructor snapshot. -/
theorem complete_source_admission : check ZkcExamples.Structured.ApplicationData.snapshot = .ok program :=
  kernel_admission

/-- Complete original encounter order is retained, independent of dependency order. -/
theorem original_declaration_order : ZkcExamples.Structured.ApplicationData.snapshot.definitions.map (·.name) =
    [runSignature.name, segmentSignature.name, stepSignature.name, observeSignature.name] := rfl

theorem checked_dependency_order : unit.protocols.map (·.signature) =
    [stepSignature, observeSignature, segmentSignature, runSignature] := rfl

/-- The concrete participants use different copies of both inputs. -/
theorem independent_participant_results :
    program.participant F F 0 (inputs (some 2) (some 3)) =
        .done (.cons (some 6) (.cons none .nil)) ∧
      program.participant F F 1 (inputs (some 5) (some 7)) =
        .done (.cons none (.cons (some 12) .nil)) :=
  ⟨first_participant_result, second_participant_result⟩

/-- Every literal candidate has an original function with its complete checked body. -/
theorem complete_protocol_source (definition : CheckedProtocol)
    (member : definition ∈ unit.protocols) :
    ∃ function domains signatures summaries,
      .function function ∈ ZkcExamples.Structured.ApplicationData.snapshot.definitions ∧
      function.kind = .protocol ∧
      checkUnitHeaders ZkcExamples.Structured.ApplicationData.snapshot =
        .ok (domains, signatures, summaries) ∧
      checkProtocol ZkcExamples.Structured.ApplicationData.snapshot domains summaries
        function signatures = .ok definition ∧
      resolveProtocolSignature function = .ok definition.signature ∧
      lowerProtocol ZkcExamples.Structured.ApplicationData.snapshot domains summaries
        signatures function definition.signature = .ok definition.raw :=
  imported.protocolSource member

/-! The following is an independent changed-source control. It changes the
actual original Step body to an identity return while preserving the complete
header. It has no native-byte or full-unit admission claim. -/

private def originalStepSource : Zkc.Source.Structured.Function :=
  ZkcExamples.Structured.ApplicationData.snapshot.protocolFunctions[2]

private def changedStepSource : Zkc.Source.Structured.Function :=
  { originalStepSource with body := .block [] (.ret [0, 1]) }

private def changedStepBody : Region protocolDialect pairTypes pairTypes :=
  .ret (.cons .here (.cons (.there .here) .nil))

private def changedStepDefinition : CheckedProtocol :=
  { stepDefinition with
    raw := changedStepBody.erase
    body := changedStepBody
    formed := changedStepBody.elaborate_erase }

theorem changed_source_preserves_full_signature :
    resolveProtocolSignature changedStepSource = .ok stepSignature := rfl

theorem changed_source_checks_exact_body :
    checkProtocol ZkcExamples.Structured.ApplicationData.snapshot [] []
      changedStepSource headers = .ok changedStepDefinition := rfl

theorem changed_source_body_differs : changedStepSource.body ≠ originalStepSource.body := by
  intro same
  cases same

theorem changed_source_invalidates_old_body_view :
    changedStepDefinition.raw ≠ stepBody.erase := by
  intro same
  cases same

theorem changed_source_cannot_check_as_original :
    checkProtocol ZkcExamples.Structured.ApplicationData.snapshot [] []
      changedStepSource headers ≠ .ok stepDefinition := by
  rw [changed_source_checks_exact_body]
  intro same
  exact changed_source_invalidates_old_body_view
    (congrArg CheckedProtocol.raw (Except.ok.inj same))

end Tests.StructuredApplications
