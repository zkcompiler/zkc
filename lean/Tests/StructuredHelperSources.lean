import Zkc.Source.Structured.HelperSources
import ZkcExamples.Structured.SumcheckSourceAssociations

/-! Controls for the helper source association. The premise is met by actual
members of an admitted unit; the source declaration it returns is checked
under the unit's own phases, and a protocol declaration is never one. -/
set_option autoImplicit false
namespace Tests.StructuredHelperSources
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured

/-- The premise holds for an actual member of the admitted Sumcheck unit. -/
example : ∃ original domains headers summaries,
    original ∈ SumcheckSourceData.snapshot.definitions ∧ original.kind ≠ .protocol ∧
    checkUnitHeaders SumcheckSourceData.snapshot = .ok (domains, headers, summaries) ∧
    checkDefinition SumcheckSourceData.snapshot domains summaries original =
      .ok SumcheckSourceViews.lessDefinition :=
  SumcheckSourceViews.imported.helperSource SumcheckSourceAssociations.less_member

/-- The returned source is the retained declaration with the member's own name. -/
example : ∀ original domains headers summaries,
    checkUnitHeaders SumcheckSourceData.snapshot = .ok (domains, headers, summaries) →
    checkDefinition SumcheckSourceData.snapshot domains summaries original =
      .ok SumcheckSourceViews.lessDefinition →
    original.name = SumcheckSourceViews.lessDefinition.name := by
  intro original domains headers summaries _ checked
  exact (checkDefinition_name checked).symm

/-- A protocol declaration is refused by the helper checker before lowering, so
no protocol tree can be returned as a helper source. -/
theorem protocol_refused :
    (checkDefinition SumcheckSourceData.snapshot SumcheckSourceViews.domains
      SumcheckSourceViews.summaries
      (.function SumcheckSourceData.snapshot.protocolFunctions[0])).toBool = false := by
  decide +kernel

end Tests.StructuredHelperSources
