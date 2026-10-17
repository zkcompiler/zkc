import Tests.DeriveRegionSources

namespace Tests.RegionViewControls
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured Tests.DeriveRegionSources

/-- Generated projection agrees with the existing raw-body witness. -/
theorem sum_view_matches_existing : sumAddView = SumcheckRelationContract.addBody := rfl

theorem sum_raw_witness : sumAdd.raw = sumAddView.erase := rfl

theorem schnorr_raw_witness : SchnorrInteractive.program.payload.entry.raw = schnorrView.erase := by
  rw [schnorr_view_exact]
  exact SchnorrInteractive.program.payload.entry.exactBody.symm

/-- The current raw-witness API and projected association pin the same body. -/
theorem raw_association :
    BodyIn SumcheckSourceViews.program.payload.definitions sumAdd.helper sumAddView := by
  exact_body SumcheckSourceViews.sumAddDefinition

theorem projected_association :
    BodyIn SumcheckSourceViews.program.payload.definitions sumAdd.helper sumAddView := by
  exact BodyIn.of_checked SumcheckSourceViews.sumAddDefinition (by structured_mem)

/-- Same ABI with a changed symbol is not a matching checked declaration. -/
example : True := by
  fail_if_success
    have : BodyIn SumcheckSourceViews.program.payload.definitions
        {sumAdd.helper with name := "different-helper"} sumAddView := by
      exact BodyIn.of_checked SumcheckSourceViews.sumAddDefinition (by structured_mem)
  trivial

/-- Same ABI with a different operation tree cannot use projected association. -/
example : True := by
  fail_if_success
    have : BodyIn SumcheckSourceViews.program.payload.definitions sumAdd.helper
        (Region.ret (.cons .here .nil)) := by
      exact BodyIn.of_checked SumcheckSourceViews.sumAddDefinition (by structured_mem)
  trivial

set_option linter.unusedVariables false in
/-- View materialization fails explicitly on an unknown source constructor. -/
example (body : Region dialect [.index] [.index]) : True := by
  fail_if_success
    let _view : Region dialect [.index] [.index] := region_view% body
  trivial

end Tests.RegionViewControls
