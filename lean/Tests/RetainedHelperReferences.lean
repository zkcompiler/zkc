import ZkcTools.StructuredSource.ReferenceLaws
import Zkc.Source.Structured.ReferenceLibrary
import ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs
import ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs
import Zkc.Protocols.Sumcheck.Source.HelperBodies

/-! The same mathematical law installs into two actual imported helper tables.
No per-instance lookup, closed-body, ABI-decoding or source equation is authored.
The tests concern helper mathematics, not an endpoint soundness assertion. -/
set_option autoImplicit false
namespace Tests.RetainedHelperReferences
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured.Generated.Bindings
open ZkcExamples.Structured.SumcheckHelperBodies

variable (model : DomainModel)

theorem small_empty :
    Domain.callHelper model SmallSumcheckInputs.imported.program emptyHelper.name
      [.data (.vector "bls12-381.fr")] [] =
      .returned [.data (.vector "bls12-381.fr" [])] := by
  apply_helper_reference ReferenceLibrary.emptyVector model "bls12-381.fr" "s0"
    using SmallSumcheckInputs.imported.program

theorem small_append (values : List (model.Field "bls12-381.fr")) (value : model.Field "bls12-381.fr") :
    Domain.callHelper model SmallSumcheckInputs.imported.program appendHelper.name
      [.data (.vector "bls12-381.fr")]
      [.data (.vector "bls12-381.fr" values), .data (.field "bls12-381.fr" value)] =
      .returned [.data (.vector "bls12-381.fr" (values ++ [value]))] := by
  apply_helper_reference ReferenceLibrary.appendVector model "bls12-381.fr" "s0"
    using SmallSumcheckInputs.imported.program

theorem two_sums_append (values : List (model.Field "bls12-381.fr")) (value : model.Field "bls12-381.fr") :
    Domain.callHelper model TwoSumsInputs.imported.program appendHelper.name
      [.data (.vector "bls12-381.fr")]
      [.data (.vector "bls12-381.fr" values), .data (.field "bls12-381.fr" value)] =
      .returned [.data (.vector "bls12-381.fr" (values ++ [value]))] := by
  apply_helper_reference ReferenceLibrary.appendVector model "bls12-381.fr" "s0"
    using TwoSumsInputs.imported.program

/-- The caller's complete body and its callee are matched independently. -/
def interpolationWrapper : ReferenceLaw model
    [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"]
    [.field "bls12-381.fr"] :=
  ReferenceLibrary.call model ZkcExamples.Structured.MapFirstBodies.interpolateHelper
    (Operands.identity _) (.cons .here .nil)
    (ReferenceLibrary.interpolate model "bls12-381.fr").reference

theorem small_interpolation (left right challenge : model.Field "bls12-381.fr") :
    Domain.callHelper model SmallSumcheckInputs.imported.program
      SmallSumcheckInputs.helper22Helper.name
      [.data (.field "bls12-381.fr")]
      [.data (.field "bls12-381.fr" left), .data (.field "bls12-381.fr" right),
        .data (.field "bls12-381.fr" challenge)] =
      .returned [.data (.field "bls12-381.fr" (left + (right - left) * challenge))] := by
  derive_helper_reference [ReferenceLibrary.emptyVector model "bls12-381.fr" "s0", interpolationWrapper model, ReferenceLibrary.interpolate model "bls12-381.fr"] using SmallSumcheckInputs.imported.program

/-- Matching the wrapper without proving its actual dependency is insufficient. -/
example (_left _right _challenge : model.Field "bls12-381.fr") : True := by
  fail_if_success
    have : Domain.callHelper model SmallSumcheckInputs.imported.program
        SmallSumcheckInputs.helper22Helper.name
        [.data (.field "bls12-381.fr")]
        [.data (.field "bls12-381.fr" _left), .data (.field "bls12-381.fr" _right),
          .data (.field "bls12-381.fr" _challenge)] =
        .returned [.data (.field "bls12-381.fr" (_left + (_right - _left) * _challenge))] := by
      derive_helper_reference [interpolationWrapper model] using SmallSumcheckInputs.imported.program
  trivial

/-- A different declared nominal output cannot borrow the successful law. -/
example : True := by
  fail_if_success
    have : Domain.callHelper model SmallSumcheckInputs.imported.program emptyHelper.name
        [.data (.vector "other.fr")] [] =
        .returned [.data (.vector "bls12-381.fr" [])] := by
      apply_helper_reference ReferenceLibrary.emptyVector model "bls12-381.fr" "s0"
        using SmallSumcheckInputs.imported.program
  trivial

/-- The tool preserves pending caller goals. -/
example : (Domain.callHelper model SmallSumcheckInputs.imported.program emptyHelper.name
      [.data (.vector "bls12-381.fr")] [] =
      .returned [.data (.vector "bls12-381.fr" [])]) ∧ True := by
  constructor
  · apply_helper_reference ReferenceLibrary.emptyVector model "bls12-381.fr" "s0"
      using SmallSumcheckInputs.imported.program
  · trivial

#print axioms small_empty
#print axioms small_interpolation
#print axioms small_append
#print axioms two_sums_append
#print axioms Domain.Binding.callHelper_of_reference
#print axioms ReferenceLibrary.sumVector
#print axioms ReferenceLibrary.splitVector
end Tests.RetainedHelperReferences
