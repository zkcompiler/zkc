module

public import ZkcSecurity.Examples.Components.TwoSumsTarget
public import ZkcSecurity.Realizations.Sumcheck.DomainHelpers

@[expose] public section

/-! Actual nominal helper equations for the updated sequential TwoSums export.
All dependencies are the complete bodies in this unit's own admitted program.
-/

set_option autoImplicit false
namespace ZkcSecurity.Examples.Components.TwoSums
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured ZkcExamples.Structured.Generated.Bindings
open ZkcSecurity.Families.Sumcheck.TableComponent

theorem domain_bodies : ZkcSecurity.Realizations.Sumcheck.DomainHelpers.Bodies TwoSumsInputs.imported.program :=
  source_bodies

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

theorem call_both (left right : Bool) :
    Domain.callHelper (ringModel F G) TwoSumsInputs.imported.program
      TwoSumsInputs.helper30Helper.name [.data .boolean]
      [.data (.boolean left), .data (.boolean right)] =
      .returned [.data (.boolean (left && right))] :=
  ZkcSecurity.Realizations.Sumcheck.DomainHelpers.call_return _ TwoSumsInputs.helper30Helper
    (.cons left (.cons right .nil)) (.cons (left && right) .nil)
    (both_equation left right) _ _ rfl rfl

/-- The compiled source-owned conjunction target is the same two table sums,
with no assumption that either scalar is correct. -/
theorem call_target (left right : List F) (leftClaim rightClaim : F)
    (leftBound : left.length < indexLimit) (rightBound : right.length < indexLimit) :
    Domain.callHelper (ringModel F G) TwoSumsInputs.imported.program
      TwoSumsInputs.helper3Helper.name [.data .boolean]
      [.data (.vector "bls12-381.fr" left), .data (.vector "bls12-381.fr" right),
        .data (.field "bls12-381.fr" leftClaim), .data (.field "bls12-381.fr" rightClaim)] =
      .returned [.data (.boolean (decide (left.sum = leftClaim ∧ right.sum = rightClaim)))] :=
  ZkcSecurity.Realizations.Sumcheck.DomainHelpers.call_return _ TwoSumsInputs.helper3Helper
    (.cons left (.cons right (.cons leftClaim (.cons rightClaim .nil))))
    (.cons (decide (left.sum = leftClaim ∧ right.sum = rightClaim)) .nil)
    (target_equation left right leftClaim rightClaim leftBound rightBound) _ _ rfl rfl

end ZkcSecurity.Examples.Components.TwoSums
