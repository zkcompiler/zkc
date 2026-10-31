module

public import ZkcSecurityExamples.Sumcheck.SourceProducerRoot
public import ZkcSecurity.Bindings.Sumcheck.SourceFamilyComposition
public import ZkcSecurityExamples.Sumcheck.SourceInstallations
public meta import ZkcTools.Companions.Goals

@[expose] public section

/-! Fixed source-property signatures. Header-only commands generate independent
goals before any companion or consumer is imported. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Sumcheck.SourcePairInstallations
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Realizations.Sumcheck
open Zkc.Source Zkc.Source.Structured ReferenceLibrary Zkc.Construction
open ZkcExamples.Structured SumcheckReferenceInstallation TableComponent
open SumcheckSourceSelections hiding field
open ZkcSecurity.Source
attribute [local implicit_reducible] NormalForm.InputPattern.scope SourceRootReference.pattern
  SourceProducerRoot.pattern SourceProducerRoot.reductionPattern

variable (model : DomainModel) [fieldLaw : Fact (IsField (model.Field field))]
local instance : Field (model.Field field) := fieldLaw.out.toField
variable {Frame : Type}

companion_goal small_goal for theorem small (scope : PairScope) (roles : scope.producer = 0 ∧ scope.validator = 1)
    (delivery : (SumcheckRoundNormalForms.challengeSite (SourceRootProperties.context "label_726564756365"),
      SumcheckRoundNormalForms.deliverySite (SourceRootProperties.context "label_726564756365")) ∈ scope.deliveries)
    (original : List (model.Field field)) (count handle : Nat) (scalar : model.Field field)
    (shape : original.length = 2^count) (bounded : count ≤ maximum .small)
    (small : count < 64) (finite : original.length < indexLimit) (honest : scalar = original.sum) :
    Pair scope (fun _ v => v = SourceInstallations.returned model .small (some true))
      (Occurrence.participant model (source .small) 0
        (SourceProducerRoot.rootInputs model .small (.cons original (.cons count .nil))))
      (Occurrence.participant model (source .small) 1
        (SourceRootReference.rootInputs model .small
          (.cons (some original) (.cons (some scalar) (.cons (some count) (.cons (some handle) .nil))))))

companion_goal two_goal for theorem two (scope : PairScope) (roles : scope.producer = 0 ∧ scope.validator = 1)
    (leftDelivery : (SumcheckRoundNormalForms.challengeSite (SourceRootProperties.context "label_6c656674"),
      SumcheckRoundNormalForms.deliverySite (SourceRootProperties.context "label_6c656674")) ∈ scope.deliveries)
    (rightDelivery : (SumcheckRoundNormalForms.challengeSite (SourceRootProperties.context "label_7269676874"),
      SumcheckRoundNormalForms.deliverySite (SourceRootProperties.context "label_7269676874")) ∈ scope.deliveries)
    (left right : List (model.Field field)) (count handle : Nat) (a b : model.Field field)
    (leftShape : left.length = 2^count) (rightShape : right.length = 2^count)
    (bounded : count ≤ maximum .twoSums) (small : count < 64)
    (leftFinite : left.length < indexLimit) (rightFinite : right.length < indexLimit)
    (honest : a = left.sum ∧ b = right.sum) :
    Pair scope (fun _ v => v = SourceInstallations.returned model .twoSums (some true))
      (Occurrence.participant model (source .twoSums) 0
        (SourceProducerRoot.rootInputs model .twoSums (.cons left (.cons right (.cons count .nil)))))
      (Occurrence.participant model (source .twoSums) 1
        (SourceRootReference.rootInputs model .twoSums
          (.cons (some left) (.cons (some right) (.cons (some a) (.cons (some b)
            (.cons (some count) (.cons (some handle) .nil))))))))

end ZkcSecurity.Realizations.Sumcheck.SourcePairInstallations
