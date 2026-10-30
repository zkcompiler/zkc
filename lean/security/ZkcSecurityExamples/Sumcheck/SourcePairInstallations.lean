module

public import ZkcSecurityExamples.Sumcheck.SourceProducerRoot
public import ZkcSecurity.Bindings.Sumcheck.SourceFamilyComposition
public import ZkcSecurityExamples.Sumcheck.SourceInstallations
public meta import ZkcSecurityTools.SourceProperties.Builder
public meta import ZkcSecurityTools.SourceProperties.Assembly

@[expose] public section

/-! Honest pairing of the actual admitted SmallSumcheck and TwoSums sources.
These theorems relate both complete participant processes and require neither
a validator handler nor a postulated honest round contract.
-/
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

theorem one (selection : Selection) (site : String) (scope : PairScope)
    (roles : scope.producer = 0 ∧ scope.validator = 1)
    (delivery : (SumcheckRoundNormalForms.challengeSite (SourceRootProperties.context site),
      SumcheckRoundNormalForms.deliverySite (SourceRootProperties.context site)) ∈ scope.deliveries)
    (original : List (model.Field field)) (count handle : Nat) (scalar : model.Field field)
    (callerFrame : Frame) (shape : original.length = 2^count)
    (bounded : count ≤ maximum selection) (small : count < 64) (finite : original.length < indexLimit)
    (honest : scalar = original.sum) :
    Pair scope (fun _ v => v = some true)
      (SourceProducerRoot.one model selection site original count)
      (SourceRootReference.one model selection {} site (some original) (some scalar)
        (some count) (some handle)) := by
  exact SourceFamily.pair model (SourceFamilySelections.installed selection) site scope roles delivery
    original count handle scalar callerFrame shape bounded small finite honest

theorem small (scope : PairScope) (roles : scope.producer = 0 ∧ scope.validator = 1)
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
          (.cons (some original) (.cons (some scalar) (.cons (some count) (.cons (some handle) .nil)))))) := by
  have _machineIndex := small
  rw [SourceProducerRoot.actual_reference, SourceRootReference.actual_reference]
  dsimp only [SourceProducerRoot.reference, SourceRootReference.reference]
  change Pair scope (fun _ v => v = (.cons (some true) .nil : Values (Component model.Value) [.boolean])) _ _
  expose_source_composition
  exact source_property "retained normalized honest pair" companions [] via by
    assemble_source_pairs
      [SourceFamily.pair_contract model (SourceFamilySelections.installed .small) scope roles]
      simplifying [SourceFamily.optionalAnd, PropertyAssembly.done_bind, Option.bind, Option.map,
        Bool.and_true, Bool.true_and]

/-- Both components use the same service handle, and the second pair receives
the actual first pair's residual. No independent-error premise is introduced. -/
theorem two (scope : PairScope) (roles : scope.producer = 0 ∧ scope.validator = 1)
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
            (.cons (some count) (.cons (some handle) .nil)))))))) := by
  have _machineIndex := small
  obtain ⟨ha, hb⟩ := honest
  rw [SourceProducerRoot.actual_reference, SourceRootReference.actual_reference]
  dsimp only [SourceProducerRoot.reference, SourceRootReference.reference]
  change Pair scope (fun _ v => v = (.cons (some true) .nil : Values (Component model.Value) [.boolean])) _ _
  expose_source_composition
  exact source_property "retained normalized honest pair" companions [] via by
    assemble_source_pairs
      [SourceFamily.pair_contract model (SourceFamilySelections.installed .twoSums) scope roles]
      simplifying [SourceFamily.conjunction_equation
        (program := source .twoSums) model (by bind_structured_bodies),
        SourceFamily.optionalAnd, PropertyAssembly.done_bind, Option.bind, Option.map,
        Bool.and_true, Bool.true_and]


#print axioms small
#print axioms two
end ZkcSecurity.Realizations.Sumcheck.SourcePairInstallations
