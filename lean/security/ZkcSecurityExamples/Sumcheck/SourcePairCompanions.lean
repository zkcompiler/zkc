module

public import ZkcSecurityExamples.Sumcheck.SourcePairGoals
public meta import ZkcSecurityTools.SourceProperties.Builder
public meta import ZkcTools.Companions

@[expose] public section

/-! Author mathematics for the independently generated source-property goals.
These proofs import no source-property consumer. -/
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

section
variable (model : DomainModel) [fieldLaw : Fact (IsField (model.Field field))]
attribute [local instance] instFieldFieldField_zkcSecurityExamples
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

end

@[zkc "[\"zkc.companion/0\",\"sumcheck::Sumcheck\",[\"instance\",\"zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071\"],\"implementation-law\",[\"label\",\"honest-pair\"]]"]
theorem Companions.small : small_goal := by
  intro model fieldLaw scope roles delivery original count handle scalar shape bounded small finite honest
  let : Field (model.Field field) := fieldLaw.out.toField
  have _machineIndex := small
  rw [SourceProducerRoot.actual_reference, SourceRootReference.actual_reference]
  dsimp only [SourceProducerRoot.reference, SourceRootReference.reference]
  change Pair scope (fun _ v => v = (.cons (some true) .nil : Values (Component model.Value) [.boolean])) _ _
  expose_source_composition
  assemble_source_pairs
    [SourceFamily.pair_contract model (SourceFamilySelections.installed .small) scope roles]
    simplifying [SourceFamily.optionalAnd, PropertyAssembly.done_bind, Option.bind, Option.map,
      Bool.and_true, Bool.true_and]

@[zkc "[\"zkc.companion/0\",\"sums::TwoSums\",[\"instance\",\"zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d\"],\"implementation-law\",[\"label\",\"honest-pair\"]]"]
theorem Companions.two : two_goal := by
  intro model fieldLaw scope roles leftDelivery rightDelivery left right count handle a b leftShape rightShape bounded small leftFinite rightFinite honest
  let : Field (model.Field field) := fieldLaw.out.toField
  have _machineIndex := small
  obtain ⟨ha, hb⟩ := honest
  rw [SourceProducerRoot.actual_reference, SourceRootReference.actual_reference]
  dsimp only [SourceProducerRoot.reference, SourceRootReference.reference]
  change Pair scope (fun _ v => v = (.cons (some true) .nil : Values (Component model.Value) [.boolean])) _ _
  expose_source_composition
  assemble_source_pairs
    [SourceFamily.pair_contract model (SourceFamilySelections.installed .twoSums) scope roles]
    simplifying [SourceFamily.conjunction_equation
      (program := source .twoSums) model (by bind_structured_bodies),
      SourceFamily.optionalAnd, PropertyAssembly.done_bind, Option.bind, Option.map,
      Bool.and_true, Bool.true_and]

#print axioms Companions.small
#print axioms Companions.two
end ZkcSecurity.Realizations.Sumcheck.SourcePairInstallations
