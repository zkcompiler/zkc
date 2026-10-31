module

public import ZkcSecurityExamples.Sumcheck.SourcePublicGoals
public meta import ZkcSecurityTools.SourceProperties.Builder
public meta import ZkcTools.Companions

@[expose] public section

/-! Author mathematics for the independently generated source-property goals.
These proofs import no source-property consumer. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Sumcheck.SourcePublicInstallations
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Realizations.Sumcheck
open Zkc.Source Zkc.Source.Structured Zkc.Construction ReferenceLibrary Zkc.Transcript Zkc.Obligations
open ZkcExamples.Structured SumcheckReferenceInstallation TableComponent SourceIteration SourceRootProperties
open SumcheckSourceSelections hiding field
open ZkcSecurity.FiatShamir ZkcSecurity.Source
open OracleComp OracleSpec
attribute [local implicit_reducible] NormalForm.InputPattern.scope SourceRootReference.pattern

section
variable (model : DomainModel) [fieldLaw : Fact (IsField (model.Field field))]
attribute [local instance] fieldStructure

variable [samples : ∀ event : Domain.Event model.toCarriers, SampleableType (Domain.Raw event)]
  (price : ENNReal)

variable (sampling : ∀ (origin : Zkc.Construction.Origin)
    (request : origin.request = some (.draw field)) (p q : Polynomial (model.Field field)),
    p ≠ q → p.natDegree ≤ 1 → q.natDegree ≤ 1 →
    Pr{let raw ← $ᵗ (Domain.Raw (.challenge origin : Domain.Event model.toCarriers))}[
      p.eval (Zkc.Construction.Original.fieldReply origin field request raw) =
        q.eval (Zkc.Construction.Original.fieldReply origin field request raw)] ≤ price)

abbrev cuts := SourceFamilyPublic.cuts model
abbrev boundaries := SourceFamilyPublic.boundaries model

omit fieldLaw in
theorem escape_empty (history : List (PublicProperties.Event model.toCarriers))
    (event : PublicProperties.Event model.toCarriers) :
    PublicProperties.escape price history event (fun _ => False) :=
  SourceFamilyPublic.escape_empty model price history event

def no_steps (selection : Selection) (site : String) (handle : Nat)
    (original : List (model.Field field)) :=
  SourceFamilyPublic.no_steps model price sampling (SourceFamilySelections.installed selection)
    site handle original

end

@[zkc "[\"zkc.companion/0\",\"sumcheck::Sumcheck\",[\"instance\",\"zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071\"],\"implementation-law\",[\"label\",\"public-rejection\"]]"]
noncomputable def Companions.small_no : small_no_goal := by
  intro model fieldLaw samples price sampling original scalar count handle wrong history
  let : Field (model.Field field) := fieldLaw.out.toField
  change ¬(count ≤ (SourceFamilySelections.installed .small).maximum ∧
    original.length = 2^count ∧ scalar = original.sum) at wrong
  rw [SourceRootReference.actual_reference]
  dsimp only [SourceRootReference.reference]
  change Derivation PublicProperties.interface (PublicProperties.escape price)
    (fun _ out => out = (.cons (some false) .nil : Values (Component model.Value) [.boolean])) history _
  assemble_source_no
    [fun site raw rounds service scalar reached => SourceFamily.one_summary model
      (SourceFamilySelections.installed .small) site raw rounds service scalar
      PublicProperties.interface (PublicProperties.escape price) (escape_empty model price)
      (no_steps model price sampling .small site service raw) reached]
    simplifying [SourceInstallations.returned, SourceFamily.optionalAnd, PropertyAssembly.done_bind,
      Option.bind, Option.map, Option.some.injEq, Values.cons.injEq, Values.get, Bool.and_eq_true, Bool.eq_false_iff]

@[zkc "[\"zkc.companion/0\",\"sums::TwoSums\",[\"instance\",\"zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d\"],\"implementation-law\",[\"label\",\"public-rejection\"]]"]
noncomputable def Companions.two_no : two_no_goal := by
  intro model fieldLaw samples price sampling left right a b count handle wrong history
  let : Field (model.Field field) := fieldLaw.out.toField
  change ¬(count ≤ (SourceFamilySelections.installed .twoSums).maximum ∧ left.length = 2^count ∧
    right.length = 2^count ∧ a = left.sum ∧ b = right.sum) at wrong
  rw [SourceRootReference.actual_reference]
  dsimp only [SourceRootReference.reference]
  change Derivation PublicProperties.interface (PublicProperties.escape price)
    (fun _ out => out = (.cons (some false) .nil : Values (Component model.Value) [.boolean])) history _
  assemble_source_no
    [fun site raw rounds service scalar reached => SourceFamily.one_summary model
      (SourceFamilySelections.installed .twoSums) site raw rounds service scalar
      PublicProperties.interface (PublicProperties.escape price) (escape_empty model price)
      (no_steps model price sampling .twoSums site service raw) reached]
    simplifying [SourceInstallations.returned, SourceFamily.conjunction_equation
      (program := source .twoSums) model (by bind_structured_bodies),
      SourceFamily.optionalAnd, PropertyAssembly.done_bind,
      Option.bind, Option.map, Option.some.injEq, Values.cons.injEq, Values.get, Bool.and_eq_true, Bool.eq_false_iff]

@[zkc "[\"zkc.companion/0\",\"sumcheck::Sumcheck\",[\"instance\",\"zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071\"],\"implementation-law\",[\"label\",\"public-cost\"]]"]
theorem Companions.small_cost : small_cost_goal := by
  intro model fieldLaw price original scalar count handle history
  let : Field (model.Field field) := fieldLaw.out.toField
  rw [SourceRootReference.actual_reference]
  dsimp only [SourceRootReference.reference]
  assemble_source_cost
    [fun site raw rounds service scalar reached => SourceFamily.one_cost model
      (SourceFamilySelections.installed .small) site raw rounds service scalar
      PublicProperties.interface (fun _ _ => price)
      (cuts model (context site) service) (boundaries model (context site)) price (fun _ => le_rfl) reached]
    simplifying [SourceFamily.optionalAnd, PropertyAssembly.done_bind]

@[zkc "[\"zkc.companion/0\",\"sums::TwoSums\",[\"instance\",\"zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d\"],\"implementation-law\",[\"label\",\"public-cost\"]]"]
theorem Companions.two_cost : two_cost_goal := by
  intro model fieldLaw price left right a b count handle history
  let : Field (model.Field field) := fieldLaw.out.toField
  rw [SourceRootReference.actual_reference]
  dsimp only [SourceRootReference.reference]
  assemble_source_cost
    [fun site raw rounds service scalar reached => SourceFamily.one_cost model
      (SourceFamilySelections.installed .twoSums) site raw rounds service scalar
      PublicProperties.interface (fun _ _ => price)
      (cuts model (context site) service) (boundaries model (context site)) price (fun _ => le_rfl) reached]
    simplifying [SourceFamily.conjunction_equation (program := source .twoSums) model
      (by bind_structured_bodies), SourceFamily.optionalAnd, PropertyAssembly.done_bind]

#print axioms Companions.small_no
#print axioms Companions.two_no
#print axioms Companions.small_cost
#print axioms Companions.two_cost
end ZkcSecurity.Realizations.Sumcheck.SourcePublicInstallations
