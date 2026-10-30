module

public import ZkcSecurityExamples.Sumcheck.SourceRootBounds
public import ZkcSecurity.Bindings.Sumcheck.SourceFamilyComposition
public import ZkcSecurity.Bindings.Sumcheck.SourceFamilyPublic
public import ZkcSecurity.Bindings.Source.PublicProperties
public import ZkcSecurity.Bindings.Source.PropertyAssembly
public meta import ZkcSecurityTools.SourceProperties.Builder
public meta import ZkcSecurityTools.SourceProperties.Assembly

@[expose] public section

/-! Actual occurrence-root rejection and costs at unrestricted nominal inputs.
The explicit distribution obligation ranges over every routed challenge origin.
Both invocations share the service and accumulated history; no independence
assumption or per-protocol connection is consumed here.
-/
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

variable (model : DomainModel) [fieldLaw : Fact (IsField (model.Field field))]
local instance fieldStructure : Field (model.Field field) := fieldLaw.out.toField

abbrev cuts := SourceFamilyPublic.cuts model
abbrev boundaries := SourceFamilyPublic.boundaries model

variable [samples : ∀ event : Domain.Event model.toCarriers, SampleableType (Domain.Raw event)]
  (price : ENNReal)

omit fieldLaw in
theorem escape_empty (history : List (PublicProperties.Event model.toCarriers))
    (event : PublicProperties.Event model.toCarriers) :
    PublicProperties.escape price history event (fun _ => False) :=
  SourceFamilyPublic.escape_empty model price history event

variable (sampling : ∀ (origin : Zkc.Construction.Origin)
    (request : origin.request = some (.draw field)) (p q : Polynomial (model.Field field)),
    p ≠ q → p.natDegree ≤ 1 → q.natDegree ≤ 1 →
    Pr{let raw ← $ᵗ (Domain.Raw (.challenge origin : Domain.Event model.toCarriers))}[
      p.eval (Zkc.Construction.Original.fieldReply origin field request raw) =
        q.eval (Zkc.Construction.Original.fieldReply origin field request raw)] ≤ price)

def no_steps (selection : Selection) (site : String) (handle : Nat)
    (original : List (model.Field field)) :=
  SourceFamilyPublic.no_steps model price sampling (SourceFamilySelections.installed selection)
    site handle original

def small_no (original : List (model.Field field)) (scalar : model.Field field) (count handle : Nat)
    (wrong : ¬ (count ≤ maximum .small ∧ original.length = 2^count ∧ scalar = original.sum))
    (history : List (PublicProperties.Event model.toCarriers)) :
    Derivation PublicProperties.interface (PublicProperties.escape price)
      (fun _ out => out = SourceInstallations.returned model .small (some false)) history
      (Occurrence.participant model (source .small) 1 (SourceRootReference.rootInputs model .small
        (.cons (some original) (.cons (some scalar) (.cons (some count) (.cons (some handle) .nil)))))) := by
  change ¬(count ≤ (SourceFamilySelections.installed .small).maximum ∧
    original.length = 2^count ∧ scalar = original.sum) at wrong
  rw [SourceRootReference.actual_reference]
  dsimp only [SourceRootReference.reference]
  change Derivation PublicProperties.interface (PublicProperties.escape price)
    (fun _ out => out = (.cons (some false) .nil : Values (Component model.Value) [.boolean])) history _
  exact source_property "retained normalized rejection" companions [] via by
    assemble_source_no
      [fun site raw rounds service scalar reached => SourceFamily.one_summary model
        (SourceFamilySelections.installed .small) site raw rounds service scalar
        PublicProperties.interface (PublicProperties.escape price) (escape_empty model price)
        (no_steps model price sampling .small site service raw) reached]
      simplifying [SourceInstallations.returned, SourceFamily.optionalAnd, PropertyAssembly.done_bind,
        Option.bind, Option.map, Option.some.injEq, Values.cons.injEq, Values.get, Bool.and_eq_true, Bool.eq_false_iff]

def two_no (left right : List (model.Field field)) (a b : model.Field field) (count handle : Nat)
    (wrong : ¬ (count ≤ maximum .twoSums ∧ left.length = 2^count ∧ right.length = 2^count ∧
      a = left.sum ∧ b = right.sum)) (history : List (PublicProperties.Event model.toCarriers)) :
    Derivation PublicProperties.interface (PublicProperties.escape price)
      (fun _ out => out = SourceInstallations.returned model .twoSums (some false)) history
      (Occurrence.participant model (source .twoSums) 1 (SourceRootReference.rootInputs model .twoSums
        (.cons (some left) (.cons (some right) (.cons (some a) (.cons (some b)
          (.cons (some count) (.cons (some handle) .nil)))))))) := by
  change ¬(count ≤ (SourceFamilySelections.installed .twoSums).maximum ∧ left.length = 2^count ∧
    right.length = 2^count ∧ a = left.sum ∧ b = right.sum) at wrong
  rw [SourceRootReference.actual_reference]
  dsimp only [SourceRootReference.reference]
  change Derivation PublicProperties.interface (PublicProperties.escape price)
    (fun _ out => out = (.cons (some false) .nil : Values (Component model.Value) [.boolean])) history _
  exact source_property "retained normalized rejection" companions [] via by
    assemble_source_no
      [fun site raw rounds service scalar reached => SourceFamily.one_summary model
        (SourceFamilySelections.installed .twoSums) site raw rounds service scalar
        PublicProperties.interface (PublicProperties.escape price) (escape_empty model price)
        (no_steps model price sampling .twoSums site service raw) reached]
      simplifying [SourceInstallations.returned, SourceFamily.conjunction_equation
        (program := source .twoSums) model (by bind_structured_bodies),
        SourceFamily.optionalAnd, PropertyAssembly.done_bind,
        Option.bind, Option.map, Option.some.injEq, Values.cons.injEq, Values.get, Bool.and_eq_true, Bool.eq_false_iff]

omit samples in
theorem small_cost (original : List (model.Field field)) (scalar : model.Field field) (count handle : Nat)
    (history : List (PublicProperties.Event model.toCarriers)) :
    Typed.ChargedCostBound PublicProperties.interface (fun _ _ => price)
      (Occurrence.participant model (source .small) 1 (SourceRootReference.rootInputs model .small
        (.cons (some original) (.cons (some scalar) (.cons (some count) (.cons (some handle) .nil))))))
      history (maximum .small • price) := by
  rw [SourceRootReference.actual_reference]
  dsimp only [SourceRootReference.reference]
  exact source_property "retained normalized cost" companions [] via by
    assemble_source_cost
      [fun site raw rounds service scalar reached => SourceFamily.one_cost model
        (SourceFamilySelections.installed .small) site raw rounds service scalar
        PublicProperties.interface (fun _ _ => price)
        (cuts model (context site) service) (boundaries model (context site)) price (fun _ => le_rfl) reached]
      simplifying [SourceFamily.optionalAnd, PropertyAssembly.done_bind]

omit samples in
theorem two_cost (left right : List (model.Field field)) (a b : model.Field field) (count handle : Nat)
    (history : List (PublicProperties.Event model.toCarriers)) :
    Typed.ChargedCostBound PublicProperties.interface (fun _ _ => price)
      (Occurrence.participant model (source .twoSums) 1 (SourceRootReference.rootInputs model .twoSums
        (.cons (some left) (.cons (some right) (.cons (some a) (.cons (some b)
          (.cons (some count) (.cons (some handle) .nil))))))))
      history (maximum .twoSums • price + maximum .twoSums • price) := by
  rw [SourceRootReference.actual_reference]
  dsimp only [SourceRootReference.reference]
  exact source_property "retained normalized cost" companions [] via by
    assemble_source_cost
      [fun site raw rounds service scalar reached => SourceFamily.one_cost model
        (SourceFamilySelections.installed .twoSums) site raw rounds service scalar
        PublicProperties.interface (fun _ _ => price)
        (cuts model (context site) service) (boundaries model (context site)) price (fun _ => le_rfl) reached]
      simplifying [SourceFamily.conjunction_equation (program := source .twoSums) model
        (by bind_structured_bodies), SourceFamily.optionalAnd, PropertyAssembly.done_bind]

#print axioms small_no
#print axioms two_no
#print axioms small_cost
#print axioms two_cost
end ZkcSecurity.Realizations.Sumcheck.SourcePublicInstallations
