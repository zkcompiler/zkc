module

public import ZkcSecurityExamples.Sumcheck.SourceRootBounds
public import ZkcSecurity.Bindings.Sumcheck.SourceFamilyComposition
public import ZkcSecurity.Bindings.Sumcheck.SourceFamilyPublic
public import ZkcSecurity.Bindings.Source.PublicProperties
public import ZkcSecurity.Bindings.Source.PropertyAssembly
public meta import ZkcTools.Companions.Goals

@[expose] public section

/-! Fixed source-property signatures. Header-only commands generate independent
goals before any companion or consumer is imported. -/
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

variable [samples : ∀ event : Domain.Event model.toCarriers, SampleableType (Domain.Raw event)]
  (price : ENNReal)

variable (sampling : ∀ (origin : Zkc.Construction.Origin)
    (request : origin.request = some (.draw field)) (p q : Polynomial (model.Field field)),
    p ≠ q → p.natDegree ≤ 1 → q.natDegree ≤ 1 →
    Pr{let raw ← $ᵗ (Domain.Raw (.challenge origin : Domain.Event model.toCarriers))}[
      p.eval (Zkc.Construction.Original.fieldReply origin field request raw) =
        q.eval (Zkc.Construction.Original.fieldReply origin field request raw)] ≤ price)

companion_goal small_no_goal for def small_no (original : List (model.Field field)) (scalar : model.Field field) (count handle : Nat)
    (wrong : ¬ (count ≤ maximum .small ∧ original.length = 2^count ∧ scalar = original.sum))
    (history : List (PublicProperties.Event model.toCarriers)) :
    Derivation PublicProperties.interface (PublicProperties.escape price)
      (fun _ out => out = SourceInstallations.returned model .small (some false)) history
      (Occurrence.participant model (source .small) 1 (SourceRootReference.rootInputs model .small
        (.cons (some original) (.cons (some scalar) (.cons (some count) (.cons (some handle) .nil))))))

companion_goal two_no_goal for def two_no (left right : List (model.Field field)) (a b : model.Field field) (count handle : Nat)
    (wrong : ¬ (count ≤ maximum .twoSums ∧ left.length = 2^count ∧ right.length = 2^count ∧
      a = left.sum ∧ b = right.sum)) (history : List (PublicProperties.Event model.toCarriers)) :
    Derivation PublicProperties.interface (PublicProperties.escape price)
      (fun _ out => out = SourceInstallations.returned model .twoSums (some false)) history
      (Occurrence.participant model (source .twoSums) 1 (SourceRootReference.rootInputs model .twoSums
        (.cons (some left) (.cons (some right) (.cons (some a) (.cons (some b)
          (.cons (some count) (.cons (some handle) .nil))))))))


omit samples in
set_option maxHeartbeats 800000 in
companion_goal small_cost_goal for theorem small_cost (original : List (model.Field field)) (scalar : model.Field field) (count handle : Nat)
    (history : List (PublicProperties.Event model.toCarriers)) :
    Typed.ChargedCostBound PublicProperties.interface (fun _ _ => price)
      (Occurrence.participant model (source .small) 1 (SourceRootReference.rootInputs model .small
        (.cons (some original) (.cons (some scalar) (.cons (some count) (.cons (some handle) .nil))))))
      history (maximum .small • price)


omit samples in
set_option maxHeartbeats 800000 in
companion_goal two_cost_goal for theorem two_cost (left right : List (model.Field field)) (a b : model.Field field) (count handle : Nat)
    (history : List (PublicProperties.Event model.toCarriers)) :
    Typed.ChargedCostBound PublicProperties.interface (fun _ _ => price)
      (Occurrence.participant model (source .twoSums) 1 (SourceRootReference.rootInputs model .twoSums
        (.cons (some left) (.cons (some right) (.cons (some a) (.cons (some b)
          (.cons (some count) (.cons (some handle) .nil))))))))
      history (maximum .twoSums • price + maximum .twoSums • price)

end ZkcSecurity.Realizations.Sumcheck.SourcePublicInstallations
