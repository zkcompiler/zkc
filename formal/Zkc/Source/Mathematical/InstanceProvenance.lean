import Zkc.Source.Mathematical.ClosedInstances

/-! Functional call identity, independent of certificate construction.

Two certificates for the same parent instance and authored call use select the
same closed key. This justifies exact-key resolution when identical call uses
occur at different sites, and when the proof table and source graph retain
separately constructed certificates for an instance.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.ClosedInstances

theorem Instance.unique {source key} (first second : Instance source key) : first = second := by
  cases first with
  | mk declaration arity bounds roles roleBounds injective roots rootBounds =>
      cases second with
      | mk other arity' bounds' roles' roleBounds' injective' roots' rootBounds' =>
          have same := declaration.unique other
          cases same
          rfl

theorem Roots.functional {available references first second}
    (left : Roots available references first) (right : Roots available references second) : first = second := by
  induction left generalizing second with
  | nil => cases right; rfl
  | cons selected rest ih =>
      cases right with
      | cons other tail =>
          exact congr (congrArg List.cons (Option.some.inj (selected.symm.trans other))) (ih tail)

theorem Key.equal {first second : Key}
    (definition : first.definition = second.definition) (statics : first.statics = second.statics)
    (roles : first.roles = second.roles) (roots : first.roots = second.roots) : first = second := by
  cases first
  cases second
  simp_all

theorem Call.target_eq_of_use {source key} {parent : Instance source key} {firstSite secondSite}
    (first : Call parent firstSite) (second : Call parent secondSite) (same : firstSite.use = secondSite.use) :
    first.target = second.target := by
  cases firstSite with
  | mk firstIndex firstUse =>
      cases secondSite with
      | mk secondIndex secondUse =>
          simp only at same
          subst secondUse
          cases first with
          | mk earlier declaration statics roles roots rootSelection target exactDefinition exactStatics exactRoles exactRoots =>
              cases second with
              | mk earlier' other statics' roles' roots' rootSelection' target' exactDefinition' exactStatics' exactRoles' exactRoots' =>
                  have declarationSame := declaration.unique other
                  cases declarationSame
                  apply Key.equal
                  · exact exactDefinition.trans exactDefinition'.symm
                  · exact exactStatics.trans ((statics.evaluations_unique statics' Fin.elim0).trans exactStatics'.symm)
                  · exact exactRoles.trans ((roles.selection.values_unique roles'.selection).trans exactRoles'.symm)
                  · exact exactRoots.trans ((rootSelection.functional rootSelection').trans exactRoots'.symm)

mutual
  theorem StepCalls.functional {step : Raw.Step} {left right : List CallSite}
      (first : StepCalls step left) (second : StepCalls step right) : left = right := by
    cases first with
    | pure => cases second; rfl
    | «local» => cases second; rfl
    | query => cases second; rfl
    | «guard» => cases second; rfl
    | message => cases second; rfl
    | invoke => cases second; rfl
    | «repeat» site count carried initial captures nested =>
        cases second with
        | «repeat» _ _ _ _ _ other => exact BodyCalls.functional nested other
  theorem StepsCalls.functional {steps : List Raw.Step} {left right : List CallSite}
      (first : StepsCalls steps left) (second : StepsCalls steps right) : left = right := by
    cases first with
    | nil => cases second; rfl
    | cons head tail =>
        cases second with
        | cons other rest =>
            rw [StepCalls.functional head other, StepsCalls.functional tail rest]
  theorem BodyCalls.functional {body : Raw.Body} {left right : List CallSite}
      (first : BodyCalls body left) (second : BodyCalls body right) : left = right := by
    cases first with
    | mk terminal checked =>
        cases second with
        | mk _ other => exact StepsCalls.functional checked other
end

theorem targets_unique {source key} {parent : Instance source key} {sites}
    (first second : Values (Call parent) sites) : targets first = targets second := by
  induction first with
  | nil => cases second; rfl
  | cons first rest ih =>
      cases second with
      | cons second tail =>
          simp only [targets, List.cons.injEq]
          exact ⟨first.target_eq_of_use second rfl, ih tail⟩

theorem Node.determined {source key} (first second : Node source key) :
    first.sites = second.sites ∧ targets first.children = targets second.children := by
  cases first with
  | mk checked sites coverage children =>
      cases second with
      | mk other otherSites otherCoverage otherChildren =>
          have same := checked.unique other
          cases same
          have sameSites := coverage.functional otherCoverage
          subst otherSites
          exact ⟨rfl, targets_unique children otherChildren⟩

end Zkc.Source.Mathematical.ClosedInstances
