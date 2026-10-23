module

public import ZkcSecurity.Families.Sumcheck.CompiledValidatorOrigins
public import ZkcSecurity.Examples.Generated.Components.TwoSumsRounds
public import ZkcSecurity.Examples.Components.TwoSumsDomainHelpers

@[expose] public section
noncomputable section

/-! Actual generated round origins and block, with the source append law. -/
set_option autoImplicit false
namespace ZkcSecurity.Examples.Components.TwoSums.ValidatorRightRound
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Families.Sumcheck
open ZkcSecurity.Examples.Generated.Components.TwoSumsRounds

abbrev context := round1.context
abbrev program := ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs.imported.program
abbrev field := round1.plan.field
theorem field_eq : field = "bls12-381.fr" := rfl

abbrev plan := round1.plan.toPlan
abbrev sites := round1.schedule
abbrev queryOrigin (index : Nat) := sites.query index

theorem query_request (index : Nat) : (queryOrigin index).request = some (.draw field) :=
  sites.request index

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

theorem connection : CompiledValidator.RoundConnection (F := F) (G := G) field program context plan sites := by
  apply CompiledValidator.connectionOfOrigins round1.plan program context round1.bases round1.origins_checked
  intro point challenge
  exact SumcheckDomainHelpers.append (F := F) (G := G) program
    ZkcSecurity.Examples.Components.TwoSums.domain_bodies.sumcheck point challenge

#print axioms connection
end ZkcSecurity.Examples.Components.TwoSums.ValidatorRightRound
