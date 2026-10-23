module

public import ZkcSecurity.Families.Sumcheck.CompiledValidatorOrigins
public import ZkcSecurity.Examples.Generated.Components.SmallSumcheckRounds
public import ZkcSecurity.Examples.Components.SmallSumcheckHelpers

@[expose] public section
noncomputable section

/-! Actual generated round origins and block, with the source append law. -/
set_option autoImplicit false
namespace ZkcSecurity.Examples.Components.SmallSumcheck.ValidatorRound
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Families.Sumcheck
open ZkcSecurity.Examples.Generated.Components.SmallSumcheckRounds

abbrev context := round0.context
abbrev program := ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs.imported.program
abbrev field := round0.plan.field
theorem field_eq : field = "bls12-381.fr" := rfl

abbrev plan := round0.plan.toPlan
abbrev sites := round0.schedule
abbrev queryOrigin (index : Nat) := sites.query index

theorem query_request (index : Nat) : (queryOrigin index).request = some (.draw field) :=
  sites.request index

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

theorem connection : CompiledValidator.RoundConnection (F := F) (G := G) field program context plan sites := by
  apply CompiledValidator.connectionOfOrigins round0.plan program context round0.bases round0.origins_checked
  intro point challenge
  exact SumcheckDomainHelpers.append (F := F) (G := G) program
    ZkcSecurity.Examples.Components.SmallSumcheck.helper_bodies.sumcheck point challenge

#print axioms connection
end ZkcSecurity.Examples.Components.SmallSumcheck.ValidatorRound
