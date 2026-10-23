module

public import ZkcSecurity.Examples.Components.TwoSumsDomainHelpers
public import ZkcSecurity.Examples.Generated.Components.TwoSumsRounds

@[expose] public section

/-! Both sequential occurrences use generated actual whole-Process bindings
and one mathematical table family. No source offsets or site paths are authored. -/
noncomputable section
set_option autoImplicit false
namespace ZkcSecurity.Examples.Components.TwoSums
open ZkcSecurity.Families.Sumcheck.TableComponent
open ZkcSecurity.Examples.Generated.Components.TwoSumsRounds

abbrev roundPlan (second : Bool) : ReadbackRound.Plan :=
  if second then round1.plan else round0.plan

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

theorem round_helpers (second : Bool) :
    ReadbackRound.HelperLaws (F := F) (G := G)
      ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs.imported.program (roundPlan second) := by
  cases second <;> exact
    SumcheckDomainHelpers.round_helpers _ domain_bodies _ rfl rfl rfl rfl

end ZkcSecurity.Examples.Components.TwoSums
