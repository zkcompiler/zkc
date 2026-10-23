module

public import ZkcSecurity.Examples.Components.SmallSumcheckHelpers
public import ZkcSecurity.Examples.Generated.Components.SmallSumcheckRounds

@[expose] public section

/-! Mathematical helper laws for the generated actual table-round binding.
All structural selectors, sites, captures and whole-block equations are generated. -/
noncomputable section
set_option autoImplicit false
namespace ZkcSecurity.Examples.Components.SmallSumcheck
open Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Families.Sumcheck.TableComponent
open ZkcSecurity.Examples.Generated.Components.SmallSumcheckRounds

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

theorem round_helpers :
    ReadbackRound.HelperLaws (F := F) (G := G)
      ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs.imported.program round0.plan :=
  SumcheckDomainHelpers.round_helpers _ helper_bodies _ rfl rfl rfl rfl

end ZkcSecurity.Examples.Components.SmallSumcheck
