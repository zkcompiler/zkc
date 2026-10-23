module

public import ZkcSecurity.Examples.Components.TwoSumsReadbackRounds

@[expose] public section

/-! The two actual schedules come from the generated source occurrence data. -/
noncomputable section
set_option autoImplicit false
namespace ZkcSecurity.Examples.Components.TwoSums
open ZkcSecurity.Families.Sumcheck.TableComponent.ReadbackRound
open ZkcSecurity.Examples.Generated.Components.TwoSumsRounds

abbrev actualContext := round0.context

def actualOrigins (second : Bool) (index : Nat) : Sites (roundPlan second) actualContext index := by
  cases second
  · exact round0.sites index
  · exact round1.sites index

end ZkcSecurity.Examples.Components.TwoSums
