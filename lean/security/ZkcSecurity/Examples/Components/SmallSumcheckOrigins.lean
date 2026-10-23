module

public import ZkcSecurity.Examples.Components.SmallSumcheckReadbackRound

@[expose] public section

/-! Both consumers use the same generated actual source occurrence binding. -/
noncomputable section
set_option autoImplicit false
namespace ZkcSecurity.Examples.Components.SmallSumcheck
open ZkcSecurity.Families.Sumcheck.TableComponent.ReadbackRound
open ZkcSecurity.Examples.Generated.Components.SmallSumcheckRounds

abbrev actualContext := round0.context

def actualOrigins (index : Nat) : Sites round0.plan actualContext index :=
  round0.sites index

end ZkcSecurity.Examples.Components.SmallSumcheck
