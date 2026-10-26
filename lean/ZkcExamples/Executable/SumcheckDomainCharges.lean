module

public import ZkcExamples.Executable.SumcheckDomainFamily

@[expose] public section

/-! Budget API for the exact retained Sumcheck Code and actual Domain Process.
The generalized maximum and loop invariant are in SumcheckDomainFamily. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace ZkcExamples.Executable.SumcheckDomainCharges
open Zkc.Construction Zkc.Executable Zkc.Source

abbrev charge := SumcheckDomainFamily.charge
abbrev cost {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] :=
  SumcheckDomainFamily.cost (F := F) (G := G)

theorem charge_eq (rounds : Nat) : charge rounds = 68 + 59 * rounds :=
  SumcheckDomainFamily.charge_eq rounds


variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Every typed public claim and proof stream fits. No oracle or honesty
premise is needed: the certificate covers every reached typed query reply. -/
abbrev sufficient := @SumcheckDomainFamily.sufficient

end ZkcExamples.Executable.SumcheckDomainCharges
