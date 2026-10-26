module

public import ZkcExamples.Executable.SumcheckFamily

@[expose] public section

/-! Budget API for the exact retained Sumcheck Code and actual Domain Process.
The generalized maximum and loop invariant are in SumcheckFamily. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace ZkcExamples.Executable.SumcheckCharges
open Zkc.Construction Zkc.Executable Zkc.Source

abbrev validator : Validator := SumcheckProof.validator
abbrev context : Context := ZkcExamples.Construction.SumcheckProof.context
abbrev scalar : String := "bls12-381.fr"

abbrev charge := SumcheckFamily.charge
abbrev cost {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] :=
  SumcheckFamily.cost (F := F) (G := G)

theorem charge_eq (rounds : Nat) : charge rounds = 68 + 59 * rounds :=
  SumcheckFamily.charge_eq rounds


variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Every typed public claim and proof stream fits. No oracle or honesty
premise is needed: the certificate covers every reached typed query reply. -/
abbrev sufficient := @SumcheckFamily.sufficient

end ZkcExamples.Executable.SumcheckCharges
