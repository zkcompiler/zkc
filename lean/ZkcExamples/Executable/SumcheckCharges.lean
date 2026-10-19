module

public import ZkcExamples.Executable.SumcheckProof

@[expose] public section

/-! The charges of the executable Sumcheck verifier.

A run of the compiled Sumcheck validator charges at most `charge rounds`
instructions for a table of `2 ^ rounds` values, whatever the claim, the proof
and the challenge answers (`sufficient`). The charge is derived from the
reading (`ZkcExamples.Executable.SumcheckFamily.Artifact.charge`): the empty
point's call and body, the loop's entry, then per round the round's charge,
which evaluating the reading's code gives, and its yield, then the terminal
check's call and body and the return. For this Entry it is `68 + 59 · rounds`
(`charge_eq`): 39 per round, the point extension's body included, and the
terminal check charging `62 + 20 · n` on a well-shaped table and a point of `n`
coordinates (`check_cost`). The bound holds for every round count; it uses the
Entry's static maximum only as the loop's own bound.
-/

set_option autoImplicit false

namespace ZkcExamples.Executable.SumcheckCharges
open Zkc.Construction Zkc.Executable Zkc.Source
open ZkcExamples.Structured.SumcheckHelperBodies

abbrev validator : Validator := SumcheckProofProgramData.validator
abbrev participant : Participant := ZkcExamples.Construction.SumcheckProof.participant
abbrev context : Context := ZkcExamples.Construction.SumcheckProof.context

/-- The scalar field's domain. -/
abbrev scalar : String := "bls12-381.fr"

/-- The instructions a complete run charges for `rounds` rounds, derived from
the reading. -/
def charge (rounds : Nat) : Nat := SumcheckProof.artifact.charge rounds

/-- A round charges 38 instructions before its yield: evaluating the reading's
code of one round, the point extension's body bounded by evaluating its local
function. -/
theorem roundCharge_eq : SumcheckProof.artifact.roundCharge = 38 := by decide +kernel

/-- The derived charge for this Entry. -/
theorem charge_eq (rounds : Nat) : charge rounds = 68 + 59 * rounds := by
  simp only [charge, SumcheckFamily.Artifact.charge, SumcheckFamily.Artifact.checkCharge, chargeSum_const,
    roundCharge_eq]
  ring

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

abbrev table := helperTable ZkcExamples.Construction.SumcheckProof.program F G

/-- The terminal check's charge on a well-shaped table: what the helper call
charges for its body. -/
theorem check_cost {xs point : List F} {claim : F} (small : point.length < 64)
    (shaped : xs.length = 2 ^ point.length) :
    helperCost installed validator checkHelper.name
      [(.vector "bls12-381.fr" xs : Value F G), .vector "bls12-381.fr" point,
        .data (.field "bls12-381.fr" claim)] = 62 + 20 * point.length :=
  SumcheckHelpers.check_cost small shaped

/-- On a table of `2 ^ rounds` values, every run of the reading charges at most
`charge rounds` instructions, whatever the claim, the proof and the challenge
answers. -/
theorem sufficient (budget : Nat) (values : List F) (claim : F) (rounds : Nat) (initial : History F G)
    (proof : Proof F G) (shaped : values.length = 2 ^ rounds) (fits : charge rounds ≤ budget) :
    Sufficient context table (helperCost installed validator) budget SumcheckProof.lowered
      (ZkcExamples.Construction.SumcheckProof.inputs values claim rounds ++ [.transcript initial]) proof := by
  have generic := SumcheckFamily.sufficient SumcheckProof.artifact budget values claim rounds initial proof shaped fits
  rw [SumcheckProof.artifact_inputs, SumcheckProof.artifact_context, SumcheckProof.artifact_program,
    SumcheckProof.artifact_validator, SumcheckProof.artifact_lowered] at generic
  exact generic

end ZkcExamples.Executable.SumcheckCharges
