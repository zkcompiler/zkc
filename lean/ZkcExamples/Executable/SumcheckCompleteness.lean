module

public import ZkcExamples.Executable.SumcheckCharges

@[expose] public section

/-! Honest-prover completeness of the executable Sumcheck verifier.

The honest producer of a Fiat–Shamir Sumcheck proof absorbs what the verifier
absorbs and draws what it draws: in each round it sends the sums of the low and
high halves of its current table, and then restricts the table at the challenge
the absorbed history determines (`honestRounds`). Its messages are framed and
encoded by a codec that the host's decoder inverts (`honestBytes`).

For every challenge function, every round count up to the Entry's static
maximum (`SumcheckProof.maximum`), every table of `2 ^ rounds` values with its
true sum as the claim, every initial transcript and expected binding, host
validation of the honest proof bytes accepts at every budget of at least
`charge rounds` (`honest_accepted`): 68, 129 and 190 instructions for zero, one
and two rounds. The proof is the family's
(`ZkcExamples.Executable.SumcheckFamily.honest_accepted`): it composes the charge
bound with `Zkc.Executable.validate_sufficient` and the lowering rule, and runs
the constructed validator's ideal meaning on the decoded honest proof, each
round by the family's round statement and the rounds by the fold invariant.
Nothing in it depends on the maximum.
-/

set_option autoImplicit false

namespace ZkcExamples.Executable.SumcheckCompleteness
open Zkc.Construction Zkc.Executable Zkc.Source
open ZkcExamples.Executable.SumcheckCharges

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The honest producer's messages for `count` rounds on the current table,
from the absorbed history. -/
def honestRounds (oracle : History F G → F) : History F G → List F → Nat → List F :=
  SumcheckFamily.honestRounds SumcheckProof.artifact oracle

/-- The honest proof bytes: the framing magic, the expected binding and every
message framed after its encoding. -/
def honestBytes (encode : F → List UInt8) (binding : List UInt8) (messages : List F) : List UInt8 :=
  SumcheckFamily.honestBytes encode binding messages

/-- Honest-prover completeness of the executable Sumcheck verifier. For every
challenge function, codec whose decoder inverts its encoder on the round
messages, budget of at least `charge rounds`, expected binding, initial
transcript and table of `2 ^ rounds` values with at most the Entry's static
maximum of rounds, host validation accepts the honest proof bytes of the
table's sum. -/
theorem honest_accepted (oracle : History F G → F) (decode : PhysicalType → List UInt8 → Option (Payload F G))
    (encode : F → List UInt8)
    (roundtrip : ∀ value, decode SumcheckProof.coordinate (encode value) = some (.field scalar value))
    (bounded : ∀ value, (encode value).length ≤ proofLimit) (budget : Nat) (binding : List UInt8)
    (bindingLength : binding.length = 32) (values : List F) (rounds : Nat) (admitted : rounds ≤ SumcheckProof.maximum)
    (shaped : values.length = 2 ^ rounds) (initial : History F G) (fits : charge rounds ≤ budget) :
    validate (m := Id) installed SumcheckProof.validator context oracle decode budget binding
      ZkcExamples.Construction.SumcheckProof.acceptancePosition
      (ZkcExamples.Construction.SumcheckProof.inputs values values.sum rounds) initial
      (honestBytes encode binding (honestRounds oracle initial values rounds)) = true := by
  have generic := SumcheckFamily.honest_accepted SumcheckProof.artifact oracle decode encode
    (by rw [SumcheckProof.artifact_coordinate, show SumcheckProof.artifact.names.scalar = scalar from
      SumcheckProof.names_scalar]; exact roundtrip)
    bounded budget binding bindingLength values rounds (by rw [SumcheckProof.artifact_maximum]; exact admitted)
    shaped initial fits
  rw [SumcheckProof.artifact_inputs, SumcheckProof.artifact_context, SumcheckProof.artifact_validator] at generic
  rw [ZkcExamples.Construction.SumcheckProof.acceptancePosition_eq]
  exact generic

end ZkcExamples.Executable.SumcheckCompleteness
