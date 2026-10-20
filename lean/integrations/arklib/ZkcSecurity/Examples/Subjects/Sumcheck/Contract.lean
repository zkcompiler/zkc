module

public import ZkcExamples.Construction.SumcheckProof
public import ZkcExamples.Structured.SumcheckContractBindings

@[expose] public section

/-! The application contract of the subject `sumcheck`.

The admitted original of the compiled `example::Proof` Entry, the Sumcheck
source, retains the target clause `public_sum`: the relation
`Sum(values, claim)`, whose formula states that the claim is the total of the
public vector, applied at the verifier's input ports `0` and `1`
(`ZkcExamples.Structured.SumcheckContractBindings`, recovered from the snapshot
by `bind_contract`). The export's policy publishes ports `0`, `1` and `2`, the
vector, the claim and the round count (`selectors`, `published`, checked by the
kernel). A policy statement is false when the formula's actual process on its
vector and claim does not return true (`falseStatement`): the relation reads the
raw vector, whatever its length, so a statement whose vector has no table at the
round count is false unless its claim is the vector's total. -/

namespace ZkcSecurity.Examples.Subjects.Sumcheck.Contract
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured

set_option smartUnfolding false

/-- The target clause is the protocol's `public_sum` target. -/
theorem target : SumcheckContractBindings.publicClause.kind = .target ∧
    SumcheckContractBindings.publicClause.name = "public_sum" :=
  ⟨rfl, rfl⟩

/-- The clause reads the vector and the claim at the verifier's input ports `0`
and `1`. -/
theorem selectors : SumcheckContractBindings.publicClause.subject.selectors =
    [⟨.input, 0, "role00000001"⟩, ⟨.input, 1, "role00000001"⟩] :=
  rfl

set_option smartUnfolding true in
/-- The policy publishes the input ports `0`, `1` and `2`, in this order. -/
theorem published : ZkcExamples.Construction.SumcheckProof.participant.policy.publicInputs = [0, 1, 2] := by
  decide +kernel

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

/-- The application's claim: a policy statement is false when the retained
formula does not return true on its vector and claim. -/
def falseStatement :
    Values (assignment F G) [.vector "bls12-381.fr", .field "bls12-381.fr", .index] → Prop
  | .cons raw (.cons claim (.cons _ .nil)) => ¬ SumcheckContractBindings.PublicTruth (G := G) raw claim

theorem falseStatement_iff (raw : List F) (claim : F) (rounds : Nat) :
    falseStatement (G := G) (.cons raw (.cons claim (.cons rounds .nil))) ↔
      ¬ SumcheckContractBindings.PublicTruth (G := G) raw claim :=
  Iff.rfl

end ZkcSecurity.Examples.Subjects.Sumcheck.Contract
