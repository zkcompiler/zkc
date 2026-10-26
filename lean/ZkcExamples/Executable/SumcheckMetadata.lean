module

public import ZkcExamples.Executable.SumcheckProofFacts
public import ZkcExamples.Executable.SumcheckShape

@[expose] public section

/-! Physical messages, receive plan and static names of the retained Sumcheck
Entry. These facts do not depend on an execution or security proof. -/
set_option autoImplicit false
namespace ZkcExamples.Executable.SumcheckProof
open Zkc.Construction Zkc.Executable
open ZkcExamples.Construction

/-- A round message coordinate: a scalar field element. -/
abbrev coordinate : PhysicalType := ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩

/-- The receive types of one round: its two message coordinates. -/
abbrev round : List PhysicalType := [coordinate, coordinate]

/-- The Entry's static maximum: the round loop's bound. -/
def maximum : Nat := SumcheckShape.maximumOf SumcheckProof.participant.instructions

/-- This Entry admits at most two rounds. -/
theorem maximum_eq : maximum = 2 := by decide +kernel

/-- The names of this Entry's sites, templates and helpers. -/
def names : SumcheckShape.Names := SumcheckShape.Names.of SumcheckProof.participant.instructions

set_option maxRecDepth 20000 in
/-- The receive plan: a loop over the round count, at most `maximum` rounds,
each receiving two coordinates. -/
theorem plan_eq : lowered.plan = [.loop 2 maximum [.receive coordinate, .receive coordinate]] := by
  decide +kernel

/-- The receive types of a run: two field messages per admitted round. -/
def receives (rounds : Nat) : List PhysicalType :=
  if rounds ≤ maximum then (List.replicate rounds round).flatten else []

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem plan_types (values : List F) (claim : F) (rounds : Nat) :
    Plan.types (SumcheckProof.inputs (G := G) values claim rounds) lowered.plan = receives rounds := by
  rw [plan_eq]
  by_cases admitted : rounds ≤ maximum <;>
    simp [Plan.types, SumcheckProof.inputs, receives, admitted, round]


end ZkcExamples.Executable.SumcheckProof
