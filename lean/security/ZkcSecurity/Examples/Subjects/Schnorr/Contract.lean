module

public import ZkcSecurity.Examples.Subjects.Schnorr.Artifacts

public import ZkcExamples.Construction.SchnorrProofBinding

@[expose] public section

/-! The application contract of the subject `schnorr`.

The admitted original of the compiled `example::Proof` Entry retains the
contract of the Schnorr protocol: the target clause `knowledge`, the relation
`DLog(base, point, scalar)` it applies, and the relation's formula
(`ZkcExamples.Construction.SchnorrProofBinding`, recovered from the snapshot by
`bind_contract`). The clause reads the formula's inputs at the protocol's input
ports `0` and `1` of the verifier role and port `2` of the prover role, and the
export's policy publishes ports `0` and `1` (`selectors`, `published`, checked
by the kernel). The witness relation of a policy statement is therefore the
formula's actual process on the published base and point and the witness
scalar (`holds`); it is the relation the export retains, not one an evidence
author chooses.
-/

namespace ZkcSecurity.Examples.Subjects.Schnorr.Contract
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Construction

set_option smartUnfolding false

/-- The target clause is the protocol's only clause, a knowledge target. -/
theorem target : SchnorrProofBinding.clause.kind = .target ∧ SchnorrProofBinding.clause.name = "knowledge" :=
  ⟨rfl, rfl⟩

/-- The clause reads the base and the point at the verifier's input ports `0`
and `1`, and the scalar at the prover's input port `2`. -/
theorem selectors : SchnorrProofBinding.clause.subject.selectors =
    [⟨.input, 0, "role00000001"⟩, ⟨.input, 1, "role00000001"⟩, ⟨.input, 2, "role00000000"⟩] :=
  rfl

set_option smartUnfolding true in
/-- The policy publishes the input ports `0` and `1`, in this order. -/
theorem published : SchnorrProof.participant.policy.publicInputs = [0, 1] := by
  decide +kernel

set_option smartUnfolding true in
/-- The admitted target, including its policy reading, fixed before evidence. -/
def retained : RetainedTarget compiled.imported artifacts.participant.policy artifacts.publics where
  owner := SchnorrProofBinding.owner
  entry := rfl
  clauseIndex := SchnorrProofBinding.clauseIndex
  target := rfl
  noResidual := rfl
  decision := by decide +kernel
  application := SchnorrProofBinding.application
  formula := SchnorrProofBinding.formulaBinding
  booleanOutput := rfl
  publicTypes := by decide +kernel
  publicArity := by decide +kernel
  supported := by decide +kernel

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The formula's inputs from a policy statement and a witness: the published
values at the clause's verifier ports, then the witness at its prover port. -/
def arguments : Values (assignment F G) [.group "bls12-381.g1", .group "bls12-381.g1"] → F →
    Values (assignment F G) SchnorrProofBinding.formulaBinding.definition.inputs
  | .cons base (.cons point .nil), witness => SchnorrProofBinding.arguments base point witness

/-- The application's witness relation: the retained formula's process returns
true. -/
def holds (statement : Values (assignment F G) [.group "bls12-381.g1", .group "bls12-381.g1"])
    (witness : F) : Prop :=
  SchnorrProofBinding.formulaBinding.process (arguments statement witness) = .done (.cons true .nil)

theorem holds_iff (base point : G) (witness : F) :
    holds (.cons base (.cons point .nil)) witness ↔ SchnorrProofBinding.Relation base point witness :=
  Iff.rfl

/-- Only private producer coordinates are used by the generic reader. -/
def embed (witness : F) : retained.Witness F G :=
  fun type _selector => match type with
    | .field _ => some witness
    | _ => none

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Exact ordered application read, derived through the compiled policy. -/
theorem arguments_read (statement : artifacts.Statement F G) (witness : F) :
    retained.arguments statement (embed witness) = some (arguments statement witness) := by
  match statement with
  | .cons base (.cons point .nil) => rfl

/-- The existing mathematical predicate is exactly the retained application. -/
theorem holds_pinned (statement : artifacts.Statement F G) (witness : F) :
    holds statement witness ↔ retained.Holds statement (embed witness) :=
  (retained.holds_iff_of_arguments statement (embed witness) (arguments statement witness)
    (arguments_read statement witness)).symm

end ZkcSecurity.Examples.Subjects.Schnorr.Contract
