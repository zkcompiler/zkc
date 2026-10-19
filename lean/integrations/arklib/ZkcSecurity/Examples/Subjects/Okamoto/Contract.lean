module

public import ZkcExamples.Construction.OkamotoProof
public import Zkc.Source.Structured.ContractExecution
public import Zkc.Source.Structured.ContractElaboration

@[expose] public section

/-! The application contract of the subject `okamoto-proof`.

The admitted original of the compiled `example::Proof` Entry retains the
contract of the Okamoto protocol: the target clause `knowledge`, the relation
`Representation` it applies, and the relation's formula, recovered from the
Entry's own export by `bind_contract`. The clause reads the two bases and the
point at the verifier's input ports `0` to `2` and the two scalars at the
prover's input ports `3` and `4`, and the export's policy publishes ports `0` to
`2` (`selectors`, `published`, checked by the kernel). The witness relation of a
policy statement is the formula's actual process on the published values and
the witness pair (`holds`).
-/

namespace ZkcSecurity.Examples.Subjects.Okamoto.Contract
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Construction.OkamotoProof

set_option smartUnfolding false

/-- The contract the export retains. -/
def owner : ContractBinding imported := by bind_contract

def clauseIndex : Fin owner.contract.clauses.length := owner.namedClause "knowledge"

/-- The target clause. -/
def clause : ContractClause := owner.clause clauseIndex

/-- The relation application of the clause. -/
def application : ApplicationBinding owner clause.subject := by bind_contract

/-- The relation's formula. -/
def formulaBinding : FormulaBinding imported application.relation := by bind_contract

/-- The target clause is the protocol's only clause, a knowledge target. -/
theorem target : owner.contract.clauses = [clause] ∧ clause.kind = .target ∧ clause.name = "knowledge" :=
  ⟨rfl, rfl, rfl⟩

/-- The clause reads the bases and the point at the verifier's input ports `0`
to `2`, and the scalars at the prover's input ports `3` and `4`. -/
theorem selectors : clause.subject.selectors =
    [⟨.input, 0, "role00000001"⟩, ⟨.input, 1, "role00000001"⟩, ⟨.input, 2, "role00000001"⟩,
      ⟨.input, 3, "role00000000"⟩, ⟨.input, 4, "role00000000"⟩] :=
  rfl

set_option smartUnfolding true in
/-- The policy publishes the input ports `0` to `2`, in this order. -/
theorem published : participant.policy.publicInputs = [0, 1, 2] := by
  decide +kernel

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The formula's inputs from a policy statement and a witness pair. -/
def arguments : Values (assignment F G) [.group "bls12-381.g1", .group "bls12-381.g1", .group "bls12-381.g1"] →
    F × F → Values (assignment F G) formulaBinding.definition.inputs
  | .cons firstBase (.cons secondBase (.cons point .nil)), witnesses =>
      .cons firstBase (.cons secondBase (.cons point (.cons witnesses.1 (.cons witnesses.2 .nil))))

/-- The application's witness relation: the retained formula's process returns
true. -/
def holds (statement : Values (assignment F G) [.group "bls12-381.g1", .group "bls12-381.g1",
      .group "bls12-381.g1"]) (witnesses : F × F) : Prop :=
  formulaBinding.process (arguments statement witnesses) = .done (.cons true .nil)

theorem formula_process (firstBase secondBase point : G) (witnesses : F × F) :
    formulaBinding.process (arguments (.cons firstBase (.cons secondBase (.cons point .nil))) witnesses) =
      .done (.cons (decide (point = witnesses.1 • firstBase + witnesses.2 • secondBase)) .nil) := by
  rfl

theorem holds_iff (firstBase secondBase point : G) (witnesses : F × F) :
    holds (.cons firstBase (.cons secondBase (.cons point .nil))) witnesses ↔
      point = witnesses.1 • firstBase + witnesses.2 • secondBase := by
  unfold holds
  rw [formula_process]
  change (PIR.Proc.done (I := closedInterface)
    (.cons (decide (point = witnesses.1 • firstBase + witnesses.2 • secondBase)) .nil :
      Values (assignment F G) [.boolean]) = .done (.cons true .nil)) ↔ _
  simp

end ZkcSecurity.Examples.Subjects.Okamoto.Contract
