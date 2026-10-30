module

public import ZkcSecurityExamples.Subjects.SchnorrAnd.Artifacts

public import ZkcExamples.Construction.SchnorrAndProof
public import Zkc.Source.Structured.ContractExecution
public import Zkc.Source.Structured.ContractElaboration

@[expose] public section

/-! The application contract of the subject `schnorr-and`.

The admitted original of the compiled `example::AndProof` Entry retains the
contract of `sigma::SchnorrAnd`: the target clause `knowledge`, the relation
`DLogPair` it applies, and the relation's formula, recovered from the Entry's
own export by `bind_contract`. The clause reads the two bases and the two
points at the verifier's input ports `0` to `3` and the two scalars at the
prover's input ports `4` and `5`, and the export's policy publishes ports `0` to
`3` (`selectors`, `published`, checked by the kernel). The witness relation of a
policy statement is the formula's actual process on the published values and
the witness pair (`holds`).
-/

namespace ZkcSecurity.Examples.Subjects.SchnorrAnd.Contract
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Construction.SchnorrAndProof

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

/-- The clause reads the bases and points at the verifier's input ports `0` to
`3`, and the scalars at the prover's input ports `4` and `5`. -/
theorem selectors : clause.subject.selectors =
    [⟨.input, 0, "role00000001", false⟩, ⟨.input, 1, "role00000001", false⟩, ⟨.input, 2, "role00000001", false⟩,
      ⟨.input, 3, "role00000001", false⟩, ⟨.input, 4, "role00000000", false⟩, ⟨.input, 5, "role00000000", false⟩] :=
  rfl

set_option smartUnfolding true in
/-- The policy publishes the input ports `0` to `3`, in this order. -/
theorem published : participant.policy.publicInputs = [0, 1, 2, 3] := by
  decide +kernel

set_option smartUnfolding true in
/-- The admitted target, including its policy reading, fixed before evidence. -/
def retained : RetainedTarget compiled.imported artifacts.participant.policy artifacts.publics where
  owner := owner
  entry := rfl
  clauseIndex := clauseIndex
  target := rfl
  noResidual := rfl
  decision := by decide +kernel
  application := application
  booleanOutput := rfl
  publicTypes := by decide +kernel
  publicArity := by decide +kernel
  supported := by decide +kernel

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The formula's inputs from a policy statement and a witness pair. -/
def arguments : Values (assignment F G) [.group "bls12-381.g1", .group "bls12-381.g1", .group "bls12-381.g1",
      .group "bls12-381.g1"] → F × F → Values (assignment F G) formulaBinding.definition.inputs
  | .cons firstBase (.cons firstPoint (.cons secondBase (.cons secondPoint .nil))), witnesses =>
      .cons firstBase (.cons firstPoint (.cons secondBase (.cons secondPoint
        (.cons witnesses.1 (.cons witnesses.2 .nil)))))

/-- The application's witness relation: the retained formula's process returns
true. -/
def holds (statement : Values (assignment F G) [.group "bls12-381.g1", .group "bls12-381.g1",
      .group "bls12-381.g1", .group "bls12-381.g1"]) (witnesses : F × F) : Prop :=
  formulaBinding.process (arguments statement witnesses) = .done (.cons true .nil)

theorem formula_process (firstBase firstPoint secondBase secondPoint : G) (witnesses : F × F) :
    formulaBinding.process (arguments (.cons firstBase (.cons firstPoint (.cons secondBase
        (.cons secondPoint .nil)))) witnesses) =
      .done (.cons (decide (firstPoint = witnesses.1 • firstBase) &&
        decide (secondPoint = witnesses.2 • secondBase)) .nil) := by
  rfl

theorem holds_iff (firstBase firstPoint secondBase secondPoint : G) (witnesses : F × F) :
    holds (.cons firstBase (.cons firstPoint (.cons secondBase (.cons secondPoint .nil)))) witnesses ↔
      firstPoint = witnesses.1 • firstBase ∧ secondPoint = witnesses.2 • secondBase := by
  unfold holds
  rw [formula_process]
  change (PIR.Process.done (I := closedInterface) (.cons (decide (firstPoint = witnesses.1 • firstBase) &&
    decide (secondPoint = witnesses.2 • secondBase)) .nil : Values (assignment F G) [.boolean]) =
      .done (.cons true .nil)) ↔ _
  simp
  change (decide (firstPoint = witnesses.1 • firstBase) && decide (secondPoint = witnesses.2 • secondBase)) = true ↔
    firstPoint = witnesses.1 • firstBase ∧ secondPoint = witnesses.2 • secondBase
  simp only [Bool.and_eq_true, decide_eq_true_eq]

/-- Only private producer coordinates are used by the generic reader. -/
def embed (witnesses : F × F) : retained.Witness F G :=
  fun type selector => match type with
    | .field _ => if selector.port.index = 4 then some witnesses.1
        else if selector.port.index = 5 then some witnesses.2 else none
    | _ => none

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Exact ordered application read, derived through the compiled policy. -/
theorem arguments_read (statement : artifacts.Statement F G) (witnesses : F × F) :
    retained.arguments statement (embed witnesses) = some (arguments statement witnesses) := by
  match statement with
  | .cons firstBase (.cons firstPoint (.cons secondBase (.cons secondPoint .nil))) => rfl

/-- The existing mathematical predicate is exactly the retained application. -/
theorem holds_pinned (statement : artifacts.Statement F G) (witnesses : F × F) :
    holds statement witnesses ↔ retained.Holds formulaBinding statement (embed witnesses) :=
  (retained.holds_iff_of_arguments formulaBinding statement (embed witnesses) (arguments statement witnesses)
    (arguments_read statement witnesses)).symm

end ZkcSecurity.Examples.Subjects.SchnorrAnd.Contract
