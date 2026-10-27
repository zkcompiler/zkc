module

public import ZkcSecurity.Examples.Subjects.ChaumPedersen.Artifacts

public import ZkcExamples.Construction.ChaumPedersenProof
public import Zkc.Source.Structured.ContractExecution
public import Zkc.Source.Structured.ContractElaboration

@[expose] public section

/-! The application contract of the subject `chaum-pedersen`.

The admitted original of the compiled `example::EqualityProof` Entry retains the
contract of `sigma::ChaumPedersen`: the target clause `knowledge`, the relation
`DLogEquality` it applies, and the relation's formula, recovered from the
Entry's own export by `bind_contract`. The clause reads the two bases and the
two points at the verifier's input ports `0` to `3` and the scalar at the
prover's input port `4`, and the export's policy publishes ports `0` to `3`
(`selectors`, `published`, checked by the kernel). The witness relation of a
policy statement is the formula's actual process on the published values and
the witness scalar (`holds`).
-/

namespace ZkcSecurity.Examples.Subjects.ChaumPedersen.Contract
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Construction.ChaumPedersenProof

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
`3`, and the scalar at the prover's input port `4`. -/
theorem selectors : clause.subject.selectors =
    [⟨.input, 0, "role00000001"⟩, ⟨.input, 1, "role00000001"⟩, ⟨.input, 2, "role00000001"⟩,
      ⟨.input, 3, "role00000001"⟩, ⟨.input, 4, "role00000000"⟩] :=
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

/-- The formula's inputs from a policy statement and a witness. -/
def arguments : Values (assignment F G) [.group "bls12-381.g1", .group "bls12-381.g1", .group "bls12-381.g1",
      .group "bls12-381.g1"] → F → Values (assignment F G) formulaBinding.definition.inputs
  | .cons firstBase (.cons firstPoint (.cons secondBase (.cons secondPoint .nil))), witness =>
      .cons firstBase (.cons firstPoint (.cons secondBase (.cons secondPoint (.cons witness .nil))))

/-- The application's witness relation: the retained formula's process returns
true. -/
def holds (statement : Values (assignment F G) [.group "bls12-381.g1", .group "bls12-381.g1",
      .group "bls12-381.g1", .group "bls12-381.g1"]) (witness : F) : Prop :=
  formulaBinding.process (arguments statement witness) = .done (.cons true .nil)

theorem formula_process (firstBase firstPoint secondBase secondPoint : G) (witness : F) :
    formulaBinding.process (arguments (.cons firstBase (.cons firstPoint (.cons secondBase
        (.cons secondPoint .nil)))) witness) =
      .done (.cons (decide (firstPoint = witness • firstBase) && decide (secondPoint = witness • secondBase)) .nil) := by
  rfl

theorem holds_iff (firstBase firstPoint secondBase secondPoint : G) (witness : F) :
    holds (.cons firstBase (.cons firstPoint (.cons secondBase (.cons secondPoint .nil)))) witness ↔
      firstPoint = witness • firstBase ∧ secondPoint = witness • secondBase := by
  unfold holds
  rw [formula_process]
  change (PIR.Process.done (I := closedInterface) (.cons (decide (firstPoint = witness • firstBase) &&
    decide (secondPoint = witness • secondBase)) .nil : Values (assignment F G) [.boolean]) =
      .done (.cons true .nil)) ↔ _
  simp
  change (decide (firstPoint = witness • firstBase) && decide (secondPoint = witness • secondBase)) = true ↔
    firstPoint = witness • firstBase ∧ secondPoint = witness • secondBase
  simp only [Bool.and_eq_true, decide_eq_true_eq]

/-- Only private producer coordinates are used by the generic reader. -/
def embed (witness : F) : retained.Witness F G :=
  fun type selector => match type with
    | .field _ => if selector.port.index = 4 then some witness else none
    | _ => none

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Exact ordered application read, derived through the compiled policy. -/
theorem arguments_read (statement : artifacts.Statement F G) (witness : F) :
    retained.arguments statement (embed witness) = some (arguments statement witness) := by
  match statement with
  | .cons firstBase (.cons firstPoint (.cons secondBase (.cons secondPoint .nil))) => rfl

/-- The existing mathematical predicate is exactly the retained application. -/
theorem holds_pinned (statement : artifacts.Statement F G) (witness : F) :
    holds statement witness ↔ retained.Holds formulaBinding statement (embed witness) :=
  (retained.holds_iff_of_arguments formulaBinding statement (embed witness) (arguments statement witness)
    (arguments_read statement witness)).symm

end ZkcSecurity.Examples.Subjects.ChaumPedersen.Contract
