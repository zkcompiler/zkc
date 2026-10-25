module

public import ZkcExamples.Construction.SchnorrProof
public import ZkcExamples.Structured.SchnorrBinding
public import Zkc.Source.Structured.ContractExecution
public import Zkc.Source.Structured.ContractElaboration

@[expose] public section

/-! The authored knowledge target retained by the Proof Entry's own export.

The checked binding recovers the target clause, its relation application and the
retained DLog formula from `SchnorrProofData`. The relation is the formula's
actual process; it agrees with the Interactive import's relation, whose
snapshot retains the same relation record.
-/
namespace ZkcExamples.Construction.SchnorrProofBinding
open Zkc.Source Zkc.Source.Structured
open ZkcExamples.Construction.SchnorrProof

set_option smartUnfolding false

def owner : ContractBinding imported := by bind_contract

def clauseIndex : Fin owner.contract.clauses.length := owner.namedClause "knowledge"

def clause : ContractClause := owner.clause clauseIndex

theorem owner_is_entry : owner.protocol = program.payload.entry := rfl

def application : ApplicationBinding owner clause.subject := by bind_contract

def formulaBinding : FormulaBinding imported application.relation := by bind_contract

theorem all_clauses : owner.contract.clauses = [clause] := rfl

/-- Both imports retain the same relation record, including its digest
`zkl_dcbf81f97f37…` and formula. -/
theorem relations_eq :
    SchnorrProofData.snapshot.relations =
      ZkcExamples.Structured.SchnorrInteractiveData.snapshot.relations := by
  decide +kernel

variable {F G : Type} [Field F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

def arguments (base key : G) (witness : F) :
    Values (assignment F G) formulaBinding.definition.inputs :=
  .cons base (.cons key (.cons witness .nil))

/-- The Proof Entry's target relation: the retained formula's actual process. -/
def Relation (base key : G) (witness : F) : Prop :=
  formulaBinding.process (arguments base key witness) = .done (.cons true .nil)

theorem formula_process (base key : G) (witness : F) :
    formulaBinding.process (arguments base key witness) =
      .done (.cons (decide (key = witness • base)) .nil) := by
  rfl

theorem relation_iff (base key : G) (witness : F) :
    Relation base key witness ↔ key = witness • base := by
  unfold Relation
  rw [formula_process]
  change (PIR.Process.done (I := closedInterface)
    (.cons (decide (key = witness • base)) .nil : Values (assignment F G) [.boolean]) =
      .done (.cons true .nil)) ↔ _
  simp
  change decide (key = witness • base) = true ↔ key = witness • base
  simp only [decide_eq_true_eq]

theorem relation_eq (base key : G) (witness : F) :
    Relation base key witness ↔ decide (witness • base = key) = true := by
  rw [relation_iff, decide_eq_true_iff, eq_comm]

/-- The Proof Entry's relation is the Interactive import's relation. -/
theorem relation_iff_interactive (base key : G) (witness : F) :
    Relation base key witness ↔ ZkcExamples.Structured.SchnorrBinding.Relation base key witness := by
  rw [relation_iff, ZkcExamples.Structured.SchnorrBinding.relation_iff]

end ZkcExamples.Construction.SchnorrProofBinding
