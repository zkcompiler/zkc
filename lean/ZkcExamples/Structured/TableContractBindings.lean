module

public import Zkc.Source.Structured.ContractMeaning
public import Zkc.Source.Structured.ContractElaboration
public import ZkcExamples.Structured.TableMembershipLaws
public import ZkcExamples.Structured.TableIndexedReadLaws

@[expose] public section

/-! Interpret the exact retained table targets, including their selected formula
and ordered parameter/statement arguments. The laws describe source-model
invocation; native execution, capacity and codec correspondence remain separate. -/
namespace ZkcExamples.Structured.TableContractBindings
open Zkc.Source Zkc.Source.Structured

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000

def membershipOwner : ContractBinding TableMembershipViews.imported := by bind_contract

def membershipClause : ContractClause :=
  membershipOwner.clause (membershipOwner.namedClause "selected_rows")

def membershipApplication : ApplicationBinding membershipOwner membershipClause.subject := by
  bind_contract

def membershipFormula : FormulaBinding TableMembershipViews.imported
    membershipApplication.relation := by bind_contract

def readOwner : ContractBinding TableIndexedReadViews.imported := by bind_contract

def readClause : ContractClause := readOwner.clause (readOwner.namedClause "selected_read")

def readApplication : ApplicationBinding readOwner readClause.subject := by bind_contract

def readFormula : FormulaBinding TableIndexedReadViews.imported readApplication.relation := by
  bind_contract

theorem membership_inventory : membershipOwner.contract.clauses = [membershipClause] := rfl
theorem read_inventory : readOwner.contract.clauses = [readClause] := rfl

theorem membership_formula_bound : membershipFormula.original.name =
    TableMembershipBodies.formulaHelper.name := rfl

theorem read_formula_bound : readFormula.original.name = TableIndexedReadBodies.formulaHelper.name := rfl

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

theorem membership_formula_equation (table : List F)
    (queries : List (TableMembershipLaws.QueryValue F)) :
    membershipFormula.invokeRelation (F := F) (G := G) (.cons table (.cons queries .nil)) =
      if TableMembershipLaws.Admissible table queries then
        .done (.cons (PIR.Relation.Table.membership table
          (queries.map TableMembershipLaws.decodeQuery)) .nil)
      else .halt .exhausted := by
  exact TableMembershipLaws.formula_equation table queries

theorem read_formula_equation (table : List F) (position : Nat) (value : F) :
    readFormula.invokeRelation (F := F) (G := G)
      (.cons table (.cons position (.cons value .nil))) =
      if table.length < indexLimit then
        .done (.cons (PIR.Relation.Table.indexedRead table position value) .nil)
      else .halt .exhausted := by
  exact TableIndexedReadLaws.formula_equation table position value

variable {membershipEnvironment : RelationEnvironment TableMembershipViews.imported F G}
variable {readEnvironment : RelationEnvironment TableIndexedReadViews.imported F G}

def membershipTarget : InterpretedApplication membershipOwner membershipClause.subject F G
    membershipEnvironment where
  binding := membershipApplication
  interpretation := .formula membershipFormula rfl
    (fun args => TableMembershipLaws.Admissible (args.get .here) (args.get (.there .here)))
    (fun args => PIR.Relation.Table.Membership (args.get .here)
      ((args.get (.there .here)).map TableMembershipLaws.decodeQuery))
    (fun args => decidable_of_iff _ (PIR.Relation.Table.membership_exact (args.get .here)
      ((args.get (.there .here)).map TableMembershipLaws.decodeQuery)))

def readTarget : InterpretedApplication readOwner readClause.subject F G readEnvironment where
  binding := readApplication
  interpretation := .formula readFormula rfl
    (fun args => (args.get .here).length < indexLimit)
    (fun args => PIR.Relation.Table.IndexedRead (args.get .here)
      (args.get (.there .here)) (args.get (.there (.there .here))))
    (fun args => decidable_of_iff _ (PIR.Relation.Table.indexedRead_exact (args.get .here)
      (args.get (.there .here)) (args.get (.there (.there .here)))))

theorem membership_formula_law : (membershipTarget (F := F) (G := G)
    (membershipEnvironment := membershipEnvironment)).interpretation.FormulaLaw := by
  intro args admissible
  cases args with | cons table rest => ?_
  cases rest with | cons queries rest => ?_
  cases rest
  change membershipFormula.invokeRelation (.cons table (.cons queries .nil)) = _
  erw [membership_formula_equation, ite_eq_left admissible]
  congr 2
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, PIR.Relation.Table.membership_exact]
  rfl

theorem read_formula_law : (readTarget (F := F) (G := G)
    (readEnvironment := readEnvironment)).interpretation.FormulaLaw := by
  intro args admissible
  cases args with | cons table rest => ?_
  cases rest with | cons position rest => ?_
  cases rest with | cons value rest => ?_
  cases rest
  change readFormula.invokeRelation (.cons table (.cons position (.cons value .nil))) = _
  erw [read_formula_equation, ite_eq_left admissible]
  congr 2
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, PIR.Relation.Table.indexedRead_exact]
  rfl

end ZkcExamples.Structured.TableContractBindings
