module

public import Zkc.Core.Program.Annotations
public import Zkc.Core.Meaning.Requirement

@[expose] public section

/-! Interpretation of Boolean expressions over positions and written operations. -/

namespace Zkc.Core.BodyAnalysis

section
variable {Raw : Type}

mutual
  /-- Every operation occurring in the expression belongs to the selected vocabulary. -/
  def Expr.UsesOnly (allowed : Raw → Bool) : Expr Raw → Bool
    | .arg _ => true
    | .apply op operands _ => allowed op && Exprs.UsesOnly allowed operands
  def Exprs.UsesOnly (allowed : Raw → Bool) : Exprs Raw → Bool
    | .nil => true
    | .cons e es => Expr.UsesOnly allowed e && Exprs.UsesOnly allowed es
end

end

section
variable {Raw Val : Type} (Run : Raw → List Val → List Val → Prop)

mutual
  /-- The value that an expression names, of the values of the positions. -/
  inductive Expr.Denotes (args : List Val) : Expr Raw → Val → Prop where
    | arg {position : Nat} {v : Val} (at_ : args[position]? = some v) :
        Expr.Denotes args (.arg position) v
    | apply {written : Raw} {operands : Exprs Raw} {result : Nat} {vs results : List Val} {v : Val}
        (named : Exprs.Denote args operands vs) (ran : Run written vs results)
        (picked : results[result]? = some v) : Expr.Denotes args (.apply written operands result) v
  /-- The values that expressions name, in order. -/
  inductive Exprs.Denote (args : List Val) : Exprs Raw → List Val → Prop where
    | nil : Exprs.Denote args .nil []
    | cons {first : Expr Raw} {others : Exprs Raw} {v : Val} {vs : List Val}
        (one : Expr.Denotes args first v) (rest : Exprs.Denote args others vs) :
        Exprs.Denote args (.cons first others) (v :: vs)
end

/-- An assertion holds of the values of the positions: it names a value, and the value reads
as true. Defined and true. -/
def Expr.Holds (R : Reading Val) (args : List Val) (assertion : Expr Raw) : Prop :=
  ∃ v, Expr.Denotes Run args assertion v ∧ R.bool v = some true

end

/-- The semantic interpretation contains the predicates in their declared order. -/
def Contract.requires {Raw : Type} (c : Contract Raw) := c.preconditions.map ContractClause.assertion
def Contract.ensures {Raw : Type} (c : Contract Raw) := c.postconditions.map ContractClause.assertion

end Zkc.Core.BodyAnalysis
