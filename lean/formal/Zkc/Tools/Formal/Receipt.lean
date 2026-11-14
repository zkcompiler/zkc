import Lean
import Zkc.Formal.Receipt

/-! The statement of a theorem, read from the theorem.

`statement_of% name` is the `Zkc.Formal.Statement` of the theorem `name`: its conclusion; the
values it ranges over; the conditions on them, which are its hypotheses that mention one of
them; its other hypotheses, which are closed propositions; and the axioms that its proof uses.
A theorem whose proof uses an axiom other than Lean's three standard ones has no statement
here: the term is refused, so that no receipt is made of it.
-/

open Lean Meta Elab Term

namespace Zkc.Formal

deriving instance ToExpr for Statement

/-- The axioms that a receipt may carry. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- A term as text, on lines of a hundred characters. -/
def printed (e : Expr) : MetaM String :=
  withOptions (fun options => pp.fullNames.set options true) do
    return (← ppExpr e).pretty 100

elab "statement_of% " name:ident : term => do
  let constant ← realizeGlobalConstNoOverloadWithInfo name
  let info ← getConstInfo constant
  unless info matches .thmInfo _ do
    throwError "`{constant}` is not a theorem"
  let axioms ← collectAxioms constant
  for used in axioms do
    unless standardAxioms.contains used do
      throwError "the proof of `{constant}` uses the axiom `{used}`"
  let statement ← forallTelescope info.type fun variables conclusion => do
    let mut ranges : Array String := #[]
    let mut conditions : Array String := #[]
    let mut hypotheses : Array String := #[]
    for bound in variables do
      let type ← instantiateMVars (← inferType bound)
      if ← isProp type then
        if variables.any fun other => type.containsFVar other.fvarId! then
          conditions := conditions.push (← printed type)
        else
          hypotheses := hypotheses.push (← printed type)
      else
        ranges := ranges.push s!"{← bound.fvarId!.getUserName} : {← printed type}"
    let concluded ← printed conclusion
    let used := axioms.toList.map (·.toString)
    return Statement.mk constant.toString concluded ranges.toList conditions.toList
      hypotheses.toList used
  return toExpr statement

end Zkc.Formal
