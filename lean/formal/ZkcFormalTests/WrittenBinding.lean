import Lean
import Zkc.Subject.WrittenGoal

/-! Read a written subject as a client of the issued module. Mathematical equality checks
the meaning of a selection. Inspecting the retained declaration reference distinguishes two
source goals with identical data. -/

namespace ZkcFormalTests.WrittenBinding
open Zkc.Core hiding Name
open Zkc.Subject

private def statementPlaces {V : Vocabulary} {ports : List (LTy V)} {p v : Role} :
    {ts : List V.Ty} → HList (SharedPort ports p v) ts → List Nat
  | _, .nil => []
  | _, .cons slot rest => slot.member.index :: statementPlaces rest

private def witnessPlaces {V : Vocabulary} {ports : List (LTy V)} :
    {ts : List V.Ty} → HList (PortRef ports) ts → List Nat
  | _, .nil => []
  | _, .cons slot rest => slot.member.index :: witnessPlaces rest

/-- Observable source coordinates, including the distinction between short syntax and an
explicitly supplied witness vector. Caps are compared as complete tables in the client. -/
def operands {V : Vocabulary} {pkg : Package V} {root : WrittenRoot pkg}
    (g : WrittenGoal root) : Nat × Nat × Nat × List Nat × Option (List Nat) :=
  let d := g.decision
  (d.place, d.relation.header.key.number, d.arity.val,
    statementPlaces d.statement, d.witness.map witnessPlaces)

open Lean Meta Elab Command

private def bodyOf (decl : Name) : MetaM Expr := do
  let some value := (← getConstInfo decl).value? (allowOpaque := true) | throwError "{decl} has no value"
  return value

/-- An argument counted from the end of an application, without reducing its head. -/
private def operand (e : Expr) (head : Name) (fromEnd : Nat) : MetaM Expr := do
  let e := e.consumeMData.headBeta
  unless e.isAppOf head && fromEnd < e.getAppNumArgs do
    throwError "expected argument {fromEnd} from the end of {head}, found {e}"
  return e.getAppArgs[e.getAppNumArgs - 1 - fromEnd]!

private def named (e : Expr) (expected : Name) : MetaM Unit := do
  unless e.consumeMData.isConstOf expected do
    throwError "expected the reference {expected}, found {e}"

/-- Observe the leaf before unfolding any generated row. Two equal-valued leaves still
have different physical names. The bound for the concrete index comes from the selector. -/
private def checkLeaf (table : Expr) (i : Nat) (expected : Name) : MetaM Unit := do
  let selector ← operand table ``BoundedTable.mk 0
  let .forallE _ domain .. ← whnf (← inferType selector) | throwError "expected a selector"
  let domain ← whnfUntil domain ``Fin
  let some domain := domain | throwError "selector does not take a bounded index"
  let index := mkNatLit i
  let lt ← mkAppM ``LT.lt #[index, domain.appArg!]
  let fin ← mkAppM ``Fin.mk #[index, ← mkDecideProof lt]
  let selected ← whnfUntil (mkApp selector fin) expected
  let some selected := selected | throwError "slot {i} did not select {expected}"
  named selected expected

/-- Follow the actual aggregate and public declarations. The expected indices and label
are chosen by the client from the original source, independently of the layout issuer. -/
def checkReferences (space : Name) (label : String) (goal clause : Nat) (fees : Bool) (arguments := 0) :
    CommandElabM Unit := liftTermElabM do
  let localName := Name.str space
  let row := localName s!"written'goal{goal}"
  let fields := localName s!"written'fields{goal}"
  let caps := localName s!"written'caps{goal}"
  let decision := localName s!"written'decision{clause}"
  let slot := localName s!"written'slot{goal}"
  let subject := localName "written'subject"
  let aggregate ← bodyOf subject
  let clauses ← operand aggregate ``WrittenSubject.mk 1
  named clauses (localName "written'clauses")
  checkLeaf (← bodyOf (localName "written'clauses")) clause decision
  checkLeaf (← operand aggregate ``WrittenSubject.mk 0) goal slot
  named (← operand (← bodyOf slot) ``GoalSlot.mk 0) fields
  let selected ← bodyOf row
  named (← operand selected ``WrittenGoal.mk 1) decision
  named (← operand selected ``WrittenGoal.mk 0) fields
  let publicName := fun (suffix_ : String) => localName (label ++ suffix_)
  named (← operand (← bodyOf fields) ``GoalFields.mk 1) caps
  named (← bodyOf (publicName "Caps")) caps
  for i in [:arguments] do
    let getter := publicName s!"Argument{i}"
    let body ← bodyOf getter
    let specification ← operand body ``getElem 2
    named (← operand specification ``GoalFields.specification 0) fields
    unless (← getNatValue? (← whnf (← operand body ``getElem 1))) == some i do
      throwError "{getter} must select argument {i}"
  let lookup := localName s!"written'goalAt{goal}"
  let some (_, lhs, rhs) := (← getConstInfo lookup).type.eq? | throwError "{lookup} must state an equality"
  named (← operand lhs ``WrittenSubject.goalAt 1) subject
  let index ← operand lhs ``WrittenSubject.goalAt 0
  unless (← getNatValue? (← whnf (← mkProjection index `val))) == some goal do
    throwError "{lookup} must select slot {goal}"
  named rhs row
  let semantic := fun (name : String) => Name.str `ZkcFormal.Written.Goal name
  let inspect (suffix_ : String) (visit : Expr → MetaM Unit) := do
    lambdaTelescope (← bodyOf (publicName suffix_)) fun _ body => visit body
  let memberLabel := if label == "root" || label == "verifier" then "relation'" ++ label else label
  let view (suffix_ kind : String) (fromEnd : Nat) (operands : List Name) := inspect suffix_ fun body => do
    let canonical ← operand body (semantic "checkedSurface") 2
    named (← operand canonical (semantic kind) fromEnd) row
    let presentation ← operand body (semantic "checkedSurface") 1
    for expected in operands do
      unless (presentation.find? (·.isConstOf expected)).isSome do
        throwError "{publicName suffix_} must expose {expected} to the author"
  let publicCap := publicName "Caps"
  let publicMember := localName (memberLabel ++ "Member")
  view "ClaimOf" "ClaimOf" 4 [publicCap]
  view "Witnessed" "Witnessed" 1 [publicMember]
  inspect "Claim" fun e => named e.getAppFn (publicName "ClaimOf")
  inspect "Goal" fun e => do
    named (← operand e (semantic "admittedAt") 1) row
    named (← operand e (semantic "admittedAt") 0) (publicName "ClaimOf")
  inspect "Result" fun e => do
    named (← operand e (semantic "resultOf") 2) row
    named (← operand e (semantic "resultOf") 0) (publicName "Goal")
  if fees then
    view "Judged" "Judged" 1 [publicCap, publicMember]
    for (suffix_, proof) in [("_claim_of_judged", "claim_of_judged"), ("_witnessed_of", "witnessed_of")] do
      inspect suffix_ fun e => do named (← operand e (semantic proof) 2) row
    let bridge := publicName "_claim_of_judged"
    let .forallE _ source target _ := (← getConstInfo bridge).type | throwError "expected a fee bridge at {bridge}"
    named source (publicName "Judged")
    named target (publicName "Claim")
    forallTelescope (← getConstInfo (publicName "_witnessed_of")).type fun _ receipt =>
      named receipt (publicName "Witnessed")

end ZkcFormalTests.WrittenBinding
