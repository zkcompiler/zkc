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
  (d.place, d.application.relation.header.key.number, d.application.arity.val,
    statementPlaces d.application.statement, d.witness.map witnessPlaces)

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

/-- What a record's body holds for the field `field` of the structure `struct`, by the field's
name, without reducing. -/
private def field (e : Expr) (struct field : Name) : MetaM Expr := do
  let env ← getEnv
  let e := e.consumeMData.headBeta
  let ctor := getStructureCtor env struct
  let some index := (getStructureFields env struct).findIdx? (· == field)
    | throwError "{struct} has no field {field}"
  unless e.isAppOf ctor.name && ctor.numParams + index < e.getAppNumArgs do
    throwError "expected a value of {struct} built by its constructor, found {e}"
  return e.getAppArgs[ctor.numParams + index]!

private def named (e : Expr) (expected : Name) : MetaM Unit := do
  unless e.consumeMData.isConstOf expected do
    throwError "expected the reference {expected}, found {e}"

private def namedApplication (e : Expr) (head : Name) (arguments : List Name) : MetaM Unit := do
  unless e.isAppOfArity head arguments.length do throwError "expected the complete application of {head}"
  for (arg, expected) in e.getAppArgs.toList.zip arguments do named arg expected

private def site (e : Expr) (head : Name) (arity : Nat) : MetaM Expr := do
  let some app := e.find? (·.isAppOfArity head arity) | throwError "missing {head} in the presentation"
  return app

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

/-- The constants of a constant's own module that it reaches through types and values. The
module decides, not the name: a private declaration of the module has a name outside the
subject's name space. -/
private partial def reachedInModule (home : Option ModuleIdx) :
    List Name → NameSet → MetaM NameSet
  | [], seen => return seen
  | name :: rest, seen => do
    if seen.contains name then reachedInModule home rest seen else
    let info ← getConstInfo name
    let env ← getEnv
    let used := info.type.getUsedConstants ++
      ((info.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
    reachedInModule home (used.toList.filter (env.getModuleIdxFor? · == home) ++ rest)
      (seen.insert name)

/-- What a statement over a short application must not read through it: a decision (the place
of a clause and its witness operands), a goal's row, fields and bound, the table of caps, the
aggregate and the source's names. -/
private def rowWords : List String :=
  ["written'decision", "written'goal", "written'fields", "written'bound", "written'slot",
    "written'caps", "written'clauses", "written'subject", "written'origins"]

/-- A short application reaches none of the subject's rows. A statement over a short application
names its constant; whatever that constant reaches is compared when a proof is judged. -/
private def checkApplicationReach (space application : Name) : MetaM Unit := do
  let home := (← getEnv).getModuleIdxFor? application
  for name in (← reachedInModule home [application] {}).toList do
    let word := ((privateToUserName name).replacePrefix space .anonymous).toString
    if rowWords.any (word.startsWith ·) then
      throwError "the short application {application} reaches {privateToUserName name}"

/-- Follow the actual aggregate and the names of the installation. The expected indices and
label are chosen by the client from the original source, independently of the layout issuer. -/
def checkReferences (space : Name) (label : String) (goal clause relation : Nat) (arguments := 0) :
    CommandElabM Unit := liftTermElabM do
  let localName := Name.str space
  let row := localName s!"written'goal{goal}"
  let fields := localName s!"written'fields{goal}"
  let caps := localName s!"written'caps{goal}"
  let bound := localName s!"written'bound{goal}"
  let decision := localName s!"written'decision{clause}"
  let fnEntry := localName s!"written'fn{relation}"
  let fnMember := localName s!"member'fn{relation}"
  let slot := localName s!"written'slot{goal}"
  let subject := localName "written'subject"
  let aggregate ← bodyOf subject
  let clauses ← field aggregate ``WrittenSubject `clauses
  named clauses (localName "written'clauses")
  checkLeaf (← bodyOf (localName "written'clauses")) clause decision
  let application := localName s!"written'application{clause}"
  named (← operand (← bodyOf decision) ``Decision.mk 2) application
  checkApplicationReach space application
  named (← operand (← bodyOf application) ``ShortApplication.mk 3) fnEntry
  let entry ← bodyOf fnEntry
  named (← operand entry ``FunctionEntry.mk 2) (localName s!"header{relation}")
  named (← operand entry ``FunctionEntry.mk 1) fnMember
  named (← operand entry ``FunctionEntry.mk 0) (localName s!"found'fn{relation}")
  checkLeaf (← field aggregate ``WrittenSubject `goals) goal slot
  named (← field (← bodyOf slot) ``GoalSlot `fields) fields
  let selected ← bodyOf row
  named (← operand selected ``WrittenGoal.mk 1) decision
  named (← operand selected ``WrittenGoal.mk 0) fields
  let publicName := fun (suffix_ : String) => localName (label ++ suffix_)
  -- a row's table is `some` of its named table, with the goal's public name for it, or `none`
  let table ← field (← bodyOf fields) ``GoalFields `caps
  if table.isAppOfArity ``Option.some 2 then
    named table.appArg! caps
    named (← bodyOf (publicName "Caps")) caps
  else unless table.isAppOfArity ``Option.none 1 do
    throwError "{fields} must hold `some` of a table of caps or `none`, not{indentExpr table}"
  named (← field (← bodyOf fields) ``GoalFields `bound) bound
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
  let memberLabel := if label == "root" || label == "verifier" then "relation'" ++ label else label
  named (← bodyOf (localName (memberLabel ++ "Member"))) fnMember

end ZkcFormalTests.WrittenBinding
