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

/-- Observable source coordinates of a decision, including the distinction between short syntax
and an explicitly supplied witness vector. Caps are compared as complete tables in the client. -/
def operands {V : Vocabulary} {pkg : Package V} {root : WrittenRoot pkg}
    (d : Decision root) : Nat × Nat × Nat × List Nat × Option (List Nat) :=
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

/-- The types of what a subject holds beside its short applications: a goal's bound, table,
number, fields and row, a decision (the place of a clause and its witness operands), a table of
rows or of decisions, the subject and the source's names. -/
private def rowTypes : List Name :=
  [``Zkc.Subject.Bound, ``Zkc.Subject.CapTable, ``Zkc.Subject.GoalNumber, ``Zkc.Subject.GoalFields,
    ``Zkc.Subject.GoalSlot, ``Zkc.Subject.Decision, ``Zkc.Subject.BoundedTable,
    ``Zkc.Subject.WrittenSubject, ``Zkc.Subject.RootOrigins]

/-- A short application reaches none of the subject's rows: no declaration of its module whose
type is a row's. A statement over a short application names its constant; whatever that constant
reaches is compared when a proof is judged. The declarations are told by their types, not by
their names. -/
private def checkApplicationReach (application : Name) : MetaM Unit := do
  let home := (← getEnv).getModuleIdxFor? application
  for name in (← reachedInModule home [application] {}).toList do
    -- the type's head with definitions unfolded: an alias of a row's type is that type
    let type := (← getConstInfo name).type
    let head ← Meta.forallTelescopeReducing type fun _ body => return (← Meta.whnf body).getAppFn
    if rowTypes.any (head.isConstOf ·) then
      throwError "the short application {application} reaches {privateToUserName name}"

/-- Follow the actual aggregate and the names of the installation: the subject's tables hold the
named decision and row at the given places, the decision names its short application, the short
application its relation's entry, the entry the relation's header, member and lookup by its key,
and the row its fields, whose number names the row's bound and, where it has one, its table. The
places and the key are chosen by the client from the original source, independently of the
layout issuer. -/
def checkReferences (space : Name) (goal clause relation : Nat) : CommandElabM Unit := liftTermElabM do
  let localName := Name.str space
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
  checkApplicationReach application
  named (← operand (← bodyOf application) ``ShortApplication.mk 3) fnEntry
  let entry ← bodyOf fnEntry
  named (← operand entry ``FunctionEntry.mk 2) (localName s!"header{relation}")
  named (← operand entry ``FunctionEntry.mk 1) fnMember
  named (← operand entry ``FunctionEntry.mk 0) (localName s!"found'fn{relation}")
  checkLeaf (← field aggregate ``WrittenSubject `goals) goal slot
  named (← field (← bodyOf slot) ``GoalSlot `fields) fields
  -- the row's clause is the place of its decision among the subject's
  let selects ← field (← bodyOf slot) ``GoalSlot `clause
  unless (← getNatValue? (← whnf (← mkProjection selects `val))) == some clause do
    throwError "{slot} must select the decision {clause}"
  -- a row's number names its bound and, where it has one, its table
  let number ← field (← bodyOf fields) ``GoalFields `number
  if number.isAppOfArity ``GoalNumber.total 2 then
    named (number.getArg! 0) caps
    named (number.getArg! 1) bound
  else if number.isAppOfArity ``GoalNumber.ceiling 2 then
    named (number.getArg! 0) bound
    let table := number.getArg! 1
    if table.isAppOfArity ``Option.some 2 then named table.appArg! caps
    else unless table.isAppOfArity ``Option.none 1 do
      throwError "{fields} must hold `some` of a table of caps or `none`, not{indentExpr table}"
  else throwError "{fields} must hold a number built by a constructor, not{indentExpr number}"

end ZkcFormalTests.WrittenBinding
