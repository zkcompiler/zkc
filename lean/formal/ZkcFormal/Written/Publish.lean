module

public import Zkc.Subject.WrittenGoal
public import ZkcFormal.Written.Soundness
public import ZkcFormal.Written.Bound
public import ZkcFormal.Written.StandardInterpretation
public meta import Lean

/-!
What a goal publishes, stated by the library from the goal's row.

`publish_goals S` reads the typed subject `S` (a constant of type `WrittenSubject root`). For
each goal row it takes the path of the goal's declaration, the property that the goal names, the
short application of the decision that the row's clause index selects, and the bound of the
row's fields. For each theorem that the row's property publishes it declares, without a proof,
the theorem `<space>.<path components>.<theorem>`, where `<space>` is the name space of `S`
and each component of the path is one component of the name. A challenge is this command over
a subject.

For the property `soundness` the theorems are

* `sound : Soundness.Result model <application> draws covers <bound>.limit` and
* `met : Soundness.Witnessed model <application> draws`,

at the standard interpretation's model, samplers and coverage.

A statement is an expression built from the constants that the row names (the short application
and the bound) and the library's own constants. The subject is the one name that is resolved
in the scope of the caller; no name inside a statement is, so a declaration of the caller's with
the short name of a library constant does not enter a statement. A row is
read by reducing the record that holds a field to its constructor and taking the field's
argument as it stands, so the constant that a field names is the constant of the statement. A
statement reads its own row alone, and the bound only where the statement has one.

`published% S <path> <theorem>` is the same statement as a term, for an author or a consumer;
the path is written as one identifier whose components are the path's (`«…»` around a component
that is no identifier).
-/

public meta section

namespace ZkcFormal.Written.Publish
open Lean Meta Elab Term Command

private def natOf (e : Expr) : MetaM Nat := do
  let some n ← getNatValue? (← whnf e) | throwError "publish: expected a number, got {e}"
  return n

/-- The field `field` of a value of the structure `struct`, as the value's constructor holds it.
Only the value is reduced, to its constructor; the field's argument is returned unreduced. -/
def fieldOf (e : Expr) (struct field : Name) : MetaM Expr := do
  let env ← getEnv
  let value ← whnf e
  let ctor := getStructureCtor env struct
  unless value.isAppOf ctor.name do
    throwError "publish: expected a value of {struct} built by its constructor, got {value}"
  let some index := (getStructureFields env struct).findIdx? (· == field)
    | throwError "publish: {struct} has no field {field}"
  return value.getAppArgs[ctor.numParams + index]!

def constName (e : Expr) : MetaM Name := do
  let some c := e.consumeMData.constName? | throwError "publish: expected a constant, got {e}"
  return c

/-- The index `i` of a table of `n` rows, refused here where it is past the rows. The term is made
of fixed constants (`Fin.mk` with `Nat.le_of_ble_eq_true rfl`), so no instance of the caller's
scope enters it. -/
private def finAt (n i : Nat) : MetaM Expr := do
  unless i < n do throwError "publish: no row {i} in a table of {n}"
  let rfl := mkApp2 (Lean.mkConst ``Eq.refl [1]) (Lean.mkConst ``Bool) (Lean.mkConst ``Bool.true)
  let within := mkApp3 (Lean.mkConst ``Nat.le_of_ble_eq_true) (mkNatLit (i + 1)) (mkNatLit n) rfl
  return mkApp3 (Lean.mkConst ``Fin.mk) (mkNatLit n) (mkNatLit i) within

private partial def strings (e : Expr) : MetaM (List String) := do
  let s ← whnf e
  if s.isAppOf ``List.nil then return []
  unless s.isAppOfArity ``List.cons 3 do throwError "publish: expected a list of strings, got {s}"
  let some head := getStringValue? (← whnf s.appFn!.appArg!) | throwError "publish: expected a string"
  return head :: (← strings s.appArg!)

/-- The two tables of a subject: the selector and the size of its goal rows and of its clauses. -/
structure Tables where
  goalAt : Expr
  goals : Nat
  clauseAt : Expr
  clauses : Nat

/-- The tables of the subject `S`. -/
def tables (subject : Name) : MetaM Tables := do
  let s := Lean.mkConst subject
  let goals ← fieldOf s ``Zkc.Subject.WrittenSubject `goals
  let clauses ← fieldOf s ``Zkc.Subject.WrittenSubject `clauses
  return {
    goalAt := ← fieldOf goals ``Zkc.Subject.BoundedTable `get
    goals := ← natOf (← fieldOf goals ``Zkc.Subject.BoundedTable `size)
    clauseAt := ← fieldOf clauses ``Zkc.Subject.BoundedTable `get
    clauses := ← natOf (← fieldOf clauses ``Zkc.Subject.BoundedTable `size) }

/-- The path of the goal row at an index, and nothing else of the row. -/
def pathAt (t : Tables) (index : Nat) : MetaM (List String) := do
  strings (← fieldOf (mkApp t.goalAt (← finAt t.goals index)) ``Zkc.Subject.GoalSlot `path)

/-- One goal row: its path, its property (the constructor's name), the constant of its short
application, and its fields as the row holds them. The bound is read from the fields only for a
statement that has a bound. -/
structure Row where
  path : List String
  property : Name
  application : Name
  fields : Expr

/-- The goal row at an index. -/
def rowAt (t : Tables) (index : Nat) : MetaM Row := do
  let slot := mkApp t.goalAt (← finAt t.goals index)
  let path ← strings (← fieldOf slot ``Zkc.Subject.GoalSlot `path)
  let property ← constName (← whnf (← fieldOf slot ``Zkc.Subject.GoalSlot `property))
  let clause ← natOf (← fieldOf (← fieldOf slot ``Zkc.Subject.GoalSlot `clause) ``Fin `val)
  let fields ← fieldOf slot ``Zkc.Subject.GoalSlot `fields
  let decision := mkApp t.clauseAt (← finAt t.clauses clause)
  let application ← constName (← fieldOf decision ``Zkc.Subject.Decision `application)
  return { path, property, application, fields }

/-- **The goal rows of a subject, read once for a command.** No path is the path of two rows: a
command declares by path, so two rows of one path would give one name two rows' meanings, also
where a command declares nothing for one of them. -/
def rows (subject : Name) : MetaM (Array Row) := do
  let t ← tables subject
  let mut read : Array Row := #[]
  for index in [:t.goals] do
    let row ← rowAt t index
    if read.any (·.path == row.path) then
      throwError "publish: the path {row.path} is the path of two rows of {subject}"
    read := read.push row
  return read

/-- Whether the row is of the property `soundness`. What a command declares for the proof of a
soundness goal (the installed bound and the step from it, the fee facts) it declares for such a
row and for no other. -/
def Row.isSoundness (row : Row) : Bool := row.property == ``Zkc.Security.Property.soundness

/-- The constant of a row's bound. -/
def Row.bound (row : Row) : MetaM Name := do
  constName (← fieldOf row.fields ``Zkc.Subject.GoalFields `bound)

/-- **What each property publishes**: the names of its theorems. A property that is not listed
publishes nothing from the written subject, and the issuer of the written subject refuses a
goal of it at the goal's line (`Zkc.Security.Property.published`; a test holds the two lists
equal). -/
def theorems : List (Name × List String) :=
  [(``Zkc.Security.Property.soundness, ["sound", "met"])]

/-- The theorems of a row's property. -/
def theoremsOf (row : Row) : MetaM (List String) := do
  let some (_, names) := theorems.find? (·.1 == row.property)
    | throwError "publish: the written subject publishes nothing for the property {row.property}"
  return names

/-- The statement of the theorem `which` of a row, built from constants. -/
def statement (row : Row) (which : String) : MetaM Expr := do
  unless (← theoremsOf row).contains which do
    throwError "publish: the property {row.property} publishes no theorem `{which}`"
  let model := Lean.mkConst ``ZkcFormal.Written.StandardInterpretation.model
  let draws := Lean.mkConst ``ZkcFormal.Written.StandardInterpretation.draws
  let covers := Lean.mkConst ``ZkcFormal.Written.StandardInterpretation.covers
  let application := Lean.mkConst row.application
  match row.property, which with
  | ``Zkc.Security.Property.soundness, "sound" =>
    let limit ← mkAppM ``Zkc.Subject.Bound.limit #[Lean.mkConst (← row.bound)]
    mkAppM ``ZkcFormal.Written.Soundness.Result #[model, application, draws, covers, limit]
  | ``Zkc.Security.Property.soundness, "met" =>
    mkAppM ``ZkcFormal.Written.Soundness.Witnessed #[model, application, draws]
  | property, _ => throwError "publish: no statement of `{which}` for the property {property}"

/-- The name of a published theorem: the name space, the path's components, the theorem. -/
def theoremName (space : Name) (row : Row) (which : String) : Name :=
  Name.str (row.path.foldl (fun n c => Name.str n c) space) which

/-- Declare a theorem without a proof, as a challenge's theorem. -/
def declareUnproved (name : Name) (type : Expr) : CommandElabM Unit := liftTermElabM do
  if (← getEnv).contains name then throwError "publish: {name} is already declared"
  let value ← mkSorry type false
  addDecl (.thmDecl { name, levelParams := [], type, value })

/-- **Declare what the goals of a subject publish**, each theorem without a proof. -/
elab "publish_goals " s:ident : command => do
  let subject ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo s
  let space := subject.getPrefix
  for row in ← liftTermElabM (rows subject) do
    for which in ← liftTermElabM (theoremsOf row) do
      declareUnproved (theoremName space row which) (← liftTermElabM (statement row which))

/-- **A published statement as a term**: `published% S a.b which`, the components of the
identifier `a.b` being those of the goal's path. The path and the theorem's name are read as
they are written, also where a macro supplies them; only the row at that path is read. A path has
at least one component here: the theorems of a row whose path is empty are declared by the
commands and have no spelling as this term. -/
elab "published% " s:ident path:ident which:ident : term => do
  let subject ← realizeGlobalConstNoOverloadWithInfo s
  let wanted := path.getId.eraseMacroScopes.components.map (·.toString (escape := false))
  let t ← tables subject
  for index in [:t.goals] do
    if (← pathAt t index) == wanted then
      return ← statement (← rowAt t index) which.getId.eraseMacroScopes.toString
  throwError "publish: no goal at the path {wanted} in {subject}"

open Lean.Elab.Term.Quotation in
/-- A notation may abbreviate a published statement. Where the notation is declared the subject
gets Lean's precheck of an identifier, which accepts a dotted name whose prefix resolves; the
term itself asks for a constant of that name where the notation is used. The path and the
theorem's name are data, not names to resolve. -/
@[quot_precheck ZkcFormal.Written.Publish.«termPublished%___»]
def precheckPublished : Precheck
  | `(published% $s:ident $_:ident $_:ident) => precheck s
  | _ => throwUnsupportedSyntax

end ZkcFormal.Written.Publish
