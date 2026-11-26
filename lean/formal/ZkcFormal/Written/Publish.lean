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
and the bound) and the library's own constants. No name is resolved in the scope of the caller,
so a declaration of the caller's with the same short name does not enter a statement. A row is
read by reducing the record that holds a field to its constructor and taking the field's
argument as it stands, so the constant that a field names is the constant of the statement.

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
private def fieldOf (e : Expr) (struct field : Name) : MetaM Expr := do
  let env ← getEnv
  let value ← whnf e
  let ctor := getStructureCtor env struct
  unless value.isAppOf ctor.name do
    throwError "publish: expected a value of {struct} built by its constructor, got {value}"
  let some index := (getStructureFields env struct).findIdx? (· == field)
    | throwError "publish: {struct} has no field {field}"
  return value.getAppArgs[ctor.numParams + index]!

private def constName (e : Expr) : MetaM Name := do
  let some c := e.consumeMData.constName? | throwError "publish: expected a constant, got {e}"
  return c

private def finAt (n i : Nat) : MetaM Expr := do
  let lt ← mkAppM ``LT.lt #[mkNatLit i, mkNatLit n]
  mkAppM ``Fin.mk #[mkNatLit i, ← mkDecideProof lt]

private partial def strings (e : Expr) : MetaM (List String) := do
  let s ← whnf e
  if s.isAppOf ``List.nil then return []
  unless s.isAppOfArity ``List.cons 3 do throwError "publish: expected a list of strings, got {s}"
  let some head := getStringValue? (← whnf s.appFn!.appArg!) | throwError "publish: expected a string"
  return head :: (← strings s.appArg!)

/-- One goal row: its path, its property (the constructor's name), and the constants of its
short application and of its bound. -/
structure Row where
  path : List String
  property : Name
  application : Name
  bound : Name

/-- The goal rows of the subject `S`. -/
def rows (subject : Name) : MetaM (Array Row) := do
  let s := Lean.mkConst subject
  let goals ← fieldOf s ``Zkc.Subject.WrittenSubject `goals
  let clauses ← fieldOf s ``Zkc.Subject.WrittenSubject `clauses
  let size ← natOf (← fieldOf goals ``Zkc.Subject.BoundedTable `size)
  let clauseCount ← natOf (← fieldOf clauses ``Zkc.Subject.BoundedTable `size)
  let goalAt ← fieldOf goals ``Zkc.Subject.BoundedTable `get
  let clauseAt ← fieldOf clauses ``Zkc.Subject.BoundedTable `get
  let mut out := #[]
  for i in [:size] do
    let slot := mkApp goalAt (← finAt size i)
    let path ← strings (← fieldOf slot ``Zkc.Subject.GoalSlot `path)
    let property ← constName (← whnf (← fieldOf slot ``Zkc.Subject.GoalSlot `property))
    let clause ← natOf (← fieldOf (← fieldOf slot ``Zkc.Subject.GoalSlot `clause) ``Fin `val)
    let fields ← fieldOf slot ``Zkc.Subject.GoalSlot `fields
    let bound ← constName (← fieldOf fields ``Zkc.Subject.GoalFields `bound)
    let decision := mkApp clauseAt (← finAt clauseCount clause)
    let application ← constName (← fieldOf decision ``Zkc.Subject.Decision `application)
    out := out.push { path, property, application, bound }
  return out

/-- **What each property publishes**: the names of its theorems. A property that is not listed
publishes nothing from the written subject, and the frontend refuses a goal of it at its line
(`Zkc.Security.Property.published`; a test holds the two lists equal). -/
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
    let limit ← mkAppM ``Zkc.Subject.Bound.limit #[Lean.mkConst row.bound]
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
identifier `a.b` being those of the goal's path. -/
elab "published% " s:ident path:ident which:ident : term => do
  let subject ← realizeGlobalConstNoOverloadWithInfo s
  let wanted := path.getId.components.map (·.toString (escape := false))
  let some row := (← rows subject).find? (·.path == wanted)
    | throwError "publish: no goal at the path {wanted} in {subject}"
  statement row which.getId.toString

end ZkcFormal.Written.Publish
