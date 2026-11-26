import ZkcFormal.Written.Publish

/-!
The frontend and the library agree on which properties the written subject publishes.

The issuer of the written subject refuses, at the goal's line, a goal whose property is not
published from the written subject (`Zkc.Security.Property.published`). The library's command states the theorems of a
goal's row from its own table (`ZkcFormal.Written.Publish.theorems`). The compiler cannot read
the library's table, so the two are held equal here: a property is published exactly when the
table has theorems for it.
-/

open Lean Zkc.Security ZkcFormal.Written

/-- The name of a property's constructor. -/
private def constructorOf (property : Property) : Name := (reprStr property).toName

#eval show IO Unit from do
  for property in Property.all do
    let stated := (Publish.theorems.find? (·.1 == constructorOf property)).map (·.2) |>.getD []
    unless property.published == !stated.isEmpty do
      throw (IO.userError s!"{reprStr property}: the frontend's column says {property.published}, \
        the command's table has the theorems {stated}")
  unless Publish.theorems.all fun (name, _) => Property.all.any (constructorOf · == name) do
    throw (IO.userError "the command's table names a constructor that is no property")
