import Zkc.Core.Package

/-! The spellings of the core types and literals in JSON, read and printed back.

These checks run in Lean's interpreter when the file is elaborated; a failure is an error of
the build. They are not kernel checks: the kernel checks of the types are in
`Zkc.Tests.Core.Types`.

- JSON: a row of the table with the name of an operation the core owns is refused.
- JSON: every type of a list that covers the type grammar prints to a JSON value that the
  reader reads back to the raw form of the type, in which a record or a variant is the number
  of its declaration (`["record", k]`, `["variant", k]`). Each type has one spelling, named as
  the type is: `"nat"`, `["seq", T]` and `["seq", T, n]`, and the empty tuple `["tuple", []]`.
- JSON: the spellings `"index"`, `"unit"` and `["array", T]` are refused as malformed types.
- JSON: the literal of a natural number is `["literal", ["nat", n]]`; the tag `"index"` is
  refused.
-/

set_option autoImplicit false

open Zkc.Core

-- A row of the table may not have the name of an operation the core owns.
#eval show IO Unit from do
  let text := "[\"zkc.core/0\", [[\"original\", [], [], [], [], [[\"nat.add\", [], \"pure\", " ++
    "[\"nat\", \"nat\"], [\"nat\"]]], []]], [], [], [], []]"
  match Raw.parsePackage text with
  | .ok _ => throw (IO.userError "a row named nat.add is read")
  | .error message =>
      unless message == "operation row nat.add: nat.add is an operation of the core, not a row of the table" do
        throw (IO.userError s!"unexpected refusal: {message}")

/-- Types that cover the grammar, with the JSON text of each. -/
def jsonSpellings : List (Ty × String) :=
  [(.bool, "\"bool\""), (.nat, "\"nat\""), (.tuple [], "[\"tuple\",[]]"), (.fin 0, "[\"fin\",0]"),
   (.fin 7, "[\"fin\",7]"), (.nominal 2, "[\"nominal\",2]"),
   (.seq .bool none, "[\"seq\",\"bool\"]"), (.seq (.fin 0) (some 0), "[\"seq\",[\"fin\",0],0]"),
   (.seq (.seq .nat none) (some 3), "[\"seq\",[\"seq\",\"nat\"],3]"),
   (.tuple [.bool, .nat], "[\"tuple\",[\"bool\",\"nat\"]]"),
   (.record 0 .free [], "[\"record\",0]"),
   (.record 1 .exactlyOnce [.bool, .nominal 0], "[\"record\",1]"),
   (.variant 0 [], "[\"variant\",0]"),
   (.variant 2 [.tuple [], .fin 2], "[\"variant\",2]"),
   (.seq (.variant 2 [.bool]) (some 1), "[\"seq\",[\"variant\",2],1]")]

#eval show IO Unit from do
  for (type, text) in jsonSpellings do
    let printed := (Raw.printType type).render
    unless printed == text do throw (IO.userError s!"{repr type} is printed as {printed}, not {text}")
    match Raw.readType (Raw.printType type) with
    | .ok back =>
        unless back == type.strip do throw (IO.userError s!"{printed} is read back as {repr back}")
    | .error message => throw (IO.userError s!"{printed}: {message}")

-- `"index"`, `"unit"` and `["array", T]` are not types: the count type, the empty tuple and a
-- sequence without a size are spelled as they are named.
#eval show IO Unit from do
  for text in ["\"index\"", "\"unit\"", "[\"array\",\"bool\"]", "[\"array\",\"nat\"]"] do
    let json ← match Zkc.Json.parse text with
      | .ok json => pure json
      | .error message => throw (IO.userError s!"{text}: {message}")
    match Raw.readType json with
    | .ok type => throw (IO.userError s!"{text} is read as {repr type}")
    | .error message =>
        unless message == s!"malformed type {json.render}" do
          throw (IO.userError s!"{text}: unexpected refusal: {message}")

-- The literal of a natural number is tagged as its type is named.
#eval show IO Unit from do
  let parse (text : String) : IO Zkc.Json := match Zkc.Json.parse text with
    | .ok json => pure json
    | .error message => throw (IO.userError s!"{text}: {message}")
  match Raw.readLocalStep #[] (← parse "[\"literal\",[\"nat\",2]]") with
  | .ok (.literal (.nat 2)) => pure ()
  | .ok _ => throw (IO.userError "[\"literal\",[\"nat\",2]] is read as another instruction")
  | .error message => throw (IO.userError s!"[\"literal\",[\"nat\",2]]: {message}")
  let old ← parse "[\"literal\",[\"index\",2]]"
  match Raw.readLocalStep #[] old with
  | .ok _ => throw (IO.userError s!"{old.render} is read")
  | .error message =>
      unless message == s!"unsupported local instruction {old.render}" do
        throw (IO.userError s!"{old.render}: unexpected refusal: {message}")
