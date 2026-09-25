/-! Let one failing check stop being the only one a file reports.

Eight modules here had an `#eval`, and three of them judged conditions: two
through a helper of their own -- `check` in BN254Reference, `require` in
ExtensionReference, byte-identical apart from the name -- and one through
`unless C do throw` written out at each site. All three threw on the first
condition that did not hold, so everything after it went unrun and unreported,
and a change that broke four of a file's checks looked like it broke one. That
is the same shape the Python suites had, and it has the same answer: record
what failed, keep going, and fail once at the end with all of them named.

The other five printed a value and judged nothing at all. Those are `#guard`s
now, which is a separate repair to the same weakness.

A shape error is different and stays fatal. `let .ok x := e | throw ...` means
the test cannot continue at all — there is no value to go on with — whereas a
condition that does not hold is a judgment this file can record and move past.

    let checks ← Checks.start
    checks.holds (encoded == expected) "canonical field wire"
    checks.holds (decoded == value) "field wire round trip"
    checks.finish "extension coordinate and reference codec controls"

The count in the summary is derived from the checks that ran, so it cannot
disagree with them the way a number written into the prose can.
-/
namespace Tests.Checks

/-- What a file has judged so far: how many checks held, and what did not. -/
structure Record where
  passed : Nat := 0
  failures : Array String := #[]
  deriving Inhabited

/-- A file's running record.

A structure rather than an abbreviation for the reference, so that `checks.holds`
resolves here: an abbreviation is reducible and the dot would look for the
method on `ST.Ref` instead. -/
structure Checks where
  ref : IO.Ref Record

/-- Begin a file's record. -/
def start : IO Checks := return { ref := ← IO.mkRef {} }

/-- Judge one condition, and carry on either way. -/
def Checks.holds (checks : Checks) (condition : Bool) (label : String) : IO Unit :=
  checks.ref.modify fun record =>
    if condition then { record with passed := record.passed + 1 }
    else { record with failures := record.failures.push label }

/-- Say what held, or name everything that did not and fail once. -/
def Checks.finish (checks : Checks) (summary : String) : IO Unit := do
  let record ← checks.ref.get
  if record.failures.isEmpty then
    IO.println s!"{summary}: {record.passed} checks passed"
  else
    let named := String.intercalate "\n  " record.failures.toList
    throw <| IO.userError
      s!"{record.failures.size} of {record.passed + record.failures.size} checks failed:\n  {named}"

end Tests.Checks
