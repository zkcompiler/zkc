import Zkc.Core.Execute
import Zkc.Core.Unelaborate
import Zkc.Core.VocabularyExecute

/-! Runs of the programs of a typed package under the model of the vocabulary's rows, for the
checks of the executor.

The entry's meaning for the side of all its roles (the grouped meaning) is run on inputs, and
so are the programs of two or more roles against each other. The same seed gives both runs the same
coins; the outcomes are compared. A package that applies a row the model does not implement
does not run. These run in Lean's interpreter, not in the kernel.
-/

set_option autoImplicit false

namespace Zkc.Core.Runs

open Zkc.Source Zkc.Core.Concrete Zkc.Core.Execute

/-- The model of the rows of a typed package: the vocabulary's. -/
def modelOf (typed : Typed) : Model := Vocabulary.model Vocabulary.table (unelaborate typed)

theorem modelOf_carrier (typed : Typed) : (modelOf typed).Carrier = Carrier := rfl

/-- The rows of a typed package that the model does not implement, each named. -/
def missing (typed : Typed) : List String := Vocabulary.missing Vocabulary.table (unelaborate typed)

/-- How a run ends, as data. -/
abbrev Ended := Outcome (List Datum)

def describeData (data : List Datum) : String :=
  let rec show_ : Datum → String
    | .number value => if value < 1000000 then toString value else s!"0x{hex (bigEndian 32 value)}"
    | .sequence items => "[" ++ ", ".intercalate (items.map show_) ++ "]"
  ", ".intercalate (data.map show_)

def Ended.describe (ended : Ended) : String := Outcome.describe describeData ended

/-- Two runs end alike: with the same values, or with the same stop. -/
def Ended.same : Ended → Ended → Bool
  | .returned first, .returned second => first == second
  | .stopped first, .stopped second => first == second
  | _, _ => false

/-- The grouped run of the entry and the runs of the programs of some of its roles against
each other. -/
structure Joint where
  /-- The grouped run's outputs, for all roles. -/
  grouped : Ended
  /-- For each of the roles, in the order given: the grouped run's outputs that the role
  holds, and the outcome of the role's own program. -/
  roles : List (Ended × Ended)

/-- The grouped meaning of the entry and the programs of the given roles against each
other, on one datum per input port and one seed. -/
def joint (typed : Typed) (inputs : List Datum) (seed : List Nat) (roles : List Nat) :
    Except String Joint := do
  if let row :: _ := missing typed then throw row
  let model := modelOf typed
  let carrier := modelOf_carrier typed
  let functionTable := typed.program.functionTable model
  let some ⟨header, meaning⟩ := groupedEntry model functionTable Identities.written typed.program.protocols
    | throw "the program has no protocol"
  let some arguments := sideValues model carrier header.inputs inputs
    | throw "an input is not a value of its port's type"
  let grouped : Ended :=
    match runAlone model (Vocabulary.seededCoins Vocabulary.table (unelaborate typed) seed) (meaning [] (fun _ => true) arguments) with
    | .returned values => .returned (sideData model carrier header.outputs values)
    | .stopped reason => .stopped reason
    | .limit elements => .limit elements
    | .failed message => .failed message
  let own (role : Nat) : Ended := match grouped with
    | .returned values => .returned (ownData role header.outputs values)
    | other => other
  let mut processes : Array (PIR.Process (Effects model) (List Datum)) := #[]
  for role in roles do
    let ⟨roleHeader, program⟩ ← roleEntry model functionTable Identities.written role typed.program.protocols
    let some arguments := roleValues model carrier _ (ownData role roleHeader.inputs inputs)
      | throw "an input is not a value of its port's type"
    processes := processes.push ((program [] arguments).bind fun values =>
      .done (roleData model carrier _ values))
  let outcomes := runAll model (Vocabulary.seededCoins Vocabulary.table (unelaborate typed) seed) processes
  return { grouped, roles := (roles.map own).zip outcomes.toList }

/-- The completeness lemma as a test: when the grouped run returns, each role's own
program, run against the others, returns the values the role holds. -/
def Joint.agrees (run : Joint) : Bool :=
  match run.grouped with
  | .returned _ => run.roles.all fun (held, own) => held.same own
  | _ => true

structure Interactive where
  /-- The grouped run's outputs, for all roles. -/
  grouped : Ended
  /-- The grouped run's outputs that each of the two roles holds. -/
  groupedFirst : Ended
  groupedSecond : Ended
  /-- The outcomes of the two roles' own programs, run against each other. -/
  first : Ended
  second : Ended

/-- The grouped meaning of the entry and the programs of two of its roles against each
other, on one datum per input port and one seed. -/
def interactive (typed : Typed) (inputs : List Datum) (seed : List Nat) (first second : Nat) :
    Except String Interactive := do
  let run ← joint typed inputs seed [first, second]
  let (groupedFirst, ownFirst) := run.roles.getD 0 default
  let (groupedSecond, ownSecond) := run.roles.getD 1 default
  return { grouped := run.grouped, groupedFirst, groupedSecond, first := ownFirst, second := ownSecond }

/-- The completeness lemma as a test: when the grouped run returns, each role's own
program, run against the other, returns the values the role holds. -/
def Interactive.agrees (run : Interactive) : Bool :=
  match run.grouped with
  | .returned _ => run.groupedFirst.same run.first && run.groupedSecond.same run.second
  | _ => true

end Zkc.Core.Runs
