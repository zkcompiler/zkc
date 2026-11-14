import Zkc.Tests.Core.Declare
import Zkc.Core.VocabularyExecute

/-! Checks of the limit where a verifier reads a proof.

`fixtures/construction/units.json` has a protocol of a prover and a verifier in which the prover
sends a collection, without a size, of values of no bytes. The serialize step makes of it the
program of `fixtures/construction/units.serialized.json`: the prover writes the collection as
its length, and the verifier takes it from the proof. The executor runs the program of each role
under the limit.

- The kernel: the serialize step on the protocol gives the program of the fixture.
- An honest proof: the prover writes the length of its collection, and the verifier, on that
  proof, returns the collection, under the default limit and under an explicit larger one.
- A proof whose length asks for `2^60` values of no bytes: the verifier ends with the limit. It
  does not stop `reject`, and the run ends.
- A limit below the collection of an honest proof is reached; a limit that holds it is not.
- A proof that is not a value, or that has bytes after its value, is rejected.
- `fixtures/construction/empty-message.json` has a protocol whose receiver waits for a value
  of `index<0>`, which has no value. The program of the receiver is reported as waiting for a
  message that is never sent, not as the limit: the executor reserves, for the mark of the
  limit, a definition number that no definition of the program has.
-/

set_option autoImplicit false

open Zkc.Source Zkc.Core Zkc.Core.Vocabulary Zkc.Core.Concrete

namespace LimitedRoles

raw_package raw from file "fixtures/construction/units.json"
raw_declaration declaration from file "fixtures/construction/units.declaration.json"
raw_package serialized from file "fixtures/construction/units.serialized.json"

kernel_refl elaborates : (elaborate raw).isOk equals true

noncomputable def typed : Typed := Typed.ofRaw raw elaborates

kernel_refl serialize_eq :
  steppedProtocols typed
      (serializeProtocols declaration Identities.written typed.program.protocols) equals
    Except.ok serialized.protocols

kernel_refl serialized_elaborates : (elaborate serialized).isOk equals true

/-- The number that the executor reserves is above every identity of the program. -/
theorem reserved_written : reservedDefinition Identities.written 3 = 3 := rfl

theorem written_below (number : Nat) (below : number < 3) :
    Identities.written number < reservedDefinition Identities.written 3 :=
  identity_lt_reservedDefinition Identities.written 3 number below

/-- A wait of a program for a value of `index<0>`, at a site of its own definition 0, is not
the mark of a run that reserved the definition 1; the mark of that run is. -/
theorem own_wait_is_not_the_mark (model : Model)
    (next : Fin 0 → PIR.Process (Effects model) Unit) :
    limitOf? model 1 (.call (.receive ⟨[], 0, 0⟩ (.fin 0)) next) = none :=
  limitOf?_other model 1 ⟨[], 0, 0⟩ next (by decide)

theorem mark_is_the_limit (model : Model) :
    limitOf? model 1 (limitReached model 1 4 : PIR.Process (Effects model) Unit) = some 4 :=
  limitOf?_limitReached model 1 4

def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"limited roles: {label}")

def describe (outcome : Execute.Outcome (List Datum)) : String :=
  Execute.Outcome.describe (fun data => reprStr data) outcome

#eval show IO Unit from do
  let readPackage (path : String) : IO Raw.Package := do
    let text ← IO.FS.readFile path
    match Raw.parsePackage text with
    | .ok package => pure package
    | .error message => throw (IO.userError message)
  let package ← readPackage (package_file "fixtures/construction/units.json")
  let declaration ← match Raw.parseDeclaration
      (← IO.FS.readFile (package_file "fixtures/construction/units.declaration.json")) with
    | .ok declaration => pure declaration
    | .error message => throw (IO.userError message)
  let typed ← match elaborate package with
    | .ok typed => pure typed
    | .error refusal => throw (IO.userError s!"refused: {repr refusal}")
  -- the program that the serialize step makes: the constructed program
  let stepped ← match serializeProtocols declaration Identities.written typed.program.protocols with
    | .ok stepped => pure stepped
    | .error _ => throw (IO.userError "the serialize step refuses the protocol")
  let unitDatum := Datum.sequence []
  let units (count : Nat) : Datum := .sequence (List.replicate count unitDatum)
  let natural (value : Nat) : List Nat := (writeNatural value).map (·.val)
  -- one role alone. The entry of the serialized program has two ports: the proof, which the
  -- verifier holds, and the collection, which the prover holds. The collection is validated
  -- once; the bytes of a proof are a validated input
  let ports := (stepped.headers.head?.map (·.inputs)).getD []
  check "the serialized entry has two ports" (ports.length == 2)
  let run (role : Nat) (inputs : List (Option (Checked table package))) (limit : Nat := defaultLimit) :
      IO (Execute.Outcome (List Datum)) := do
    match runRole table package typed stepped.protocols stepped.identities role inputs
        (seededCoins table package [1]) limit with
    | .ok outcome => pure outcome
    | .error message => throw (IO.userError message)
  let verify (bytes : List Nat) (limit : Nat := defaultLimit) : IO (Execute.Outcome (List Datum)) :=
    run 1 [some (Checked.ofBytes table package (bytes.map Byte.ofNat)), none] limit
  -- an honest proof: the length of the collection
  let collection := checked? table package (.seq (.tuple []) none) (units 5)
  check "a collection of five units is a value of its type" collection.isSome
  let proved ← run 0 [none, collection]
  let proof ← match proved with
    | .returned [proof] => pure proof.toBytes
    | other => throw (IO.userError s!"limited roles: the prover: {describe other}")
  check "the proof of five units is their length" (proof == [5])
  let verified ← verify proof
  check s!"the verifier on the honest proof: {describe verified}"
    (match verified with | .returned [collection] => collection == units 5 | _ => false)
  let larger ← verify proof (limit := 2 ^ 21)
  check s!"the verifier on the honest proof under a larger limit: {describe larger}"
    (match larger with | .returned [collection] => collection == units 5 | _ => false)
  -- a limit below the collection is reached; a limit that holds it is not
  let below ← verify proof (limit := 4)
  check s!"the verifier under a limit of four: {describe below}"
    (match below with | .limit 4 => true | _ => false)
  let exact ← verify proof (limit := 5)
  check s!"the verifier under a limit of five: {describe exact}"
    (match exact with | .returned [collection] => collection == units 5 | _ => false)
  -- a proof whose length asks for 2^60 values of no bytes: the limit, not a rejection, and
  -- the run ends
  let asked ← verify (natural (2 ^ 60))
  check s!"the verifier on a proof that asks for 2^60 units: {describe asked}"
    (match asked with | .limit elements => elements == defaultLimit | _ => false)
  -- a proof that is not a value, and one with bytes after its value, are rejected
  for (what, bytes) in [("no bytes", ([] : List Nat)), ("a length cut short", [128]),
      ("a length in a longer form", [133, 0]), ("a byte after the value", [5, 0])] do
    let rejected ← verify bytes
    check s!"the verifier on {what}: {describe rejected}"
      (match rejected with | .stopped .reject => true | _ => false)
  -- a role whose input is not given, or was validated at another type, does not run
  check "the verifier without its proof does not run"
    (match runRole table package typed stepped.protocols stepped.identities 1 [none, none]
        (seededCoins table package [1]) with | .error _ => true | .ok _ => false)
  check "the verifier on an input validated at another type does not run"
    (match runRole table package typed stepped.protocols stepped.identities 1
        [checked? table package .bool (.number 1), none] (seededCoins table package [1]) with
      | .error _ => true | .ok _ => false)
  check "a collection that is not a value of its type is not an input"
    ((checked? table package (.seq (.tuple []) none) (.number 5)).isNone)
  -- the serialized program as a package that is written: the same runs, from data
  let written ← readPackage (package_file "fixtures/construction/units.serialized.json")
  match runEntryRole table written 1 [Datum.ofBytes (natural (2 ^ 60)), default] [1] with
  | .ok outcome =>
    check s!"the written verifier on a proof that asks for 2^60 units: {describe outcome}"
      (match outcome with | .limit elements => elements == defaultLimit | _ => false)
  | .error message => throw (IO.userError message)
  -- a program whose receiver waits for a value of a type with no value is waiting, not at
  -- the limit
  let waiting ← readPackage (package_file "fixtures/construction/empty-message.json")
  match runEntry table waiting [1] [default] [1] with
  | .ok result =>
    check s!"the receiver of a value of index<0>: {describe (result.outcomes.headD default)}"
      (match result.outcomes with
        | [.failed message] => message == "waits for a message that is never sent"
        | _ => false)
  | .error message => throw (IO.userError message)

end LimitedRoles
