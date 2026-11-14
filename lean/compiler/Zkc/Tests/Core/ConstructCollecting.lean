import Zkc.Tests.Core.Declare
import Zkc.Tests.Core.Runs
import Zkc.Core.ThreadTheorem

/-! The construction steps on loops that collect and whose regions are rewritten.

`fixtures/construction/collecting.json` has the protocol `rounds` of a prover and a
verifier, with two loops that collect:

- three iterations, a count of the operation. In each the prover doubles a carried value
  and sends it, the verifier draws a coin for the prover, the prover sends the product of
  the two and the verifier checks it. The verifier collects the messages and the coins;
  the region has two exchanges from the prover to the verifier and a draw between the two.
- a count that both roles hold. Each iteration applies the protocol `challenge`, in which
  the verifier draws a coin for the prover; each role collects its copy. The region is
  rewritten through the application.

Both steps accept the package. `collecting.fiat-shamir.json` and `collecting.serialized.json`
are the output of the compiled tool; the kernel evaluates the same two functions on the
typed package and finds the same raw protocols, and it accepts both outputs as programs.
In the results both loops still collect what they collected, and carry the two threaded
values before their own carried values.

The executor then runs the three programs under the model of the vocabulary's rows (Lean's
interpreter, not the kernel): in each the grouped meaning and the two role programs end
alike; the messages and the carried value are the same in all three, the two roles collect
the same coins, the serialized verifier on the prover's proof returns what the derived
program returns, and it rejects another proof. -/

set_option autoImplicit false

open Zkc.Source Zkc.Core

namespace ConstructCollecting

raw_package raw from file "fixtures/construction/collecting.json"
raw_declaration declaration from file "fixtures/construction/collecting.declaration.json"
raw_package constructed from file "fixtures/construction/collecting.fiat-shamir.json"
raw_package serialized from file "fixtures/construction/collecting.serialized.json"

kernel_refl accepted : (elaborateWritten raw).isOk equals true
kernel_refl elaborates : (elaborate raw).isOk equals true

noncomputable def typed : Typed := Typed.ofRaw raw elaborates

kernel_refl fiatShamir_eq :
  steppedProtocols typed (fiatShamir typed declaration) equals Except.ok constructed.protocols
kernel_refl serialize_eq :
  steppedProtocols typed (construct typed declaration) equals Except.ok serialized.protocols

kernel_refl constructed_elaborates : (elaborate constructed).isOk equals true
kernel_refl serialized_elaborates : (elaborate serialized).isOk equals true

mutual
  /-- The loops of a raw region, nested ones included: for each, the number of its carried
  values and the located types of what it collects. -/
  def loops : Raw.ProtocolRegion → List (Nat × List Located)
    | .ret _ => []
    | .stop _ => []
    | .step (.repeat _ _ carried _ collected body) next =>
        (carried.length, collected) :: (loops body ++ loops next)
    | .step (.choose _ _ _ _ _ arms) next => armLoops arms ++ loops next
    | .step _ next => loops next
    | .block _ body next => loops body ++ loops next

  def armLoops : Raw.ProtocolArms → List (Nat × List Located)
    | .none => []
    | .arm region rest => loops region ++ armLoops rest
end

/-- The loops of the last protocol of a package, which is the entry. -/
def entryLoops (package : Raw.Package) : List (Nat × List Located) :=
  match package.protocols.getLast? with
  | some protocol => loops protocol.body
  | none => []

-- The two loops of the entry: the first carries one value and the verifier collects two
-- values of the field, the second carries nothing and each role collects one.
kernel_refl source_loops : entryLoops raw equals
  [(1, [⟨.nominal 0, 1⟩, ⟨.nominal 0, 1⟩]), (0, [⟨.nominal 0, 0⟩, ⟨.nominal 0, 1⟩])]

-- After the Fiat–Shamir step each loop collects the same and carries the two transcripts.
kernel_refl constructed_loops : entryLoops constructed equals
  [(3, [⟨.nominal 0, 1⟩, ⟨.nominal 0, 1⟩]), (2, [⟨.nominal 0, 0⟩, ⟨.nominal 0, 1⟩])]

-- After the serialize step the first loop also carries the writer and the reader. The
-- second has no exchange after the first step, so the serialize step copies it.
kernel_refl serialized_loops : entryLoops serialized equals
  [(5, [⟨.nominal 0, 1⟩, ⟨.nominal 0, 1⟩]), (2, [⟨.nominal 0, 0⟩, ⟨.nominal 0, 1⟩])]

#print axioms fiatShamir_eq
#print axioms serialize_eq

-- The structural theorem of a threading step covers such a loop.
#print axioms Zkc.Core.repeat_threads
#print axioms Zkc.Core.repeat_region_threads
#print axioms Zkc.Core.threadRegion_meaning

end ConstructCollecting

/-! ## The executor -/

namespace ConstructCollecting.Run

open Zkc.Core.Concrete Zkc.Core.Execute Zkc.Core.Runs

def fail {α : Type} (message : String) : IO α := throw (IO.userError message)

/-- The data a run returned. -/
def returned (what : String) : Ended → IO (List Datum)
  | .returned data => pure data
  | other => fail s!"{what}: {other.describe}"

#eval show IO Unit from do
  let read (written : Bool) (path : String) : IO Typed := do
    let raw ← match Raw.parsePackage (← IO.FS.readFile path) with
      | .ok raw => pure raw
      | .error message => fail message
    match (if written then elaborateWritten raw else elaborate raw) with
    | .ok typed => pure typed
    | .error refusal => fail s!"refused: {repr refusal}"
  let interactive ← read true (package_file "fixtures/construction/collecting.json")
  let derived ← read false (package_file "fixtures/construction/collecting.fiat-shamir.json")
  let serialized ← read false (package_file "fixtures/construction/collecting.serialized.json")
  let value : Nat := 5
  let count : Nat := 2
  let inputs : List Datum := [.number value, .number value, .number count, .number count]
  let seed : List Nat := [11, 12, 13, 14, 15, 16, 17, 18]
  let messages : Datum := .sequence [.number (2 * value), .number (4 * value), .number (8 * value)]
  -- The parts of the outputs that no coin decides: the collected messages, the carried
  -- value, and that the two roles collected the same coins, one per iteration.
  let checkOutputs (what : String) (outputs : List Datum) : IO Unit := do
    match outputs with
    | [sent, .sequence coins, carried, .sequence proverCoins, .sequence verifierCoins] =>
        unless sent == messages do fail s!"{what}: the messages are {describeData [sent]}"
        unless carried == .number (8 * value) do
          fail s!"{what}: the carried value is {describeData [carried]}"
        unless coins.length == 3 do fail s!"{what}: {coins.length} coins of the first loop"
        unless proverCoins.length == count && proverCoins == verifierCoins do
          fail s!"{what}: the roles collected {describeData proverCoins} and {describeData verifierCoins}"
    | _ => fail s!"{what}: returned {describeData outputs}"
  -- The interactive program: the grouped meaning and the two role programs end alike.
  let run ← IO.ofExcept (Runs.interactive interactive inputs seed 0 1)
  unless run.agrees do fail "the interactive role programs do not end as the grouped meaning"
  let interactiveOutputs ← returned "the interactive program" run.grouped
  checkOutputs "the interactive program" interactiveOutputs
  -- The result of the Fiat–Shamir step, which draws nothing: the same on any seed.
  let run ← IO.ofExcept (Runs.interactive derived inputs seed 0 1)
  unless run.agrees do fail "the derived role programs do not end as the grouped meaning"
  let derivedOutputs ← returned "the derived program" run.grouped
  checkOutputs "the derived program" derivedOutputs
  let other ← IO.ofExcept (Runs.interactive derived inputs [] 0 1)
  unless other.grouped.same run.grouped do fail "the derived program depends on the seed"
  -- No iteration of the second loop: nothing collected there.
  let none ← IO.ofExcept (Runs.interactive derived
    [.number value, .number value, .number 0, .number 0] seed 0 1)
  match ← returned "no iteration" none.grouped with
  | [sent, _, _, .sequence [], .sequence []] =>
      unless none.agrees && sent == messages do fail "no iteration: other messages"
  | outputs => fail s!"no iteration: returned {describeData outputs}"
  -- The result of the serialize step. The prover's program runs alone and returns the
  -- proof first; the verifier's first input is the proof.
  let alone ← IO.ofExcept (Runs.joint serialized (.sequence [] :: inputs) seed [0])
  let proof ← match alone.roles with
    | [(_, .returned (proof :: _))] => pure proof
    | _ => fail "the serialized prover does not return a proof"
  let run ← IO.ofExcept (Runs.interactive serialized (proof :: inputs) seed 0 1)
  unless run.agrees do fail "the serialized role programs do not end as the grouped meaning"
  match ← returned "the serialized program" run.grouped with
  | written :: outputs =>
      unless written == proof do fail "the grouped prover writes another proof"
      -- The verifier on the proof returns what the derived program returns.
      unless outputs == derivedOutputs do
        fail s!"the serialized program returned {describeData outputs}"
  | [] => fail "the serialized program returned nothing"
  -- The proof is the six messages of the first loop.
  unless proof.items.length == 6 * 32 do fail s!"a proof of {proof.items.length} bytes"
  -- Another proof is rejected: the verifier's check of the first product fails, or a
  -- message is missing.
  let tampered : Datum := .sequence (proof.items.map fun byte =>
    if byte == Datum.number 0 then Datum.number 1 else byte)
  for wrong in [tampered, Datum.sequence (proof.items.take 40), Datum.sequence []] do
    let run ← IO.ofExcept (Runs.joint serialized (wrong :: inputs) seed [1])
    match run.roles with
    | [(_, .stopped .reject)] => pure ()
    | [(_, ended)] => fail s!"another proof: {ended.describe}"
    | _ => fail "another proof: no run"

end ConstructCollecting.Run
