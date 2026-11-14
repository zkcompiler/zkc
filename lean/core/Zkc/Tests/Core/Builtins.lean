import Zkc.Tests.Core.Check
import Zkc.Tests.Core.Reflexivity
import Zkc.Core.RoundTrip
import Zkc.Tests.Core.Runs
import Zkc.Core.Facts

/-! Kernel checks for the operations the core owns.

- One evaluation of every operation, and for each of the seven with a domain (`nat.sub`,
  `nat.div`, `nat.rem`, `seq.at`, `seq.slice`, `seq.sized`, `nat.below`) one evaluation inside
  and one outside it, among them `seq.at` on a sequence of `fin 0` and a slice into a sized
  result of another size. The values are those of any carriers: the operations read none.
- `fixtures/builtins.json`: a function that guards `i < length(xs)` and then reads `xs[i]`; the
  same function without the guard; a function that applies every operation once; a protocol
  that calls the first and adds in a role's local code. The package elaborates, its typed
  package unelaborates to it, and its printed JSON reads back to it. The kernel evaluates the
  two functions' meanings for every model, inside and outside the domain of `seq.at`, and the
  check of facts, which passes the first function only.
- The executor runs the two functions and the protocol under the model of the vocabulary's
  rows (Lean's interpreter, not the kernel).
-/

set_option autoImplicit false

open Zkc.Source Zkc.Core

namespace Builtins

/-- Carriers of the nominal types; the operations read none of them. -/
abbrev C : Nat → Type := fun _ => PUnit

/-! ## One evaluation of each operation -/

theorem nat_add : Builtin.natAdd.eval (Carrier := C) (.cons (2 : Nat) (.cons (3 : Nat) .nil)) =
    some (.cons (5 : Nat) .nil) := kernel_rfl%
theorem nat_mul : Builtin.natMul.eval (Carrier := C) (.cons (2 : Nat) (.cons (3 : Nat) .nil)) =
    some (.cons (6 : Nat) .nil) := kernel_rfl%
theorem nat_pow : Builtin.natPow.eval (Carrier := C) (.cons (2 : Nat) (.cons (3 : Nat) .nil)) =
    some (.cons (8 : Nat) .nil) := kernel_rfl%
theorem nat_equal : Builtin.natEqual.eval (Carrier := C) (.cons (2 : Nat) (.cons (3 : Nat) .nil)) =
    some (.cons false .nil) := kernel_rfl%
theorem nat_less : Builtin.natLess.eval (Carrier := C) (.cons (2 : Nat) (.cons (3 : Nat) .nil)) =
    some (.cons true .nil) := kernel_rfl%
theorem bool_and : Builtin.boolAnd.eval (Carrier := C) (.cons true (.cons false .nil)) =
    some (.cons false .nil) := kernel_rfl%
theorem bool_or : Builtin.boolOr.eval (Carrier := C) (.cons true (.cons false .nil)) =
    some (.cons true .nil) := kernel_rfl%
theorem bool_not : Builtin.boolNot.eval (Carrier := C) (.cons true .nil) =
    some (.cons false .nil) := kernel_rfl%
theorem bool_equal : Builtin.boolEqual.eval (Carrier := C) (.cons true (.cons true .nil)) =
    some (.cons true .nil) := kernel_rfl%
theorem seq_length : (Builtin.seqLength .nat none).eval (Carrier := C)
    (.cons ([5, 7] : List Nat) .nil) = some (.cons (2 : Nat) .nil) := kernel_rfl%
theorem seq_length_sized : (Builtin.seqLength .nat (some 3)).eval (Carrier := C)
    (.cons ⟨[5, 7, 9], rfl⟩ .nil) = some (.cons (3 : Nat) .nil) := kernel_rfl%
theorem seq_concat : (Builtin.seqConcat .nat (some 2) none).eval (Carrier := C)
    (.cons ⟨[1, 2], rfl⟩ (.cons ([3] : List Nat) .nil)) =
      some (.cons ([1, 2, 3] : List Nat) .nil) := kernel_rfl%
theorem seq_fill : (Builtin.seqFill .nat 3).eval (Carrier := C) (.cons (7 : Nat) .nil) =
    some (.cons ⟨[7, 7, 7], rfl⟩ .nil) := kernel_rfl%
theorem seq_make : (Builtin.seqMake .nat 2).eval (Carrier := C)
    (.cons (1 : Nat) (.cons (2 : Nat) .nil)) = some (.cons ⟨[1, 2], rfl⟩ .nil) := kernel_rfl%
theorem seq_unsized : (Builtin.seqUnsized .nat 2).eval (Carrier := C) (.cons ⟨[1, 2], rfl⟩ .nil) =
    some (.cons ([1, 2] : List Nat) .nil) := kernel_rfl%
theorem fin_to_nat : (Builtin.finToNat 3).eval (Carrier := C) (.cons (⟨2, by decide⟩ : Fin 3) .nil) =
    some (.cons (2 : Nat) .nil) := kernel_rfl%
theorem fin_widen : (Builtin.finWiden 3 5 rfl).eval (Carrier := C)
    (.cons (⟨2, by decide⟩ : Fin 3) .nil) = some (.cons (⟨2, by decide⟩ : Fin 5) .nil) := kernel_rfl%
theorem tuple_make : (Builtin.tupleMake [.bool, .nat]).eval (Carrier := C)
    (.cons true (.cons (4 : Nat) .nil)) = some (.cons (true, (4 : Nat), PUnit.unit) .nil) :=
  kernel_rfl%
theorem tuple_get : (Builtin.tupleGet [.bool, .nat] .nat ⟨1, rfl⟩).eval (Carrier := C)
    (.cons (true, (4 : Nat), PUnit.unit) .nil) = some (.cons (4 : Nat) .nil) := kernel_rfl%
theorem variant_make : (Builtin.variantMake 0 [.bool, .nat] .nat ⟨1, rfl⟩).eval (Carrier := C)
    (.cons (4 : Nat) .nil) = some (.cons (.inr (.inl (4 : Nat))) .nil) := kernel_rfl%
theorem record_make : (Builtin.recordMake 0 .exactlyOnce [.bool, .nat]).eval (Carrier := C)
    (.cons true (.cons (4 : Nat) .nil)) = some (.cons (true, (4 : Nat), PUnit.unit) .nil) :=
  kernel_rfl%
theorem record_get : (Builtin.recordGet 0 .exactlyOnce [.bool, .nat] .nat ⟨1, rfl⟩).eval
    (Carrier := C) (.cons (true, (4 : Nat), PUnit.unit) .nil) = some (.cons (4 : Nat) .nil) :=
  kernel_rfl%

/-! ## The seven operations with a domain, inside and outside it -/

theorem nat_sub_inside : Builtin.natSub.eval (Carrier := C) (.cons (5 : Nat) (.cons (3 : Nat) .nil)) =
    some (.cons (2 : Nat) .nil) := kernel_rfl%
theorem nat_sub_outside : Builtin.natSub.eval (Carrier := C) (.cons (3 : Nat) (.cons (5 : Nat) .nil)) =
    none := kernel_rfl%
theorem nat_div_inside : Builtin.natDiv.eval (Carrier := C) (.cons (7 : Nat) (.cons (2 : Nat) .nil)) =
    some (.cons (3 : Nat) .nil) := kernel_rfl%
theorem nat_div_outside : Builtin.natDiv.eval (Carrier := C) (.cons (7 : Nat) (.cons (0 : Nat) .nil)) =
    none := kernel_rfl%
theorem nat_rem_inside : Builtin.natRem.eval (Carrier := C) (.cons (7 : Nat) (.cons (2 : Nat) .nil)) =
    some (.cons (1 : Nat) .nil) := kernel_rfl%
theorem nat_rem_outside : Builtin.natRem.eval (Carrier := C) (.cons (7 : Nat) (.cons (0 : Nat) .nil)) =
    none := kernel_rfl%
theorem seq_at_inside : (Builtin.seqAt .nat none).eval (Carrier := C)
    (.cons ([5, 7] : List Nat) (.cons (1 : Nat) .nil)) = some (.cons (7 : Nat) .nil) := kernel_rfl%
/-- A sequence of an empty element type has no element to give. -/
theorem seq_at_outside : (Builtin.seqAt (.fin 0) none).eval (Carrier := C)
    (.cons ([] : List (Fin 0)) (.cons (0 : Nat) .nil)) = none := kernel_rfl%
theorem seq_slice_inside : (Builtin.seqSlice .nat none (some 2)).eval (Carrier := C)
    (.cons ([1, 2, 3, 4] : List Nat) (.cons (1 : Nat) (.cons (3 : Nat) .nil))) =
      some (.cons ⟨[2, 3], rfl⟩ .nil) := kernel_rfl%
/-- The slice has two elements, and the result is sized three. -/
theorem seq_slice_outside : (Builtin.seqSlice .nat none (some 3)).eval (Carrier := C)
    (.cons ([1, 2, 3, 4] : List Nat) (.cons (1 : Nat) (.cons (3 : Nat) .nil))) = none := kernel_rfl%
theorem seq_sized_inside : (Builtin.seqSized .nat 2).eval (Carrier := C)
    (.cons ([1, 2] : List Nat) .nil) = some (.cons ⟨[1, 2], rfl⟩ .nil) := kernel_rfl%
theorem seq_sized_outside : (Builtin.seqSized .nat 2).eval (Carrier := C)
    (.cons ([1, 2, 3] : List Nat) .nil) = none := kernel_rfl%
theorem nat_below_inside : (Builtin.natBelow 3).eval (Carrier := C) (.cons (2 : Nat) .nil) =
    some (.cons (⟨2, by decide⟩ : Fin 3) .nil) := kernel_rfl%
theorem nat_below_outside : (Builtin.natBelow 0).eval (Carrier := C) (.cons (0 : Nat) .nil) =
    none := kernel_rfl%

/-! ## The package -/

raw_package raw from file "fixtures/builtins.json"

kernel_refl accepted : (elaborateWritten raw).isOk equals true
kernel_refl elaborates : (elaborate raw).isOk equals true

noncomputable def typed : Typed := Typed.ofRaw raw elaborates

kernel_refl elaborated_unelaborate : unelaborate typed equals raw

reprinted_package reprinted from file "fixtures/builtins.json"

kernel_refl reprinted_eq : reprinted equals raw

/-- The process of a function of a typed package, by its number, on a sequence of naturals
and an index, with its one natural result; none when it has another signature. -/
def indexRun (model : Model) (typed : Typed) (number : Nat) (xs : List Nat) (index : Nat) :
    Option (PIR.Process (Effects model) Nat) :=
  let position := typed.functions.length - 1 - number
  match found : typed.functions[position]? with
  | some header =>
      if inputs : header.inputs = [.seq .nat none, .nat] then
        if outputs : header.outputs = [.nat] then
          some (((typed.program.functions.table model).get (⟨position, found⟩ : Var _ header)
              (cast (by rw [inputs])
                (Values.cons xs (Values.cons index Values.nil) :
                  Values model.Value [.seq .nat none, .nat]))).bind
            fun values => .done ((cast (by rw [outputs]) values : Values model.Value [.nat]).get .here))
        else none
      else none
  | none => none

/-- Inside the domain: the guarded function returns the element. -/
theorem guarded_inside (model : Model) : indexRun model typed 0 [5, 7] 1 = some (.done 7) :=
  kernel_rfl%

/-- Outside the domain: the guard stops `reject` before the element is read. -/
theorem guarded_outside (model : Model) : indexRun model typed 0 [5, 7] 2 = some (.halt .reject) :=
  kernel_rfl%

theorem unguarded_inside (model : Model) : indexRun model typed 1 [5, 7] 1 = some (.done 7) :=
  kernel_rfl%

/-- Without the guard the package is well formed all the same, and outside the domain the
read stops `undefined`. The check of facts does not pass the function. -/
theorem unguarded_outside (model : Model) :
    indexRun model typed 1 [5, 7] 2 = some (.halt .undefined) := kernel_rfl%

-- The check of facts passes the guarded function. The unguarded one reads without a known
-- position, and the function that applies every operation once subtracts without a known
-- order.
kernel_refl unjustified :
    typed.program.functions.unjustified equals [(1, ⟨[0], .position⟩), (2, ⟨[5], .ordered⟩)]

#print axioms nat_add
#print axioms seq_at_outside
#print axioms elaborated_unelaborate
#print axioms reprinted_eq
#print axioms guarded_outside
#print axioms unguarded_outside

end Builtins

/-! ## The executor -/

namespace Builtins.Run

open Zkc.Core.Concrete Zkc.Core.Execute Zkc.Core.Runs

/-- The outcome of a function of a package under the model of the vocabulary's rows, on one
datum per input. -/
def functionOutcome (typed : Typed) (number : Nat) (inputs : List Datum) : String :=
  if let row :: _ := missing typed then s!"failed: {row}" else
  let model := modelOf typed
  let carrier := modelOf_carrier typed
  let position := typed.functions.length - 1 - number
  match found : typed.functions[position]? with
  | none => "no such function"
  | some header =>
      match roleValues model carrier header.inputs inputs with
      | none => "an input is not a value of its type"
      | some arguments =>
          let process := (typed.program.functions.table model).get
            (⟨position, found⟩ : Var typed.functions header) arguments
          match runAlone model (Vocabulary.seededCoins Vocabulary.table (unelaborate typed) []) process with
          | .returned values => s!"returned {describeData (roleData model carrier _ values)}"
          | .stopped reason => s!"stopped {repr reason}"
          | .limit elements => s!"reached the limit of {elements} elements"
          | .failed message => s!"failed: {message}"

#eval show IO Unit from do
  let raw ← match Raw.parsePackage (← IO.FS.readFile (package_file "fixtures/builtins.json")) with
    | .ok raw => pure raw
    | .error message => throw (IO.userError message)
  let typed ← match elaborateWritten raw with
    | .ok typed => pure typed
    | .error refusal => throw (IO.userError s!"refused: {repr refusal}")
  let xs := Datum.sequence [.number 5, .number 7]
  let expect (number index : Nat) (expected : String) : IO Unit := do
    let found := functionOutcome typed number [xs, .number index]
    unless found == expected do
      throw (IO.userError s!"function {number} at {index}: {found}, not {expected}")
  expect 0 1 "returned 7"
  expect 0 2 "stopped PIR.Stop.reject"
  expect 1 1 "returned 7"
  expect 1 2 "stopped PIR.Stop.undefined"
  -- The protocol: role 0 reads with the guarded function and sends, role 1 adds.
  let inside ← IO.ofExcept (interactive typed [xs, .number 1] [] 0 1)
  unless inside.agrees && inside.grouped.describe == "returned 14" do
    throw (IO.userError s!"protocol inside: {inside.grouped.describe}")
  let outside ← IO.ofExcept (interactive typed [xs, .number 2] [] 0 1)
  unless outside.grouped.describe == "stopped PIR.Stop.reject" do
    throw (IO.userError s!"protocol outside: {outside.grouped.describe}")

end Builtins.Run
