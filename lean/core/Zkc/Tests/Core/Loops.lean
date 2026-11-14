import Zkc.Tests.Core.Check
import Zkc.Tests.Core.Reflexivity
import Zkc.Tests.Core.Builtins
import Zkc.Core.RoundTrip
import Zkc.Core.Laws
import Zkc.Tests.Core.Runs

/-! Kernel checks for `loop`: a count of the operation or a count that is a value, and
collected values.

- `fixtures/loops.json` has five functions and a protocol. `squares` runs four iterations,
  a count of the operation, and collects `i * i`. `nothing` runs no iteration: it returns
  its carried input and an empty sequence. `shifted` runs a count that is a value, without
  a maximum, and collects `i + base` into an unsized sequence. `sums` carries a sum and
  collects it after each iteration, within the maximum 8. `total` is the loop that carries
  and collects nothing, as it was written before a loop could collect. In `sends` a role
  collects in its local code and sends the sequence. The package elaborates, its typed
  package unelaborates to it, and its printed JSON reads back to it.
- For an arbitrary model the kernel evaluates each function: the collected values are those
  of the iterations in order, a sized sequence for a count of the operation and an unsized
  one for a count that is a value; a count above the maximum stops `undefined`.
- Refusals: a region that yields no collected value, one that yields a collected value of
  another type, a result used at another size than the count; in JSON, an empty list of
  collected types.
- The executor runs the functions and the protocol under the model of the vocabulary's rows
  (Lean's interpreter, not the kernel).
-/

set_option autoImplicit false

open Zkc.Source Zkc.Core

namespace Loops

/-! ## The JSON package -/

raw_package raw from file "fixtures/loops.json"

kernel_refl tables : tablesViolation raw.types raw.records raw.variants raw.operations equals none
kernel_refl accepted : (elaborateWritten raw).isOk equals true
kernel_refl elaborates : (elaborate raw).isOk equals true

noncomputable def elaborated : Typed := Typed.ofRaw raw elaborates

typed_literal typed := elaborated

kernel_refl elaborate_eq : elaborate raw equals Except.ok typed
kernel_refl unelaborate_eq : unelaborate typed equals raw

reprinted_package reprinted from file "fixtures/loops.json"

kernel_refl reprinted_eq : reprinted equals raw

-- The raw body of the first function: a count of the instruction and one collected type.
kernel_refl squares_body : (raw.functions.head?.bind (·.body)) equals
  some (.step (.loop (.static 4) [] [] [.nat]
      (.step (.builtin .natMul [0, 0]) (.ret [1])))
    (.ret [0]))

-- The raw body of the last function: the loop that collects nothing has the spelling it
-- had before a loop could collect.
kernel_refl total_body : (raw.functions.getLast?.bind (·.body)) equals
  some (.step (.loop (.runtime (some 8) 0) [1] [] []
      (.step (.builtin .natAdd [1, 0]) (.ret [2])))
    (.ret [2]))

abbrev squares : Var typed.functions ⟨[], [.seq .nat (some 4)], false⟩ := ⟨4, rfl⟩
abbrev nothing : Var typed.functions ⟨[.nat], [.nat, .seq .nat (some 0)], false⟩ := ⟨3, rfl⟩
abbrev shifted : Var typed.functions ⟨[.nat, .nat], [.seq .nat none], false⟩ := ⟨2, rfl⟩
abbrev sums : Var typed.functions ⟨[.nat, .nat], [.nat, .seq .nat none], false⟩ := ⟨1, rfl⟩
abbrev total : Var typed.functions ⟨[.nat, .nat], [.nat], false⟩ := ⟨0, rfl⟩

/-- Four iterations collect the squares of their numbers into a sequence of four. -/
theorem squares_collects (model : Model) :
    (typed.program.functions.table model).get squares .nil =
      .done (.cons ⟨[0, 1, 4, 9], rfl⟩ .nil) := kernel_rfl%

/-- No iteration: the carried value as it was given, and the empty sequence. -/
theorem nothing_collects (model : Model) (carried : Nat) :
    (typed.program.functions.table model).get nothing (.cons carried .nil) =
      .done (.cons carried (.cons ⟨[], rfl⟩ .nil)) := kernel_rfl%

/-- A count that is a value: three iterations collect into an unsized sequence. -/
theorem shifted_collects (model : Model) :
    (typed.program.functions.table model).get shifted (.cons (3 : Nat) (.cons (10 : Nat) .nil)) =
      .done (.cons ([10, 11, 12] : List Nat) .nil) := kernel_rfl%

/-- A count of zero that is a value collects the empty sequence. -/
theorem shifted_empty (model : Model) (base : Nat) :
    (typed.program.functions.table model).get shifted (.cons (0 : Nat) (.cons base .nil)) =
      .done (.cons ([] : List Nat) .nil) := kernel_rfl%

/-- A loop that carries and collects: the sum after the last iteration, and the sums after
each. -/
theorem sums_collects (model : Model) :
    (typed.program.functions.table model).get sums (.cons (4 : Nat) (.cons (10 : Nat) .nil)) =
      .done (.cons (16 : Nat) (.cons ([10, 11, 13, 16] : List Nat) .nil)) := kernel_rfl%

/-- A count above the maximum is outside the domain of the loop: it stops `undefined`. -/
theorem sums_beyond (model : Model) (start : Nat) :
    (typed.program.functions.table model).get sums (.cons (9 : Nat) (.cons start .nil)) =
      .halt .undefined := kernel_rfl%

/-- The loop that collects nothing returns its carried values. -/
theorem total_carries (model : Model) :
    (typed.program.functions.table model).get total (.cons (4 : Nat) (.cons (10 : Nat) .nil)) =
      .done (.cons (16 : Nat) .nil) := kernel_rfl%

theorem total_beyond (model : Model) (start : Nat) :
    (typed.program.functions.table model).get total (.cons (9 : Nat) (.cons start .nil)) =
      .halt .undefined := kernel_rfl%

/-! ## Refusals -/

/-- The refusal of a package with one function. -/
abbrev refusalOf (inputs outputs : List Ty) (body : Raw.LocalRegion) : Option Refusal :=
  match elaborate ⟨[], [], [], [], [⟨false, inputs, outputs, some body⟩], [], none⟩ with
  | .error refusal => some refusal
  | .ok _ => none

-- The region yields no value for the collected type.
kernel_refl missing_collected :
    refusalOf [] [.seq .nat (some 2)]
      (.step (.loop (.static 2) [] [] [.nat] (.ret [])) (.ret [0])) equals
      some ⟨.operand, some (.function 0), [0, 0, 0]⟩

-- The region yields two values for one collected type.
kernel_refl surplus_collected :
    refusalOf [] [.seq .nat (some 2)]
      (.step (.loop (.static 2) [] [] [.nat] (.ret [0, 0])) (.ret [0])) equals
      some ⟨.operand, some (.function 0), [0, 0, 0]⟩

-- The region yields the iteration number, a `nat`, for a collected `bool`.
kernel_refl other_collected :
    refusalOf [] [.seq .bool (some 2)]
      (.step (.loop (.static 2) [] [] [.bool] (.ret [0])) (.ret [0])) equals
      some ⟨.operand, some (.function 0), [0, 0, 0]⟩

-- The collected sequence of a count of the instruction has that size, and no other.
kernel_refl other_size :
    refusalOf [] [.seq .nat (some 3)]
      (.step (.loop (.static 2) [] [] [.nat] (.ret [0])) (.ret [0])) equals
      some ⟨.operand, some (.function 0), [1]⟩

-- The collected sequence of a count that is a value is unsized.
kernel_refl sized_runtime :
    refusalOf [.nat] [.seq .nat (some 2)]
      (.step (.loop (.runtime none 0) [] [] [.nat] (.ret [0])) (.ret [1])) equals
      some ⟨.operand, some (.function 0), [1]⟩

-- The same loops with the results they have.
kernel_refl static_accepted :
    refusalOf [] [.seq .nat (some 2)]
      (.step (.loop (.static 2) [] [] [.nat] (.ret [0])) (.ret [0])) equals none
kernel_refl runtime_accepted :
    refusalOf [.nat] [.seq .nat none]
      (.step (.loop (.runtime none 0) [] [] [.nat] (.ret [0])) (.ret [1])) equals none

-- A collected type that names an undeclared record.
kernel_refl undeclared_collected :
    refusalOf [] []
      (.step (.loop (.static 2) [] [] [.record 3 .free []] (.ret [0])) (.ret [])) equals
      some ⟨.declaration, some (.function 0), [0]⟩

#print axioms elaborate_eq
#print axioms reprinted_eq
#print axioms squares_collects
#print axioms nothing_collects
#print axioms shifted_collects
#print axioms sums_collects
#print axioms sums_beyond
#print axioms total_carries

end Loops

/-! ## The JSON text -/

-- A loop that collects nothing has one spelling: the one without a list of collected types.
#eval show IO Unit from do
  let parse (text : String) : IO Zkc.Json := match Zkc.Json.parse text with
    | .ok json => pure json
    | .error message => throw (IO.userError message)
  let region := "[[], [1]]"
  match Raw.readLocalStep #[] (← parse s!"[\"loop\", 8, 0, [1], [], {region}]") with
  | .ok (.loop (.runtime (some 8) 0) [1] [] [] _) => pure ()
  | .ok _ => throw (IO.userError "the loop is read as another instruction")
  | .error message => throw (IO.userError message)
  match Raw.readLocalStep #[] (← parse s!"[\"loop\", 8, 0, [1], [], {region}, []]") with
  | .ok _ => throw (IO.userError "a loop with an empty list of collected types is read")
  | .error message =>
      unless message == "loop: a loop that collects nothing does not list collected types" do
        throw (IO.userError s!"unexpected refusal: {message}")

/-! ## The executor -/

namespace Loops.Run

open Zkc.Core.Concrete Zkc.Core.Execute Builtins.Run

#eval show IO Unit from do
  let raw ← match Raw.parsePackage (← IO.FS.readFile (package_file "fixtures/loops.json")) with
    | .ok raw => pure raw
    | .error message => throw (IO.userError message)
  let typed ← match elaborateWritten raw with
    | .ok typed => pure typed
    | .error refusal => throw (IO.userError s!"refused: {repr refusal}")
  let expect (number : Nat) (inputs : List Datum) (expected : String) : IO Unit := do
    let found := functionOutcome typed number inputs
    unless found == expected do
      throw (IO.userError s!"function {number}: {found}, not {expected}")
  let expectEnd (number : Nat) (inputs : List Datum) (expected : String) : IO Unit := do
    let found := functionOutcome typed number inputs
    unless found.endsWith expected do
      throw (IO.userError s!"function {number}: the outcome does not end with {expected}")
  expect 0 [] "returned [0, 1, 4, 9]"
  expect 1 [.number 7] "returned 7, []"
  expect 2 [.number 3, .number 10] "returned [10, 11, 12]"
  expect 3 [.number 4, .number 10] "returned 16, [10, 11, 13, 16]"
  expect 3 [.number 9, .number 10] "stopped PIR.Stop.undefined"
  expect 4 [.number 4, .number 10] "returned 16"
  -- The protocol: role 0 collects in its local code and sends, role 1 holds the sequence.
  let sent ← IO.ofExcept (Zkc.Core.Runs.interactive typed [] [] 0 1)
  unless sent.agrees && sent.grouped.describe == "returned [0, 1, 4]" do
    throw (IO.userError s!"protocol: {sent.grouped.describe}")
  -- A count that is a value and has no maximum: many iterations run.
  expectEnd 2 [.number 200000, .number 0] "199998, 199999]"

end Loops.Run
