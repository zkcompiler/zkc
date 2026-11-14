import Zkc.Tests.Core.Check
import Zkc.Tests.Core.Reflexivity
import Zkc.Tests.Core.Builtins
import Zkc.Core.RoundTrip
import Zkc.Core.Laws
import Zkc.Core.Copies
import Zkc.Tests.Core.Runs

/-! Kernel checks for `repeat`: a count of the operation or a count that each participant
holds, the iteration number that each participant holds, and collected values.

- `fixtures/repeats.json` has two protocols of two roles, each over a count that both roles
  hold, within the maximum 8. In `squares` the second role collects the square of its
  iteration number into an unsized sequence. In `sums` each role carries a sum: the first
  adds its iteration number, the second the square of its own. The package elaborates, its
  typed package unelaborates to it, and its printed JSON reads back to it.
- `fixtures/repeats-static.json` has the protocol `fixed`: three iterations, a count of the
  operation, without a count operand. Each role carries a sum, the first collects its sum
  after each iteration and the second the square of its iteration number, into sequences of
  three. `swapped` applies it with the two roles exchanged.
- For an arbitrary model the kernel evaluates each protocol for the side of both roles and
  for the side of each: a role outside the side holds nothing; a count above the maximum
  stops `undefined`; two different counts in one side stop `incomplete`; no iteration returns
  the carried operands and empty sequences; a side without a participant does nothing.
- Refusals: a collected value held by a role that is not a participant, a region that
  yields no collected value, one that yields a collected value of another holder, a result
  used at another size than the count; in JSON, an empty list of collected values.
- The executor runs the grouped meaning and the two role programs against each other under
  the model of the vocabulary's rows (Lean's interpreter, not the kernel).
-/

set_option autoImplicit false

open Zkc.Source Zkc.Core

namespace Repeats

raw_package raw from file "fixtures/repeats.json"

kernel_refl tables : tablesViolation raw.types raw.records raw.variants raw.operations equals none
kernel_refl accepted : (elaborateWritten raw).isOk equals true
kernel_refl elaborates : (elaborate raw).isOk equals true

noncomputable def elaborated : Typed := Typed.ofRaw raw elaborates

typed_literal typed := elaborated

kernel_refl elaborate_eq : elaborate raw equals Except.ok typed
kernel_refl unelaborate_eq : unelaborate typed equals raw

reprinted_package reprinted from file "fixtures/repeats.json"

kernel_refl reprinted_eq : reprinted equals raw

-- The raw bodies: the region's first values are the iteration numbers of the two roles,
-- and it returns the collected values before the carried ones.
kernel_refl bodies : (raw.protocols.map (·.body)) equals
  [.step (.repeat [0, 1] (.runtime 8 [0, 1]) [] [] [⟨.nat, 1⟩]
      (.step (.at 1 (.builtin .natMul [1, 1])) (.ret [2])))
    (.ret [2]),
   .step (.at 0 (.literal (.nat 0)))
    (.step (.at 1 (.literal (.nat 0)))
      (.step (.repeat [0, 1] (.runtime 8 [0, 1]) [2, 3] [] []
          (.step (.at 0 (.builtin .natAdd [2, 0]))
            (.step (.at 1 (.builtin .natMul [1, 1]))
              (.step (.at 1 (.builtin .natAdd [3, 5])) (.ret [4, 6])))))
        (.ret [4, 5])))]

abbrev squares :
    Var typed.protocols ⟨2, [⟨.nat, 0⟩, ⟨.nat, 1⟩], [⟨.seq .nat none, 1⟩], .none, false⟩ :=
  ⟨1, rfl⟩

abbrev sums :
    Var typed.protocols ⟨2, [⟨.nat, 0⟩, ⟨.nat, 1⟩], [⟨.nat, 0⟩, ⟨.nat, 1⟩], .none, false⟩ :=
  ⟨0, rfl⟩

/-- The meaning of a protocol of the package for a side. -/
noncomputable abbrev meaning (model : Model) {header : ProtocolHeader}
    (protocol : Var typed.protocols header) :=
  (typed.program.protocols.table model (typed.program.functionTable model)
    Identities.written).get protocol []

abbrev both : Side := fun _ => true
abbrev left : Side := fun role => Nat.beq role 0
abbrev right : Side := fun role => Nat.beq role 1

/-- Both roles in the side: each sums over its own iteration number, 0 + 1 + 2 + 3 and
0 + 1 + 4 + 9. -/
theorem both_sum (model : Model) :
    meaning model sums both (.cons (4 : Nat) (.cons (4 : Nat) .nil)) =
      .done (.cons (6 : Nat) (.cons (14 : Nat) .nil)) := kernel_rfl%

/-- The first role alone: its own sum, and nothing of the second role. -/
theorem left_sum (model : Model) :
    meaning model sums left (.cons (4 : Nat) (.cons PUnit.unit .nil)) =
      .done (.cons (6 : Nat) (.cons PUnit.unit .nil)) := kernel_rfl%

/-- The second role alone. -/
theorem right_sum (model : Model) :
    meaning model sums right (.cons PUnit.unit (.cons (4 : Nat) .nil)) =
      .done (.cons PUnit.unit (.cons (14 : Nat) .nil)) := kernel_rfl%

/-- No iteration: the carried operands. -/
theorem both_none (model : Model) :
    meaning model sums both (.cons (0 : Nat) (.cons (0 : Nat) .nil)) =
      .done (.cons (0 : Nat) (.cons (0 : Nat) .nil)) := kernel_rfl%

/-- A count above the maximum is outside the domain of the loop: it stops `undefined`. -/
theorem both_beyond (model : Model) :
    meaning model sums both (.cons (9 : Nat) (.cons (9 : Nat) .nil)) = .halt .undefined :=
  kernel_rfl%

theorem left_beyond (model : Model) :
    meaning model sums left (.cons (9 : Nat) (.cons PUnit.unit .nil)) = .halt .undefined :=
  kernel_rfl%

/-- Two counts in one side that differ stop `incomplete`, before the maximum is compared. -/
theorem both_disagree (model : Model) :
    meaning model sums both (.cons (3 : Nat) (.cons (9 : Nat) .nil)) = .halt .incomplete :=
  kernel_rfl%

/-- The check of copies refuses both protocols: the counts are inputs under no agreement. With
`both_disagree`, what the check refuses is a program that stops `incomplete`. -/
theorem counts_refused :
    typed.program.protocols.copies.2 = [(0, ⟨[0], .counts⟩), (1, ⟨[2], .counts⟩)] := kernel_rfl%

/-- A count that is a value: the second role collects the squares of three iteration
numbers into an unsized sequence. -/
theorem both_squares (model : Model) :
    meaning model squares both (.cons (3 : Nat) (.cons (3 : Nat) .nil)) =
      .done (.cons ([0, 1, 4] : List Nat) .nil) := kernel_rfl%

/-- The holder alone collects; the other role alone holds nothing of the sequence. -/
theorem right_squares (model : Model) :
    meaning model squares right (.cons PUnit.unit (.cons (3 : Nat) .nil)) =
      .done (.cons ([0, 1, 4] : List Nat) .nil) := kernel_rfl%

theorem left_squares (model : Model) :
    meaning model squares left (.cons (3 : Nat) (.cons PUnit.unit .nil)) =
      .done (.cons PUnit.unit .nil) := kernel_rfl%

/-- No iteration collects the empty sequence. -/
theorem no_squares (model : Model) :
    meaning model squares both (.cons (0 : Nat) (.cons (0 : Nat) .nil)) =
      .done (.cons ([] : List Nat) .nil) := kernel_rfl%

theorem squares_beyond (model : Model) :
    meaning model squares both (.cons (9 : Nat) (.cons (9 : Nat) .nil)) = .halt .undefined :=
  kernel_rfl%

#print axioms elaborate_eq
#print axioms reprinted_eq
#print axioms both_sum
#print axioms left_sum
#print axioms right_sum
#print axioms both_beyond
#print axioms both_disagree
#print axioms both_squares
#print axioms right_squares
#print axioms no_squares

/-! ## A count of the operation -/

namespace Fixed

raw_package raw from file "fixtures/repeats-static.json"

kernel_refl accepted : (elaborateWritten raw).isOk equals true
kernel_refl elaborates : (elaborate raw).isOk equals true

noncomputable def elaborated : Typed := Typed.ofRaw raw elaborates

typed_literal typed := elaborated

kernel_refl elaborate_eq : elaborate raw equals Except.ok typed
kernel_refl unelaborate_eq : unelaborate typed equals raw

reprinted_package reprinted from file "fixtures/repeats-static.json"

kernel_refl reprinted_eq : reprinted equals raw

-- The raw body: the count is a number of the instruction, the instruction has no count
-- operand, and its results are the two sequences, then the two carried values.
kernel_refl fixed_body : (raw.protocols.head?.map (·.body)) equals
  some (.step (.at 0 (.literal (.nat 0)))
    (.step (.at 1 (.literal (.nat 1)))
      (.step (.repeat [0, 1] (.static 3) [0, 1] [] [⟨.nat, 0⟩, ⟨.nat, 1⟩]
          (.step (.at 0 (.builtin .natAdd [2, 0]))
            (.step (.at 1 (.builtin .natAdd [3, 1]))
              (.step (.at 1 (.builtin .natMul [1, 1])) (.ret [4, 6, 4, 5])))))
        (.ret [2, 3, 4, 5]))))

abbrev fixed :
    Var typed.protocols
      ⟨2, [], [⟨.seq .nat (some 3), 0⟩, ⟨.seq .nat (some 3), 1⟩, ⟨.nat, 0⟩, ⟨.nat, 1⟩], .none,
        false⟩ :=
  ⟨1, rfl⟩

abbrev swapped :
    Var typed.protocols
      ⟨2, [], [⟨.seq .nat (some 3), 1⟩, ⟨.seq .nat (some 3), 0⟩, ⟨.nat, 1⟩, ⟨.nat, 0⟩], .none,
        false⟩ :=
  ⟨0, rfl⟩

noncomputable abbrev meaning (model : Model) {header : ProtocolHeader}
    (protocol : Var typed.protocols header) :=
  (typed.program.protocols.table model (typed.program.functionTable model)
    Identities.written).get protocol []

/-- Three iterations for the side of both roles: the first role's sums 0, 1, 3 and the
second's squares 0, 1, 4, in sequences of three, then the sums 0 + 0 + 1 + 2 and
1 + 0 + 1 + 2. -/
theorem both_collect (model : Model) :
    meaning model fixed both .nil =
      .done (.cons ⟨[0, 1, 3], rfl⟩ (.cons ⟨[0, 1, 4], rfl⟩
        (.cons (3 : Nat) (.cons (4 : Nat) .nil)))) := kernel_rfl%

/-- A side with one participant runs the three iterations of that role and holds its
sequence. -/
theorem left_collects (model : Model) :
    meaning model fixed left .nil =
      .done (.cons ⟨[0, 1, 3], rfl⟩ (.cons PUnit.unit
        (.cons (3 : Nat) (.cons PUnit.unit .nil)))) := kernel_rfl%

theorem right_collects (model : Model) :
    meaning model fixed right .nil =
      .done (.cons PUnit.unit (.cons ⟨[0, 1, 4], rfl⟩
        (.cons PUnit.unit (.cons (4 : Nat) .nil)))) := kernel_rfl%

/-- A side without a participant does nothing and holds nothing. -/
theorem none_collects (model : Model) :
    meaning model fixed (fun _ => false) .nil =
      .done (.cons PUnit.unit (.cons PUnit.unit (.cons PUnit.unit (.cons PUnit.unit .nil)))) :=
  kernel_rfl%

/-- The application with the roles exchanged: the second role collects the sums. -/
theorem swapped_collects (model : Model) :
    meaning model swapped right .nil =
      .done (.cons ⟨[0, 1, 3], rfl⟩ (.cons PUnit.unit
        (.cons (3 : Nat) (.cons PUnit.unit .nil)))) := kernel_rfl%

#print axioms elaborate_eq
#print axioms reprinted_eq
#print axioms both_collect
#print axioms left_collects
#print axioms none_collects
#print axioms swapped_collects

end Fixed

/-! ## Refusals -/

/-- The refusal of a package with one protocol of two roles without inputs. -/
abbrev refusalOf (outputs : List Located) (body : Raw.ProtocolRegion) : Option Refusal :=
  match elaborate ⟨[], [], [], [], [], [⟨false, 2, [], outputs, [], body⟩], none⟩ with
  | .error refusal => some refusal
  | .ok _ => none

-- The same loop with the results it has.
kernel_refl collecting_accepted :
    refusalOf [⟨.seq .nat (some 2), 1⟩]
      (.step (.repeat [0, 1] (.static 2) [] [] [⟨.nat, 1⟩] (.ret [1])) (.ret [0])) equals none

-- A collected value held by a role that is not a participant.
kernel_refl outside_collected :
    refusalOf [⟨.seq .nat (some 2), 1⟩]
      (.step (.repeat [0] (.static 2) [] [] [⟨.nat, 1⟩] (.ret [0])) (.ret [0])) equals
      some ⟨.operand, some (.protocol 0), [0]⟩

-- The region yields no value for the collected entry: the refusal is at what the region
-- of the first instruction returns.
kernel_refl missing_collected :
    refusalOf [⟨.seq .nat (some 2), 1⟩]
      (.step (.repeat [0, 1] (.static 2) [] [] [⟨.nat, 1⟩] (.ret [])) (.ret [0])) equals
      some ⟨.operand, some (.protocol 0), [0, 0, 0]⟩

-- The region yields the iteration number of the other role for the collected entry.
kernel_refl other_collected :
    refusalOf [⟨.seq .nat (some 2), 1⟩]
      (.step (.repeat [0, 1] (.static 2) [] [] [⟨.nat, 1⟩] (.ret [0])) (.ret [0])) equals
      some ⟨.operand, some (.protocol 0), [0, 0, 0]⟩

-- The collected sequence of a count of the instruction has that size, and no other: the
-- refusal is at what the body returns, after its one instruction.
kernel_refl other_size :
    refusalOf [⟨.seq .nat (some 3), 1⟩]
      (.step (.repeat [0, 1] (.static 2) [] [] [⟨.nat, 1⟩] (.ret [1])) (.ret [0])) equals
      some ⟨.operand, some (.protocol 0), [1]⟩

end Repeats

/-! ## The JSON text -/

-- A repeat that collects nothing has one spelling: the one without a list of collected
-- values.
#eval show IO Unit from do
  let parse (text : String) : IO Zkc.Json := match Zkc.Json.parse text with
    | .ok json => pure json
    | .error message => throw (IO.userError message)
  let region := "[[], []]"
  match Raw.readProtocolStep #[] (← parse s!"[\"repeat\", [0, 1], [\"static\", 2], [], [], {region}]") with
  | .ok (.repeat [0, 1] (.static 2) [] [] [] _) => pure ()
  | .ok _ => throw (IO.userError "the repeat is read as another instruction")
  | .error message => throw (IO.userError message)
  match Raw.readProtocolStep #[]
      (← parse s!"[\"repeat\", [0, 1], [\"static\", 2], [], [], {region}, []]") with
  | .ok _ => throw (IO.userError "a repeat with an empty list of collected values is read")
  | .error message =>
      unless message == "repeat: a repeat that collects nothing does not list collected values" do
        throw (IO.userError s!"unexpected refusal: {message}")

/-! ## The executor -/

namespace Repeats.Run

open Zkc.Core.Concrete Zkc.Core.Execute Builtins.Run

#eval show IO Unit from do
  let read (path : String) : IO Typed := do
    let raw ← match Raw.parsePackage (← IO.FS.readFile path) with
      | .ok raw => pure raw
      | .error message => throw (IO.userError message)
    match elaborateWritten raw with
    | .ok typed => pure typed
    | .error refusal => throw (IO.userError s!"refused: {repr refusal}")
  let typed ← read (package_file "fixtures/repeats.json")
  let expect (inputs : List Datum) (expected : String) : IO Unit := do
    let run ← IO.ofExcept (Zkc.Core.Runs.interactive typed inputs [] 0 1)
    unless run.agrees && run.grouped.describe == expected do
      throw (IO.userError s!"{run.grouped.describe}, not {expected}")
  -- The grouped meaning and the two role programs, run against each other, end alike.
  expect [.number 4, .number 4] "returned 6, 14"
  expect [.number 0, .number 0] "returned 0, 0"
  expect [.number 8, .number 8] "returned 28, 140"
  expect [.number 9, .number 9] "stopped PIR.Stop.undefined"
  -- A count of the operation, applied with the roles exchanged: each role program collects
  -- in its own loop.
  let fixed ← read (package_file "fixtures/repeats-static.json")
  let run ← IO.ofExcept (Zkc.Core.Runs.interactive fixed [] [] 0 1)
  unless run.agrees && run.grouped.describe == "returned [0, 1, 3], [0, 1, 4], 3, 4" do
    throw (IO.userError s!"a count of the operation: {run.grouped.describe}")

end Repeats.Run
