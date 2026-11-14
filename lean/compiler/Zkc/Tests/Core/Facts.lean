import Zkc.Tests.Core.Check
import Zkc.Tests.Core.Reflexivity
import Zkc.Core.RoundTrip
import Zkc.Core.FactsSound

/-! Kernel checks for the check of facts and for the domain row of a restricted row.

- `fixtures/facts.json` has a pure row with one `bool` output, a restricted row that names
  it as its domain row, and twenty-seven functions that pass the check of facts:
  - `index`: a guard `i < length(xs)`, then `xs[i]`;
  - `slice`: a guard `start + count <= length(xs)`, then `xs[start..start + count]`; `pair`:
    the same into a sequence of two elements, the count being the literal 2;
  - `each`: a loop over a count of the operation that reads `xs[i]` of a sequence of that
    size; `all`: a loop whose count is `length(xs)` and whose region captures it; `bounded`:
    a guard `n <= 8`, then a loop over `n` that reads a sequence of eight elements;
  - `offset`: a guard `a <= length(xs)`, then a loop over `length(xs) - a` that reads
    `xs[a + i]`: the index of a range that does not start at 0;
  - `minus`: `a - b` in the first region of an `if` on `b <= a`; `minus_else`: `a - b` in the
    second region of an `if` on `a < b`;
  - `quotient`: `a / b` and `a % b` after a guard `b != 0`; `either`: `a / b` in the second
    region of an `if` on `b == 0 or a < b`;
  - `four`: `seq.sized` after a guard `length(xs) == 4`; `small`: `nat.below` after a guard
    `a < 4`; `square`: `nat.below` of `a * a` to 10 after the same guard;
  - `nonzero`: the restricted row after a guard on its domain row applied to the same
    operand;
  - `both`: two reads after a guard on `i < length(xs) and j < length(xs)`;
  - `inside`: a read in the first region of an `if` that captures the length;
  - `joined`: `nat.below` of the result of an `if` whose regions return a value below 4 and
    the literal 5;
  - `calls`: a call of `index`; `power`: `nat.below` of `2 ^ a` to 5 after a guard `a < 3`;
  - `weight`: the number of true flags of a sequence of two, a loop that carries a sum of
    terms in `0..1`, converted to `fin 3`; `weight_none`: the same over a sequence of no
    element, whose loop runs no iteration and whose region reads without a justification;
    `total`: a sum of terms in `0..3` over a count guarded `<= 5`, converted to `fin 16`;
    `running`: the loop of `weight` that also collects the sum after each iteration;
  - `first_is_one`: a guard on `0 < length(xs) and xs[0] == 1`, written as an `if` whose
    second region returns the literal `false`, then `xs[0]`; `first_or_zero`: an `if` on
    that conditional with the read in its first region; `empty_or_one`: an `if` on
    `length(xs) == 0 or xs[0] == 1`, written as an `if` whose first region returns the
    literal `true`, with the read in its second region.
  The package elaborates and round-trips, the kernel evaluates the check, and for every
  model that satisfies the domain laws every function never stops `undefined`.
- `fixtures/facts-unjustified.json` has fifteen functions that are admitted and do not
  pass: the same reads, slices, subtractions and conversions without their guards; a
  subtraction under the condition that does not order it; a read in a region that does not
  capture the length; a restricted row without a justification, with its domain row applied
  to another operand, and without a domain row; a read at a carried value of a loop; a read
  that would need two orders in a chain; a conversion of a carried value that is a product
  and not a sum; a read after a guard on an `if` whose second region returns the literal
  `true`. The kernel finds the first application of each that is not justified.
- The tables are refused when a domain row is not an earlier pure row with the inputs of
  its restricted row and the one output `bool`.
-/

set_option autoImplicit false

open Zkc.Source Zkc.Core

namespace Facts

/-! ## Functions that pass -/

raw_package raw from file "fixtures/facts.json"

kernel_refl tables : tablesViolation raw.types raw.records raw.variants raw.operations equals none
kernel_refl kinds :
    (raw.operations.map (·.signature.kind)) equals [.pure, .restricted (some 0)]
kernel_refl accepted : (elaborateWritten raw).isOk equals true
kernel_refl elaborates : (elaborate raw).isOk equals true

noncomputable def elaborated : Typed := Typed.ofRaw raw elaborates

typed_literal typed := elaborated

kernel_refl elaborate_eq : elaborate raw equals Except.ok typed
kernel_refl unelaborate_eq : unelaborate typed equals raw

reprinted_package reprinted from file "fixtures/facts.json"

kernel_refl reprinted_eq : reprinted equals raw

-- Every function passes the check of facts.
kernel_refl justified : typed.program.justified equals true
kernel_refl none_unjustified : typed.program.functions.unjustified equals []

/-- For every model that satisfies the domain laws of the package's table, every function
of the package never stops `undefined`, on any arguments. -/
theorem never_undefined (model : Model) (laws : model.DomainLaws (typed.table.map (·.signature)))
    {header : FunctionHeader} (callee : Var typed.functions header)
    (arguments : Values model.Value header.inputs) :
    NeverStops .undefined ((typed.program.functionTable model).get callee arguments) :=
  Program.never_undefined laws typed.program justified callee arguments

abbrev index : Var typed.functions ⟨[.seq .nat none, .nat], [.nat], false⟩ := ⟨26, rfl⟩
abbrev slice : Var typed.functions ⟨[.seq .nat none, .nat, .nat], [.seq .nat none], false⟩ :=
  ⟨25, rfl⟩
abbrev each : Var typed.functions ⟨[.seq .nat (some 4)], [.seq .nat (some 4)], false⟩ := ⟨23, rfl⟩
abbrev offset : Var typed.functions ⟨[.seq .nat none, .nat], [.seq .nat none], false⟩ := ⟨20, rfl⟩
abbrev minus : Var typed.functions ⟨[.nat, .nat], [.nat], false⟩ := ⟨19, rfl⟩
abbrev quotient : Var typed.functions ⟨[.nat, .nat], [.nat, .nat], false⟩ := ⟨17, rfl⟩
abbrev nonzero : Var typed.functions ⟨[.nominal 0], [.nominal 1], false⟩ := ⟨14, rfl⟩
abbrev weight : Var typed.functions ⟨[.seq .bool (some 2)], [.fin 3], false⟩ := ⟨6, rfl⟩
abbrev weightNone : Var typed.functions ⟨[.seq .bool (some 0)], [.fin 3], false⟩ := ⟨5, rfl⟩
abbrev total : Var typed.functions ⟨[.nat], [.fin 16], false⟩ := ⟨4, rfl⟩
abbrev firstIsOne : Var typed.functions ⟨[.seq .nat none], [.nat], false⟩ := ⟨3, rfl⟩
abbrev emptyOrOne : Var typed.functions ⟨[.seq .nat none], [.nat], false⟩ := ⟨1, rfl⟩
abbrev running :
    Var typed.functions ⟨[.seq .bool (some 2)], [.fin 3, .seq .nat (some 2)], false⟩ := ⟨0, rfl⟩

/-- A guarded read never stops `undefined`, whatever the sequence and the position. -/
theorem index_defined (model : Model) (laws : model.DomainLaws (typed.table.map (·.signature)))
    (xs : List Nat) (position : Nat) :
    NeverStops .undefined
      ((typed.program.functionTable model).get index (.cons xs (.cons position .nil))) :=
  never_undefined model laws index _

theorem slice_defined (model : Model) (laws : model.DomainLaws (typed.table.map (·.signature)))
    (xs : List Nat) (start count : Nat) :
    NeverStops .undefined
      ((typed.program.functionTable model).get slice
        (.cons xs (.cons start (.cons count .nil)))) :=
  never_undefined model laws slice _

theorem each_defined (model : Model) (laws : model.DomainLaws (typed.table.map (·.signature)))
    (xs : { values : List Nat // values.length = 4 }) :
    NeverStops .undefined ((typed.program.functionTable model).get each (.cons xs .nil)) :=
  never_undefined model laws each _

theorem offset_defined (model : Model) (laws : model.DomainLaws (typed.table.map (·.signature)))
    (xs : List Nat) (start : Nat) :
    NeverStops .undefined
      ((typed.program.functionTable model).get offset (.cons xs (.cons start .nil))) :=
  never_undefined model laws offset _

theorem minus_defined (model : Model) (laws : model.DomainLaws (typed.table.map (·.signature)))
    (a b : Nat) :
    NeverStops .undefined
      ((typed.program.functionTable model).get minus (.cons a (.cons b .nil))) :=
  never_undefined model laws minus _

theorem quotient_defined (model : Model) (laws : model.DomainLaws (typed.table.map (·.signature)))
    (a b : Nat) :
    NeverStops .undefined
      ((typed.program.functionTable model).get quotient (.cons a (.cons b .nil))) :=
  never_undefined model laws quotient _

/-- The restricted row is applied only where its domain row is true: under the domain law
the application has a value, whatever the model makes of the two rows. -/
theorem nonzero_defined (model : Model) (laws : model.DomainLaws (typed.table.map (·.signature)))
    (element : model.Carrier 0) :
    NeverStops .undefined ((typed.program.functionTable model).get nonzero (.cons element .nil)) :=
  never_undefined model laws nonzero _

/-- A loop that carries a sum: the conversion of its result is justified by the interval of
the sum over the iterations. -/
theorem weight_defined (model : Model) (laws : model.DomainLaws (typed.table.map (·.signature)))
    (flags : { values : List Bool // values.length = 2 }) :
    NeverStops .undefined ((typed.program.functionTable model).get weight (.cons flags .nil)) :=
  never_undefined model laws weight _

theorem total_defined (model : Model) (laws : model.DomainLaws (typed.table.map (·.signature)))
    (count : Nat) :
    NeverStops .undefined ((typed.program.functionTable model).get total (.cons count .nil)) :=
  never_undefined model laws total _

/-- A guard on an `if` that is a conjunction gives the facts of its condition. -/
theorem firstIsOne_defined (model : Model)
    (laws : model.DomainLaws (typed.table.map (·.signature))) (xs : List Nat) :
    NeverStops .undefined ((typed.program.functionTable model).get firstIsOne (.cons xs .nil)) :=
  never_undefined model laws firstIsOne _

theorem emptyOrOne_defined (model : Model)
    (laws : model.DomainLaws (typed.table.map (·.signature))) (xs : List Nat) :
    NeverStops .undefined ((typed.program.functionTable model).get emptyOrOne (.cons xs .nil)) :=
  never_undefined model laws emptyOrOne _

/-- Two true flags have the weight 2. -/
theorem weight_counts (model : Model) :
    (typed.program.functions.table model).get weight (.cons ⟨[true, true], rfl⟩ .nil) =
      .done (.cons (⟨2, by decide⟩ : Fin 3) .nil) := kernel_rfl%

/-- No flag has the weight 0: the loop runs no iteration. -/
theorem weightNone_counts (model : Model) :
    (typed.program.functions.table model).get weightNone (.cons ⟨[], rfl⟩ .nil) =
      .done (.cons (⟨0, by decide⟩ : Fin 3) .nil) := kernel_rfl%

/-- The sum that is carried and collected: the collected sequence comes before the carried
result, and the conversion of the carried result is justified as for `weight`. -/
theorem running_defined (model : Model) (laws : model.DomainLaws (typed.table.map (·.signature)))
    (flags : { values : List Bool // values.length = 2 }) :
    NeverStops .undefined ((typed.program.functionTable model).get running (.cons flags .nil)) :=
  never_undefined model laws running _

theorem running_counts (model : Model) :
    (typed.program.functions.table model).get running (.cons ⟨[true, true], rfl⟩ .nil) =
      .done (.cons (⟨2, by decide⟩ : Fin 3) (.cons ⟨[1, 2], rfl⟩ .nil)) := kernel_rfl%

/-- Five terms `i % 4` sum to `0 + 1 + 2 + 3 + 0`. -/
theorem total_sums (model : Model) :
    (typed.program.functions.table model).get total (.cons (5 : Nat) .nil) =
      .done (.cons (⟨6, by decide⟩ : Fin 16) .nil) := kernel_rfl%

/-- The statement is not vacuous: the one-point model satisfies the domain laws. -/
theorem unit_index_defined (xs : List Nat) (position : Nat) :
    NeverStops .undefined
      ((typed.program.functionTable Model.unit).get index (.cons xs (.cons position .nil))) :=
  index_defined Model.unit (Model.unit_domainLaws _) xs position

/-- The loop over a range that does not start at 0 reads the elements from the start on. -/
theorem offset_reads (model : Model) :
    (typed.program.functions.table model).get offset
        (.cons ([5, 7, 9] : List Nat) (.cons (1 : Nat) .nil)) =
      .done (.cons ([7, 9] : List Nat) .nil) := kernel_rfl%

/-- A start beyond the length stops at the guard, with the guard's reason. -/
theorem offset_beyond (model : Model) :
    (typed.program.functions.table model).get offset
        (.cons ([5, 7, 9] : List Nat) (.cons (4 : Nat) .nil)) =
      .halt .reject := kernel_rfl%

/-! ## Functions that do not pass -/

raw_package unguarded from file "fixtures/facts-unjustified.json"

kernel_refl unguarded_tables :
    tablesViolation unguarded.types unguarded.records unguarded.variants unguarded.operations
      equals none
-- The package is admitted: the check of facts is not a residual condition.
kernel_refl unguarded_accepted : (elaborateWritten unguarded).isOk equals true
kernel_refl unguarded_elaborates : (elaborate unguarded).isOk equals true

noncomputable def unguardedElaborated : Typed := Typed.ofRaw unguarded unguarded_elaborates

typed_literal unguardedTyped := unguardedElaborated

kernel_refl unguarded_unelaborate : unelaborate unguardedTyped equals unguarded

kernel_refl unguarded_fails : unguardedTyped.program.justified equals false

-- The first application of each function that is not justified: the function's number, the
-- path of the instruction and the requirement it does not meet.
kernel_refl first_unjustified :
    unguardedTyped.program.functions.unjustified equals
      [(0, ⟨[0], .position⟩), (1, ⟨[1], .slice⟩), (2, ⟨[0], .ordered⟩),
       (3, ⟨[1, 0, 0], .ordered⟩), (4, ⟨[0], .positive⟩), (5, ⟨[0], .size⟩),
       (6, ⟨[0], .bound⟩), (7, ⟨[2, 0, 0], .position⟩), (8, ⟨[0], .domain⟩),
       (9, ⟨[2], .domain⟩), (10, ⟨[0], .noDomain⟩), (11, ⟨[1, 0, 0], .position⟩),
       (12, ⟨[5], .position⟩), (13, ⟨[2], .bound⟩), (14, ⟨[5], .position⟩)]

/-! ## The domain row of a restricted row -/

/-- A row of a table of test rows. -/
abbrev row (name : Nat) (inputs outputs : List Ty) (kind : OperationKind) : Operation :=
  ⟨⟨[97, name], []⟩, ⟨inputs, outputs, kind⟩⟩

kernel_refl domain_row :
    tablesViolation [] [] [] [row 48 [.nat] [.bool] .pure, row 49 [.nat] [.nat] (.restricted (some 0))]
      equals none
-- The domain row is a later row of the table.
kernel_refl later_row :
    tablesViolation [] [] [] [row 48 [.nat] [.nat] (.restricted (some 1)), row 49 [.nat] [.bool] .pure]
      equals some .domainRow
-- A row is not its own domain row.
kernel_refl own_row :
    tablesViolation [] [] [] [row 48 [.nat] [.bool] (.restricted (some 0))] equals some .domainRow
-- The domain row is not pure.
kernel_refl restricted_row :
    tablesViolation [] [] []
      [row 48 [.nat] [.bool] (.restricted none), row 49 [.nat] [.nat] (.restricted (some 0))]
      equals some .domainRow
-- The domain row has other inputs.
kernel_refl other_inputs :
    tablesViolation [] [] []
      [row 48 [.nat, .nat] [.bool] .pure, row 49 [.nat] [.nat] (.restricted (some 0))]
      equals some .domainRow
-- The domain row does not return one `bool`.
kernel_refl other_output :
    tablesViolation [] [] [] [row 48 [.nat] [.nat] .pure, row 49 [.nat] [.nat] (.restricted (some 0))]
      equals some .domainRow
-- The table has no such row.
kernel_refl missing_row :
    tablesViolation [] [] [] [row 48 [.nat] [.nat] (.restricted (some 7))] equals some .domainRow

#print axioms never_undefined
#print axioms index_defined
#print axioms nonzero_defined
#print axioms unit_index_defined
#print axioms weight_defined
#print axioms firstIsOne_defined
#print axioms weight_counts
#print axioms running_counts
#print axioms offset_reads
#print axioms justified
#print axioms first_unjustified
#print axioms reprinted_eq

end Facts

-- The kind of a restricted row with a domain row is `["restricted", d]` in JSON.
#eval show IO Unit from do
  let text ← IO.FS.readFile (package_file "fixtures/facts.json")
  let raw ← match Raw.parsePackage text with
    | .ok raw => pure raw
    | .error message => throw (IO.userError message)
  let printed := (Raw.printPackage raw).render
  unless (printed.splitOn "[\"restricted\",0]").length == 2 do
    throw (IO.userError "the printed package does not spell the domain row")
