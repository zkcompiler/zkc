import Zkc.Tests.Core.Check
import Zkc.Tests.Core.Reflexivity
import Zkc.Core.RoundTrip
import Zkc.Core.ProtocolFactsProject

/-! Kernel checks for the check of facts over protocol bodies.

- `fixtures/role-facts.json` has a pure row with one `bool` output, a restricted row that
  names it as its domain row, and twelve protocols of two roles that pass the check of
  facts:
  - `guarded`: the prover guards `i < length(xs)` in one `at` and reads `xs[i]` in a later
    one; the element goes to the verifier;
  - `relayed`: the prover guards and sends the position; the verifier guards the received
    position against its own sequence and reads;
  - `chosen`: a `choose` on the condition `i < length(xs)`, of which the verifier holds a
    received copy, with the prover's read in the region of `true`;
  - `counted`: a `repeat` over the count 4 of the operation whose region reads a sequence
    of four elements at the prover's iteration number; `never`: a `repeat` over the count 0
    whose region reads a sequence of no element;
  - `ranged`: a `repeat` over a count that is a value, `length(xs)` for the prover and a
    received copy for the verifier; the region captures the prover's count and reads `xs`
    at the prover's iteration number;
  - `inverse`: the restricted row, applied by the prover after its guard on the domain row
    applied to the same operand;
  - `nested`: a read in the first region of an `if` that the prover performs on
    `i < length(xs)`, the region capturing the length;
  - `armed`: a guard before a `choose` on an arm number, and the read in an arm, which
    captures the length;
  - `swapped`: an application of `guarded` with the two roles exchanged;
  - `joined`: `nat.below` of the result of a `choose` whose regions return the literals 1
    and 0, to 2; `blocked`: `nat.below` of the result of a block that returns the literal 3,
    to 4.
  The package elaborates and round-trips, the kernel evaluates the check, and for every
  model that satisfies the domain laws every protocol never stops `undefined`, for every
  side, under any path and with any identities; so does every role program that projection
  gives, on any arguments.
- `fixtures/role-facts-unjustified.json` has ten protocols that are admitted and do not
  pass: the read of `guarded` without its guard; a verifier that reads at a position that
  the prover guarded and sent; the read of `chosen` in the region of `false`; the loop of
  `counted` over a sequence of three elements; the loop of `ranged` whose region does not
  capture the count; a verifier that applies the restricted row to an element that the
  prover tested and sent; the restricted row without a guard; the read of `nested` in the
  second region; a read at a carried value of a `repeat`; the conversion of `joined` to 1.
  The kernel finds the first application of each that is not justified, and evaluates two
  of them to the stop `undefined`.
-/

set_option autoImplicit false

open Zkc.Source Zkc.Core

namespace RoleFacts

/-! ## Protocols that pass -/

raw_package raw from file "fixtures/role-facts.json"

kernel_refl tables : tablesViolation raw.types raw.records raw.variants raw.operations equals none
kernel_refl accepted : (elaborateWritten raw).isOk equals true
kernel_refl elaborates : (elaborate raw).isOk equals true

noncomputable def elaborated : Typed := Typed.ofRaw raw elaborates

typed_literal typed := elaborated

kernel_refl elaborate_eq : elaborate raw equals Except.ok typed
kernel_refl unelaborate_eq : unelaborate typed equals raw

reprinted_package reprinted from file "fixtures/role-facts.json"

kernel_refl reprinted_eq : reprinted equals raw

-- Every protocol passes the check of facts, and so does the program.
kernel_refl justified : typed.program.justified equals true
kernel_refl none_unjustified : typed.program.protocols.unjustified equals []

/-- For every model that satisfies the domain laws of the package's table and every side,
every protocol of the package never stops `undefined`: with any identities, under any path,
on any values, whatever the replies of its effects. -/
theorem never_undefined (model : Model) (laws : model.DomainLaws (typed.table.map (·.signature)))
    (identities : Identities) {header : ProtocolHeader} (callee : Var typed.protocols header)
    (path : List Nat) (side : Side) (arguments : Values (SideValue model side) header.inputs) :
    NeverStops .undefined
      ((typed.program.protocolTable model identities).get callee path side arguments) :=
  Program.protocols_never_undefined laws typed.program justified identities callee path side
    arguments

abbrev guarded :
    Var typed.protocols ⟨2, [⟨.seq .nat none, 0⟩, ⟨.nat, 0⟩], [⟨.nat, 1⟩], .none, false⟩ :=
  ⟨11, rfl⟩
abbrev relayed :
    Var typed.protocols
      ⟨2, [⟨.seq .nat none, 0⟩, ⟨.seq .nat none, 1⟩, ⟨.nat, 0⟩], [⟨.nat, 1⟩], .none, false⟩ :=
  ⟨10, rfl⟩
abbrev chosen :
    Var typed.protocols ⟨2, [⟨.seq .nat none, 0⟩, ⟨.nat, 0⟩], [⟨.nat, 0⟩], .none, false⟩ :=
  ⟨9, rfl⟩
abbrev counted :
    Var typed.protocols
      ⟨2, [⟨.seq .nat (some 4), 0⟩], [⟨.seq .nat (some 4), 1⟩], .none, false⟩ :=
  ⟨8, rfl⟩
abbrev ranged :
    Var typed.protocols ⟨2, [⟨.seq .nat none, 0⟩], [⟨.seq .nat none, 1⟩], .none, false⟩ :=
  ⟨7, rfl⟩
abbrev inverse :
    Var typed.protocols ⟨2, [⟨.nominal 0, 0⟩], [⟨.nominal 1, 1⟩], .none, false⟩ :=
  ⟨6, rfl⟩
abbrev never :
    Var typed.protocols
      ⟨2, [⟨.seq .nat (some 0), 0⟩], [⟨.seq .nat (some 0), 0⟩], .none, false⟩ :=
  ⟨5, rfl⟩
abbrev nested :
    Var typed.protocols ⟨2, [⟨.seq .nat none, 0⟩, ⟨.nat, 0⟩], [⟨.nat, 0⟩], .none, false⟩ :=
  ⟨4, rfl⟩
abbrev armed :
    Var typed.protocols
      ⟨2, [⟨.seq .nat none, 0⟩, ⟨.nat, 0⟩, ⟨.fin 2, 0⟩], [⟨.nat, 0⟩], .none, false⟩ :=
  ⟨3, rfl⟩
abbrev swapped :
    Var typed.protocols ⟨2, [⟨.seq .nat none, 1⟩, ⟨.nat, 1⟩], [⟨.nat, 0⟩], .none, false⟩ :=
  ⟨2, rfl⟩
abbrev joined : Var typed.protocols ⟨2, [⟨.bool, 0⟩], [⟨.fin 2, 0⟩], .none, false⟩ := ⟨1, rfl⟩
abbrev blocked : Var typed.protocols ⟨2, [⟨.nat, 0⟩], [⟨.fin 4, 0⟩], .none, false⟩ := ⟨0, rfl⟩

/-- A read after a guard of the same role never stops `undefined`, for any side: whatever
the sequence and the position, and for the verifier alone whatever it receives. -/
theorem guarded_defined (model : Model) (laws : model.DomainLaws (typed.table.map (·.signature)))
    (identities : Identities) (path : List Nat) (side : Side)
    (arguments : Values (SideValue model side) [⟨.seq .nat none, 0⟩, ⟨.nat, 0⟩]) :
    NeverStops .undefined
      ((typed.program.protocolTable model identities).get guarded path side arguments) :=
  never_undefined model laws identities guarded path side arguments

/-- The verifier reads at a received position under a guard of its own: whatever position
arrives, it does not stop `undefined`. -/
theorem relayed_defined (model : Model) (laws : model.DomainLaws (typed.table.map (·.signature)))
    (identities : Identities) (path : List Nat) (side : Side)
    (arguments : Values (SideValue model side)
      [⟨.seq .nat none, 0⟩, ⟨.seq .nat none, 1⟩, ⟨.nat, 0⟩]) :
    NeverStops .undefined
      ((typed.program.protocolTable model identities).get relayed path side arguments) :=
  never_undefined model laws identities relayed path side arguments

/-- The read in the region of `true` of a `choose` on its condition. -/
theorem chosen_defined (model : Model) (laws : model.DomainLaws (typed.table.map (·.signature)))
    (identities : Identities) (path : List Nat) (side : Side)
    (arguments : Values (SideValue model side) [⟨.seq .nat none, 0⟩, ⟨.nat, 0⟩]) :
    NeverStops .undefined
      ((typed.program.protocolTable model identities).get chosen path side arguments) :=
  never_undefined model laws identities chosen path side arguments

/-- The read at the iteration number of a `repeat` over the count of the operation. -/
theorem counted_defined (model : Model) (laws : model.DomainLaws (typed.table.map (·.signature)))
    (identities : Identities) (path : List Nat) (side : Side)
    (arguments : Values (SideValue model side) [⟨.seq .nat (some 4), 0⟩]) :
    NeverStops .undefined
      ((typed.program.protocolTable model identities).get counted path side arguments) :=
  never_undefined model laws identities counted path side arguments

/-- The read at the iteration number of a `repeat` whose region captures the count. -/
theorem ranged_defined (model : Model) (laws : model.DomainLaws (typed.table.map (·.signature)))
    (identities : Identities) (path : List Nat) (side : Side)
    (arguments : Values (SideValue model side) [⟨.seq .nat none, 0⟩]) :
    NeverStops .undefined
      ((typed.program.protocolTable model identities).get ranged path side arguments) :=
  never_undefined model laws identities ranged path side arguments

/-- The restricted row is applied by a role only where its domain row is true: under the
domain law the application has a value, whatever the model makes of the two rows. -/
theorem inverse_defined (model : Model) (laws : model.DomainLaws (typed.table.map (·.signature)))
    (identities : Identities) (path : List Nat) (side : Side)
    (arguments : Values (SideValue model side) [⟨.nominal 0, 0⟩]) :
    NeverStops .undefined
      ((typed.program.protocolTable model identities).get inverse path side arguments) :=
  never_undefined model laws identities inverse path side arguments

/-- An application of a protocol that passes. -/
theorem swapped_defined (model : Model) (laws : model.DomainLaws (typed.table.map (·.signature)))
    (identities : Identities) (path : List Nat) (side : Side)
    (arguments : Values (SideValue model side) [⟨.seq .nat none, 1⟩, ⟨.nat, 1⟩]) :
    NeverStops .undefined
      ((typed.program.protocolTable model identities).get swapped path side arguments) :=
  never_undefined model laws identities swapped path side arguments

/-- The conversion of the result of a `choose` is justified by the intervals of what its
regions return. -/
theorem joined_defined (model : Model) (laws : model.DomainLaws (typed.table.map (·.signature)))
    (identities : Identities) (path : List Nat) (side : Side)
    (arguments : Values (SideValue model side) [⟨.bool, 0⟩]) :
    NeverStops .undefined
      ((typed.program.protocolTable model identities).get joined path side arguments) :=
  never_undefined model laws identities joined path side arguments

/-- The statement is not vacuous: the one-point model satisfies the domain laws. -/
theorem unit_guarded_defined (side : Side)
    (arguments : Values (SideValue Model.unit side) [⟨.seq .nat none, 0⟩, ⟨.nat, 0⟩]) :
    NeverStops .undefined
      ((typed.program.protocolTable Model.unit Identities.written).get guarded [] side
        arguments) :=
  guarded_defined Model.unit (Model.unit_domainLaws _) Identities.written [] side arguments

/-- The meaning of a protocol of the package for a side. -/
noncomputable abbrev meaning (model : Model) {header : ProtocolHeader}
    (protocol : Var typed.protocols header) :=
  (typed.program.protocolTable model Identities.written).get protocol []

abbrev both : Side := fun _ => true
abbrev prover : Side := fun role => Nat.beq role 0
abbrev verifier : Side := fun role => Nat.beq role 1

/-- Both roles in the side: the element at the position reaches the verifier. -/
theorem guarded_reads (model : Model) :
    meaning model guarded both (.cons ([5, 7, 9] : List Nat) (.cons (1 : Nat) .nil)) =
      .done (.cons (7 : Nat) .nil) := kernel_rfl%

/-- A position beyond the length stops at the guard, with the guard's reason. -/
theorem guarded_beyond (model : Model) :
    meaning model guarded both (.cons ([5, 7, 9] : List Nat) (.cons (3 : Nat) .nil)) =
      .halt .reject := kernel_rfl%

/-- The prover alone stops at its guard as well. -/
theorem prover_beyond (model : Model) :
    meaning model guarded prover (.cons ([5, 7, 9] : List Nat) (.cons (3 : Nat) .nil)) =
      .halt .reject := kernel_rfl%

/-- The verifier reads its own sequence at the position that the prover guarded and sent,
after its own guard. -/
theorem relayed_reads (model : Model) :
    meaning model relayed both
        (.cons ([5, 7, 9] : List Nat) (.cons ([2, 4, 6] : List Nat) (.cons (2 : Nat) .nil))) =
      .done (.cons (6 : Nat) .nil) := kernel_rfl%

/-- A position that the prover's guard admits and the verifier's sequence does not have
stops at the verifier's guard. -/
theorem relayed_short (model : Model) :
    meaning model relayed both
        (.cons ([5, 7, 9] : List Nat) (.cons ([2] : List Nat) (.cons (2 : Nat) .nil))) =
      .halt .reject := kernel_rfl%

/-- The region of `true` reads; the region of `false` returns 0. -/
theorem chosen_reads (model : Model) :
    meaning model chosen both (.cons ([5, 7, 9] : List Nat) (.cons (2 : Nat) .nil)) =
      .done (.cons (9 : Nat) .nil) := kernel_rfl%

theorem chosen_beyond (model : Model) :
    meaning model chosen both (.cons ([5, 7, 9] : List Nat) (.cons (3 : Nat) .nil)) =
      .done (.cons (0 : Nat) .nil) := kernel_rfl%

/-- Four iterations: the verifier collects the four elements. -/
theorem counted_collects (model : Model) :
    meaning model counted both (.cons ⟨[5, 7, 9, 11], rfl⟩ .nil) =
      .done (.cons ⟨[5, 7, 9, 11], rfl⟩ .nil) := kernel_rfl%

/-- As many iterations as the sequence has elements. -/
theorem ranged_collects (model : Model) :
    meaning model ranged both (.cons ([5, 7, 9] : List Nat) .nil) =
      .done (.cons ([5, 7, 9] : List Nat) .nil) := kernel_rfl%

/-- No iteration: the region, whose read nothing justifies, does not run. -/
theorem never_collects (model : Model) :
    meaning model never both (.cons ⟨[], rfl⟩ .nil) = .done (.cons ⟨[], rfl⟩ .nil) :=
  kernel_rfl%

theorem nested_reads (model : Model) :
    meaning model nested both (.cons ([5, 7, 9] : List Nat) (.cons (0 : Nat) .nil)) =
      .done (.cons (5 : Nat) .nil) := kernel_rfl%

theorem armed_reads (model : Model) :
    meaning model armed both
        (.cons ([5, 7, 9] : List Nat) (.cons (1 : Nat) (.cons (⟨0, by decide⟩ : Fin 2) .nil))) =
      .done (.cons (7 : Nat) .nil) := kernel_rfl%

/-- The applied protocol runs with the roles exchanged. -/
theorem swapped_reads (model : Model) :
    meaning model swapped both (.cons ([5, 7, 9] : List Nat) (.cons (1 : Nat) .nil)) =
      .done (.cons (7 : Nat) .nil) := kernel_rfl%

/-- The result of the `choose` is 1 or 0, below 2. -/
theorem joined_converts (model : Model) :
    meaning model joined both (.cons true .nil) =
      .done (.cons (⟨1, by decide⟩ : Fin 2) .nil) := kernel_rfl%

theorem blocked_converts (model : Model) :
    meaning model blocked both (.cons (0 : Nat) .nil) =
      .done (.cons (⟨3, by decide⟩ : Fin 4) .nil) := kernel_rfl%

/-! ## Role programs -/

/-- The value of a result that is known to be one. -/
def okValue {ε α : Type} (result : Except ε α) (accepted : result.isOk = true) : α :=
  match result, accepted with
  | .ok value, _ => value

theorem okValue_eq {ε α : Type} (result : Except ε α) (accepted : result.isOk = true) :
    result = .ok (okValue result accepted) := by
  match result, accepted with
  | .ok value, _ => rfl

kernel_refl projects : (projectProtocols typed.program.protocols).isOk equals true

/-- The role programs of the package. -/
noncomputable def projected :
    Projected (typed.table.map (·.signature)) typed.functions typed.protocols :=
  okValue (projectProtocols typed.program.protocols) projects

theorem projected_eq : projectProtocols typed.program.protocols = .ok projected :=
  okValue_eq (projectProtocols typed.program.protocols) projects

/-- For every model that satisfies the domain laws, the program of every role of every
protocol of the package never stops `undefined`, under any path and on any arguments,
whatever the replies of its effects. -/
theorem role_never_undefined (model : Model)
    (laws : model.DomainLaws (typed.table.map (·.signature))) (identities : Identities)
    {header : ProtocolHeader} (callee : Var typed.protocols header) (role : Nat)
    (program : Var projected.headers (roleHeader role header))
    (named : projected.callees.find callee role = some program) (path : List Nat)
    (arguments : Values model.Value (roleHeader role header).inputs) :
    NeverStops .undefined
      ((projected.programs.table model (typed.program.functionTable model) identities).get
        program path arguments) :=
  Program.role_never_undefined laws typed.program justified identities projected projected_eq
    callee role program named path arguments

-- The verifier of `relayed` has a program, to which the statement applies.
kernel_refl relayed_verifier : (projected.callees.find relayed 1).isSome equals true

/-! ## Protocols that do not pass -/

raw_package unguarded from file "fixtures/role-facts-unjustified.json"

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

-- The first application of each protocol that is not justified: the protocol's number, the
-- path of the instruction and the requirement it does not meet. A region of a `choose` on
-- a condition has the number 0 for `false` and 1 for `true`; a region of a local operation
-- inside an `at` is numbered under the instruction of the `at`.
kernel_refl first_unjustified :
    unguardedTyped.program.protocols.unjustified equals
      [(0, ⟨[0], .position⟩), (1, ⟨[4], .position⟩), (2, ⟨[3, 0, 0], .position⟩),
       (3, ⟨[0, 0, 0], .position⟩), (4, ⟨[8, 0, 0], .position⟩), (5, ⟨[3], .domain⟩),
       (6, ⟨[0], .domain⟩), (7, ⟨[2, 1, 0], .position⟩), (8, ⟨[1, 0, 0], .position⟩),
       (9, ⟨[1], .bound⟩)]

abbrev unguardedRead :
    Var unguardedTyped.protocols
      ⟨2, [⟨.seq .nat none, 0⟩, ⟨.nat, 0⟩], [⟨.nat, 1⟩], .none, false⟩ :=
  ⟨9, rfl⟩
abbrev trusted :
    Var unguardedTyped.protocols
      ⟨2, [⟨.seq .nat none, 0⟩, ⟨.seq .nat none, 1⟩, ⟨.nat, 0⟩], [⟨.nat, 1⟩], .none, false⟩ :=
  ⟨8, rfl⟩

/-- The meaning of a protocol of the second package for a side. -/
noncomputable abbrev unguardedMeaning (model : Model) {header : ProtocolHeader}
    (protocol : Var unguardedTyped.protocols header) :=
  (unguardedTyped.program.protocolTable model Identities.written).get protocol []

/-- Without the guard a position beyond the length stops `undefined`. -/
theorem unguarded_stops (model : Model) :
    unguardedMeaning model unguardedRead both
        (.cons ([5, 7, 9] : List Nat) (.cons (3 : Nat) .nil)) =
      .halt .undefined := kernel_rfl%

/-- The prover's guard says nothing of the verifier's sequence: a position that the prover
admits stops the verifier `undefined`. -/
theorem trusted_stops (model : Model) :
    unguardedMeaning model trusted both
        (.cons ([5, 7, 9] : List Nat) (.cons ([2] : List Nat) (.cons (2 : Nat) .nil))) =
      .halt .undefined := kernel_rfl%

#print axioms never_undefined
#print axioms guarded_defined
#print axioms relayed_defined
#print axioms inverse_defined
#print axioms joined_defined
#print axioms unit_guarded_defined
#print axioms role_never_undefined
#print axioms guarded_reads
#print axioms relayed_reads
#print axioms counted_collects
#print axioms ranged_collects
#print axioms justified
#print axioms first_unjustified
#print axioms trusted_stops
#print axioms reprinted_eq

end RoleFacts
