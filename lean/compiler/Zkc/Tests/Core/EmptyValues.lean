import Zkc.Tests.Core.Check
import Zkc.Tests.Core.Reflexivity
import Zkc.Core.RoundTrip
import Zkc.Core.ProtocolFactsProject

/-! Kernel checks for regions in which a value of a type without a value is in scope.

- `fixtures/empty-values.json` declares a record with a field `fin 0`, a variant whose
  first alternative is `fin 0`, and a variant without alternatives. Its definitions read
  `xs[0]` of an unsized sequence without a guard, and pass the check of facts:
  - `absent_index`: a function with an input `fin 0`; `empty_field`: with an input of the
    record;
  - `empty_arm`: the read in the region of a `match` for the alternative `fin 0`;
  - `after_call`: the read after a call of `halts`, a function known by its header whose
    output is `fin 0`; `after_block`: after a block that returns that output;
  - `one_holder`: a protocol whose first role holds a value of the variant without
    alternatives, and reads;
  - `empty_case`: a `choose` on the first variant, with the read of a participant in the
    region of the alternative `fin 0`.
  For every model that satisfies the domain laws, every function and every protocol, for
  every side, never stops `undefined`.
- `fixtures/empty-values-unjustified.json` has the same reads where a value exists:
  `present_index` with an input `fin 1`; `populated_arm` and `populated_case` with the read
  in the region of the alternative `nat`; `other_holder`, in which the second role, which
  holds no value of the empty variant, reads as the first one does. The kernel finds each
  read, and in `other_holder` the read of the second role only.
-/

set_option autoImplicit false

open Zkc.Source Zkc.Core

namespace EmptyValues

raw_package raw from file "fixtures/empty-values.json"

kernel_refl accepted : (elaborateWritten raw).isOk equals true
kernel_refl elaborates : (elaborate raw).isOk equals true

noncomputable def elaborated : Typed := Typed.ofRaw raw elaborates

typed_literal typed := elaborated

kernel_refl elaborate_eq : elaborate raw equals Except.ok typed
kernel_refl unelaborate_eq : unelaborate typed equals raw

-- Every function and every protocol passes the check of facts.
kernel_refl justified : typed.program.justified equals true
kernel_refl none_unjustified : typed.program.functions.unjustified equals []
kernel_refl no_protocol_unjustified : typed.program.protocols.unjustified equals []

/-- For every model that satisfies the domain laws, every function of the package never
stops `undefined`, on any arguments. -/
theorem never_undefined (model : Model) (laws : model.DomainLaws (typed.table.map (·.signature)))
    {header : FunctionHeader} (callee : Var typed.functions header)
    (arguments : Values model.Value header.inputs) :
    NeverStops .undefined ((typed.program.functionTable model).get callee arguments) :=
  Program.never_undefined laws typed.program justified callee arguments

/-- For every model that satisfies the domain laws and every side, every protocol of the
package never stops `undefined`, with any identities, under any path and on any values. -/
theorem protocols_never_undefined (model : Model)
    (laws : model.DomainLaws (typed.table.map (·.signature))) (identities : Identities)
    {header : ProtocolHeader} (callee : Var typed.protocols header) (path : List Nat)
    (side : Side) (arguments : Values (SideValue model side) header.inputs) :
    NeverStops .undefined
      ((typed.program.protocolTable model identities).get callee path side arguments) :=
  Program.protocols_never_undefined laws typed.program justified identities callee path side
    arguments

abbrev afterCall : Var typed.functions ⟨[.seq .nat none], [.nat], false⟩ := ⟨2, rfl⟩
abbrev oneHolder :
    Var typed.protocols
      ⟨2, [⟨.variant 1 [], 0⟩, ⟨.seq .nat none, 0⟩, ⟨.seq .nat none, 1⟩], [⟨.nat, 0⟩], .none,
        false⟩ :=
  ⟨1, rfl⟩

/-- A read after a call whose output has no value never stops `undefined`, whatever the
sequence: the call does not return. -/
theorem afterCall_defined (model : Model)
    (laws : model.DomainLaws (typed.table.map (·.signature))) (xs : List Nat) :
    NeverStops .undefined
      ((typed.program.functionTable model).get afterCall (.cons xs .nil)) :=
  never_undefined model laws afterCall _

/-- The protocol whose first role holds a value of a variant without alternatives never
stops `undefined`, for any side. A side with the first role has no values to run on; for
a side without it, the first role's read is not part of the side's process. -/
theorem oneHolder_defined (model : Model)
    (laws : model.DomainLaws (typed.table.map (·.signature))) (identities : Identities)
    (path : List Nat) (side : Side)
    (arguments : Values (SideValue model side)
      [⟨.variant 1 [], 0⟩, ⟨.seq .nat none, 0⟩, ⟨.seq .nat none, 1⟩]) :
    NeverStops .undefined
      ((typed.program.protocolTable model identities).get oneHolder path side arguments) :=
  protocols_never_undefined model laws identities oneHolder path side arguments

/-! ## What is in scope -/

-- A type without a value in scope: the region never runs.
kernel_refl empty_input : ((Facts.start 2).inScope [.fin 0, .nat]).dead equals true
kernel_refl empty_variant : ((Facts.start 1).inScope [.variant 1 []]).dead equals true
kernel_refl empty_field : ((Facts.start 1).inScope [.record 0 .free [.fin 0, .nat]]).dead
    equals true
kernel_refl empty_elements : ((Facts.start 1).inScope [.seq (.fin 0) (some 2)]).dead equals true
-- Types with a value: a sequence of no element, a variant with one populated alternative.
kernel_refl populated_inputs :
    ((Facts.start 3).inScope
      [.fin 1, .seq (.fin 0) (some 0), .seq (.fin 0) none, .variant 0 [.fin 0, .nat]]).dead
      equals false
-- The holder of a value of a type without a value never runs; the other roles do.
kernel_refl holder_dead :
    (((RoleFacts.start 2).inScope [⟨.variant 1 [], 0⟩, ⟨.nat, 1⟩]).view 0).dead equals true
kernel_refl other_alive :
    (((RoleFacts.start 2).inScope [⟨.variant 1 [], 0⟩, ⟨.nat, 1⟩]).view 1).dead equals false
kernel_refl region_alive :
    ((RoleFacts.start 2).inScope [⟨.variant 1 [], 0⟩, ⟨.nat, 1⟩]).dead equals false

/-! ## The same reads where a value exists -/

raw_package unguarded from file "fixtures/empty-values-unjustified.json"

kernel_refl unguarded_accepted : (elaborateWritten unguarded).isOk equals true
kernel_refl unguarded_elaborates : (elaborate unguarded).isOk equals true

noncomputable def unguardedElaborated : Typed := Typed.ofRaw unguarded unguarded_elaborates

typed_literal unguardedTyped := unguardedElaborated

kernel_refl first_unjustified :
    unguardedTyped.program.functions.unjustified equals
      [(0, ⟨[1], .position⟩), (1, ⟨[0, 1, 1], .position⟩)]
kernel_refl first_protocol_unjustified :
    unguardedTyped.program.protocols.unjustified equals
      [(0, ⟨[3], .position⟩), (1, ⟨[0, 1, 1], .position⟩)]

#print axioms never_undefined
#print axioms protocols_never_undefined
#print axioms afterCall_defined
#print axioms oneHolder_defined
#print axioms Ty.populated_of_value

end EmptyValues
