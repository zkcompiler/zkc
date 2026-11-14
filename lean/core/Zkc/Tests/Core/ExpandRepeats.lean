import Zkc.Tests.Core.Roles

/-! Expansion and projection evaluated by the kernel on the Repeats fixtures.

`fixtures/repeats-expanded.json`, `repeats-roles.json` and `repeats-calls.json`, and the
same three of `repeats-static`, are the outputs of the compiled tool's `expand`, `project`
and `calls` commands. The kernel evaluates the same functions on the typed packages and
finds the same raw syntax: the expanded entry, and the role programs, in which the loop of
each role takes the role's own iteration number before its carried values, and its own
count when the count is a value, and collects the values that the role holds. The entry of
`repeats-static` applies a protocol whose loop collects, with the roles exchanged. -/

set_option autoImplicit false

open Zkc.Source Zkc.Core

namespace ExpandRepeats

raw_package raw from file "fixtures/repeats.json"
raw_package expandedByTool from file "fixtures/repeats-expanded.json"
raw_roles rolesByTool from file "fixtures/repeats-roles.json"
raw_roles callsByTool from file "fixtures/repeats-calls.json"

kernel_refl elaborates : (elaborate raw).isOk equals true

noncomputable def typed : Typed := Typed.ofRaw raw elaborates

kernel_refl expanded_eq : typed.expandedProtocols equals Except.ok expandedByTool.protocols
kernel_refl expanded_written : (elaborateWritten expandedByTool).isOk equals true
kernel_refl roles_eq : typed.entryRoles equals Except.ok rolesByTool
kernel_refl calls_eq : typed.calledRoles equals Except.ok callsByTool

-- The program of the first role of the entry: its loop reads its iteration number, the
-- first value of the region.
kernel_refl left_program : (rolesByTool.head?.map (·.body)) equals
  some (.step (.perform (.literal (.nat 0)))
    (.step (.repeat (.runtime 8 0) [1] [] [] (.step (.perform (.builtin .natAdd [1, 0])) (.ret [2])))
      (.ret [2])))

#print axioms expanded_eq
#print axioms roles_eq
#print axioms calls_eq

/-! ## A count of the operation -/

namespace Fixed

raw_package raw from file "fixtures/repeats-static.json"
raw_package expandedByTool from file "fixtures/repeats-static-expanded.json"
raw_roles rolesByTool from file "fixtures/repeats-static-roles.json"
raw_roles callsByTool from file "fixtures/repeats-static-calls.json"

kernel_refl elaborates : (elaborate raw).isOk equals true

noncomputable def typed : Typed := Typed.ofRaw raw elaborates

kernel_refl expanded_eq : typed.expandedProtocols equals Except.ok expandedByTool.protocols
kernel_refl expanded_written : (elaborateWritten expandedByTool).isOk equals true
kernel_refl roles_eq : typed.entryRoles equals Except.ok rolesByTool
kernel_refl calls_eq : typed.calledRoles equals Except.ok callsByTool

-- The expanded entry: the applied loop with the roles exchanged, so that the collected
-- values and the carried values are held by the roles that run the callee's.
kernel_refl expanded_body : (expandedByTool.protocols.map (·.body)) equals
  [.step (.at 1 (.literal (.nat 0)))
    (.step (.at 0 (.literal (.nat 1)))
      (.step (.repeat [1, 0] (.static 3) [0, 1] [] [⟨.nat, 1⟩, ⟨.nat, 0⟩]
          (.step (.at 1 (.builtin .natAdd [2, 0]))
            (.step (.at 0 (.builtin .natAdd [3, 1]))
              (.step (.at 0 (.builtin .natMul [1, 1])) (.ret [4, 6, 4, 5])))))
        (.ret [2, 3, 4, 5])))]

-- The program of the first role of the entry: its loop has the count and no count operand,
-- collects the square of its iteration number, and returns the sequence before the sum.
kernel_refl left_program : (rolesByTool.head?.map (·.body)) equals
  some (.step (.perform (.literal (.nat 1)))
    (.step (.repeat (.static 3) [0] [] [.nat]
        (.step (.perform (.builtin .natAdd [1, 0]))
          (.step (.perform (.builtin .natMul [0, 0])) (.ret [3, 2]))))
      (.ret [1, 2])))

#print axioms expanded_eq
#print axioms roles_eq

end Fixed

end ExpandRepeats
