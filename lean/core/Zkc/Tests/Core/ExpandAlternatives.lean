import Zkc.Tests.Core.Roles

/-! Expansion and projection evaluated by the kernel on the Alternatives fixture.

`fixtures/alternatives-expanded.json`, `alternatives-roles.json` and
`alternatives-calls.json` are the outputs of the compiled tool's `expand`, `project` and
`calls` commands. The kernel evaluates the same functions on the typed package and finds
the same raw syntax: the expanded entry, in which the choice on the variant has the roles
of the application, and the role programs, in which the choice of each role takes the
role's own payload in the region of each alternative. -/

set_option autoImplicit false

open Zkc.Source Zkc.Core

namespace ExpandAlternatives

raw_package raw from file "fixtures/alternatives.json"
raw_package expandedByTool from file "fixtures/alternatives-expanded.json"
raw_roles rolesByTool from file "fixtures/alternatives-roles.json"
raw_roles callsByTool from file "fixtures/alternatives-calls.json"

kernel_refl elaborates : (elaborate raw).isOk equals true

noncomputable def typed : Typed := Typed.ofRaw raw elaborates

kernel_refl expanded_eq : typed.expandedProtocols equals Except.ok expandedByTool.protocols
kernel_refl expanded_written : (elaborateWritten expandedByTool).isOk equals true
kernel_refl roles_eq : typed.entryRoles equals Except.ok rolesByTool
kernel_refl calls_eq : typed.calledRoles equals Except.ok callsByTool

-- The expanded entry: the applied choice with the roles exchanged, so that the first
-- payload of a region is held by the role that runs the callee's first role.
kernel_refl expanded_body : (expandedByTool.protocols.map (·.body)) equals
  [.step (.choose [1, 0] [1, 0] (.alternative 0 []) [] [⟨.nat, 0⟩, ⟨.nat, 1⟩]
      (.arm
        (.step (.at 1 (.builtin .natAdd [0, 0]))
          (.step (.exchange 1 0 0 2)
            (.step (.at 0 (.builtin .natAdd [3, 1])) (.ret [4, 2]))))
        (.arm
          (.step (.at 1 (.conditional 0 [] [.nat]
              (.step (.literal (.nat 1)) (.ret [0])) (.step (.literal (.nat 0)) (.ret [0]))))
            (.step (.exchange 1 0 1 2)
              (.step (.at 0 (.conditional 1 [] [.nat]
                  (.step (.literal (.nat 10)) (.ret [0]))
                  (.step (.literal (.nat 20)) (.ret [0]))))
                (.step (.at 0 (.builtin .natAdd [3, 4])) (.ret [5, 2])))))
          .none)))
    (.ret [2, 3])]

-- The program of the first role of the entry, which runs the callee's second role: it
-- chooses on its own copy, and the first value of each region is its own payload.
kernel_refl first_program : (rolesByTool.head?.map fun program =>
    (program.inputs, program.outputs, program.body)) equals
  some ([.variant 0 []], [.nat],
    .step (.choose (.alternative 0 []) 0 [] [.nat]
        (.arm
          (.step (.receive 0 .nat) (.step (.perform (.builtin .natAdd [1, 0])) (.ret [2])))
          (.arm
            (.step (.receive 1 .nat)
              (.step (.perform (.conditional 0 [] [.nat]
                  (.step (.literal (.nat 10)) (.ret [0]))
                  (.step (.literal (.nat 20)) (.ret [0]))))
                (.step (.perform (.builtin .natAdd [1, 2])) (.ret [3]))))
            .none)))
      (.ret [1]))

#print axioms expanded_eq
#print axioms roles_eq
#print axioms calls_eq

end ExpandAlternatives
