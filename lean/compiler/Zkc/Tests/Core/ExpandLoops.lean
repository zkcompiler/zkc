import Zkc.Tests.Core.Roles

/-! Expansion and projection evaluated by the kernel on the Loops fixture.

`fixtures/loops-expanded.json`, `loops-roles.json` and `loops-calls.json` are the outputs of
the compiled tool's `expand`, `project` and `calls` commands. The kernel evaluates the same
functions on the typed package and finds the same raw syntax: the expanded entry, in which
a role collects in a loop of its local code, and the role programs, in which the loop is
the role's own instruction. -/

set_option autoImplicit false

open Zkc.Source Zkc.Core

namespace ExpandLoops

raw_package raw from file "fixtures/loops.json"
raw_package expandedByTool from file "fixtures/loops-expanded.json"
raw_roles rolesByTool from file "fixtures/loops-roles.json"
raw_roles callsByTool from file "fixtures/loops-calls.json"

kernel_refl elaborates : (elaborate raw).isOk equals true

noncomputable def typed : Typed := Typed.ofRaw raw elaborates

kernel_refl expanded_eq : typed.expandedProtocols equals Except.ok expandedByTool.protocols
kernel_refl expanded_written : (elaborateWritten expandedByTool).isOk equals true
kernel_refl roles_eq : typed.entryRoles equals Except.ok rolesByTool
kernel_refl calls_eq : typed.calledRoles equals Except.ok callsByTool

#print axioms expanded_eq
#print axioms roles_eq
#print axioms calls_eq

end ExpandLoops
