module

public import Zkc.Core.ProtocolFactsSound
public import Zkc.Core.ProjectProgramMeaning

public section

/-! The role programs of a program that passes the check of facts never stop `undefined`.

Projection gives every role of a protocol its program, and the program has the process of
the protocol for a side with that role alone (`projectProtocols_sound`). The protocol never
stops `undefined` for that side, whatever the replies of its effects, so the role program
does not either: on the values that the role holds of any values of such a side, and, since
every tuple of values of the role is that of a side with the role alone, on any arguments.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

variable {model : Model}

section Programs

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader}

/-- For a program all of whose functions and protocols pass the check of facts and a model
that satisfies the domain laws: the program of a role of a protocol never stops
`undefined`, on the values that the role holds of any values of a side whose only member
among the protocol's roles is that role. -/
theorem Program.roles_never_undefined (laws : model.DomainLaws operations)
    {typeTable : TypeTable} (program : Program typeTable operations functions protocols)
    (passes : program.justified = true) (identities : Identities)
    (projected : Projected operations functions protocols)
    (projects : projectProtocols program.protocols = .ok projected) {header : ProtocolHeader}
    (callee : Var protocols header) (role : Nat)
    (calling : Var projected.headers (roleHeader role header))
    (named : projected.callees.find callee role = some calling) (path : List Nat) (side : Side)
    (only : side.Only role header.roles) (inside : side role = true)
    (arguments : Values (SideValue model side) header.inputs) :
    NeverStops .undefined
      ((projected.programs.table model (program.functionTable model) identities).get calling path
        (ownValues model side role inside header.inputs arguments)) := by
  rw [(projectProtocols_sound (functionTable := program.functionTable model) identities
    program.protocols projected projects).program callee role calling named path side only inside
    arguments]
  exact NeverStops.bind
    (Program.protocols_never_undefined laws program passes identities callee path side arguments)
    fun _ => NeverStops.done _ _

/-- For a program all of whose functions and protocols pass the check of facts and a model
that satisfies the domain laws: the program of a role of a protocol never stops
`undefined`, under any path and on any arguments, whatever the replies of its effects. -/
theorem Program.role_never_undefined (laws : model.DomainLaws operations)
    {typeTable : TypeTable} (program : Program typeTable operations functions protocols)
    (passes : program.justified = true) (identities : Identities)
    (projected : Projected operations functions protocols)
    (projects : projectProtocols program.protocols = .ok projected) {header : ProtocolHeader}
    (callee : Var protocols header) (role : Nat)
    (calling : Var projected.headers (roleHeader role header))
    (named : projected.callees.find callee role = some calling) (path : List Nat)
    (arguments : Values model.Value (roleHeader role header).inputs) :
    NeverStops .undefined
      ((projected.programs.table model (program.functionTable model) identities).get calling path
        arguments) := by
  have held := Program.roles_never_undefined laws program passes identities projected projects
    callee role calling named path (single role) (Side.only_single role header.roles)
    (Side.single_inside role) (onlyValues model role header.inputs arguments)
  rw [ownValues_onlyValues] at held
  exact held

end Programs

end Zkc.Core
