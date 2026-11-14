module

public import Zkc.Core.Entry
public import Zkc.Core.Idle
public import Zkc.Core.EndpointsListeners

public section

/-! The restriction law for definitions and programs, and the endpoint lemma.

`protocols_together`: for the protocols of a program whose definitions have the shape of
`protocolsEnclosed` (`Zkc.Core.Idle`) and whose functions perform no effect, the meaning of
every protocol for a union of two disjoint sides and its meanings for the two sides are
`Together`, under every path and for every two sides at which the listeners are those of the
protocol (`Protocols.listens`), and every protocol does nothing for a side without any of
its roles.

`endpoints_return` is the endpoint lemma: when the grouped run of a protocol for the union
of two disjoint sides returns, the programs of two roles, one the only role of each side
among the roles of the protocol, run against each other on the inputs each role holds,
return the outputs each role holds. It composes the restriction law with the projection
theorem for a side that looks like one role. The run of the two starts from a board and
counts at which each side has heard every coin of the sites where it hears.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

section Program

variable {model : Model} {sampler : Sampler model} {listeners : Listeners} {typeTable : TypeTable}
  {operations : List OperationSignature} {functions : List FunctionHeader}
  (functionTable : FunctionTable model functions)

variable {protocols : List ProtocolHeader} {table : ProtocolTable model protocols}
  {listens : ListenTable protocols}

/-- The restriction law for a definition. -/
theorem definition_together (quiet : QuietTable functionTable)
    (sound : TableTogether sampler listeners listens table) {header : ProtocolHeader}
    (definition : ProtocolDefinition operations functions protocols header)
    (enclosed : regionEnclosed definition.body) (identity : Nat) (path : List Nat)
    (first second : Side) (disjoint : first.Disjoint second)
    (heard : regionListens listeners (ownSites identity path) listens first second
      definition.body)
    (arguments : Values (SideValue model (first.union second)) header.inputs) :
    Together sampler listeners (leftValues model first second) (rightValues model first second)
      (definition.meaning model functionTable table identity path (first.union second) arguments)
      (definition.meaning model functionTable table identity path first
        (leftValues model first second arguments))
      (definition.meaning model functionTable table identity path second
        (rightValues model first second arguments)) :=
  region_together quiet sound disjoint definition.body enclosed heard _ _ _
    (Restricts.ofValues arguments) (Restricts.ofValues arguments)

/-- The restriction law for every protocol of a program whose functions perform no effect. -/
theorem protocols_together (quiet : QuietTable functionTable) (identities : Identities) :
    ∀ {protocols : List ProtocolHeader}
      (program : Protocols typeTable operations functions protocols), protocolsEnclosed program →
        TableTogether sampler listeners (program.listens listeners identities)
          (program.table model functionTable identities)
  | _, .nil, _ => ⟨fun callee => callee.elimNil, fun callee => callee.elimNil⟩
  | _, .snoc earlier definition _, enclosed => by
      have sound : TableTogether sampler listeners (earlier.listens listeners identities)
          (earlier.table model functionTable identities) :=
        protocols_together quiet identities earlier enclosed.1
      refine ⟨fun {other} callee => ?_, fun {other} callee => ?_⟩
      · cases callee with
        | here =>
            intro path first second disjoint heard arguments
            exact definition_together functionTable quiet sound definition enclosed.2.1 _ path
              first second disjoint heard arguments
        | there callee => exact sound.together callee
      · cases callee with
        | here =>
            intro path side absent arguments
            exact definition_idle functionTable sound.idle definition enclosed.2.2 _ path side
              absent arguments
        | there callee => exact sound.idle callee

end Program

/-! ## The endpoint lemma -/

section Endpoints

variable {model : Model} {sampler : Sampler model} {listeners : Listeners}
  {operations : List OperationSignature}
  {functions : List FunctionHeader} {protocols : List ProtocolHeader} {programs : List RoleHeader}
  {functionTable : FunctionTable model functions} {table : ProtocolTable model protocols}
  {listens : ListenTable protocols}
  {called : RoleTable model programs} {callees : ProjectedCallees protocols programs}

/-- The endpoint lemma. `first` and `second` are disjoint sides whose only members among
the roles of the protocol are `firstRole` and `secondRole`, and the listeners are those of
the definition for the two sides. When the run of the grouped meaning for their union
returns, the programs of the two roles, run against each other on the inputs each holds,
with the same sampler and counters, return the outputs each holds. The grouped run starts
from any counters; the composed run starts from the same counters and from any board and
counts at which each side has heard every coin of the sites where it hears. -/
theorem endpoints_return (calleePrograms : CalleesSound model table called callees)
    (quiet : QuietTable functionTable)
    (sound : TableTogether sampler listeners listens table) {header : ProtocolHeader}
    (definition : ProtocolDefinition operations functions protocols header)
    (enclosed : regionEnclosed definition.body) (identity : Nat) (path : List Nat)
    (first second : Side) (disjoint : first.Disjoint second) (firstRole secondRole : Nat)
    (onlyFirst : first.Only firstRole header.roles)
    (onlySecond : second.Only secondRole header.roles)
    (firstInside : first firstRole = true) (secondInside : second secondRole = true)
    (heard : regionListens listeners (ownSites identity path) listens first second
      definition.body)
    (firstProgram : RoleProgram operations functions programs (roleHeader firstRole header))
    (secondProgram : RoleProgram operations functions programs (roleHeader secondRole header))
    (projectsFirst : projectProtocol firstRole callees definition = .ok firstProgram)
    (projectsSecond : projectProtocol secondRole callees definition = .ok secondProgram)
    (inputs : Values (SideValue model (first.union second)) header.inputs)
    (outputs : Values (SideValue model (first.union second)) header.outputs) (board : Board model)
    (heardFirst heardSecond : Heard) (heardAll : listeners.HeardAll board heardFirst heardSecond)
    (asked : Asked)
    (returns : ReturnsAlone sampler
      (definition.meaning model functionTable table identity path (first.union second) inputs)
      asked outputs) :
    ReturnTogether sampler
      (firstProgram.body.denote (roleMeaning model functionTable called (ownSites identity path))
        (Environment.ofValues
          (ownValues model first firstRole firstInside header.inputs
            (leftValues model first second inputs))))
      (secondProgram.body.denote (roleMeaning model functionTable called (ownSites identity path))
        (Environment.ofValues
          (ownValues model second secondRole secondInside header.inputs
            (rightValues model first second inputs))))
      Mail.empty board heardFirst heardSecond asked
      (ownValues model first firstRole firstInside header.outputs
        (leftValues model first second outputs))
      (ownValues model second secondRole secondInside header.outputs
        (rightValues model first second outputs)) := by
  rw [projectProtocol_meaning calleePrograms definition firstProgram projectsFirst identity path
      first onlyFirst firstInside,
    projectProtocol_meaning calleePrograms definition secondProgram projectsSecond identity path
      second onlySecond secondInside]
  refine (definition_together functionTable quiet sound definition enclosed identity path first
    second disjoint heard inputs).run PIR.Process.done _ _ board heardFirst heardSecond asked
    outputs _ _ heardAll ?_ ?_
  · intro value later laterFirst laterSecond counted _ returned
    cases returned
    exact .done _ _ _ _ _ _ _
  · rw [PIR.Process.bind_done]
    exact returns

/-- The two sides of a protocol of two roles: role 0 alone and role 1 alone. -/
theorem single_disjoint : (single 0).Disjoint (single 1) := by
  intro role
  cases role with
  | zero => rfl
  | succ role => rfl

/-- The endpoint lemma for the two roles of a protocol of two roles, from the start of a
run: no coin announced, none heard, no site asked. -/
theorem endpoints_return_two (calleePrograms : CalleesSound model table called callees)
    (quiet : QuietTable functionTable)
    (sound : TableTogether sampler listeners listens table) {header : ProtocolHeader}
    (definition : ProtocolDefinition operations functions protocols header)
    (enclosed : regionEnclosed definition.body) (identity : Nat) (path : List Nat)
    (heard : regionListens listeners (ownSites identity path) listens (single 0) (single 1)
      definition.body)
    (firstProgram : RoleProgram operations functions programs (roleHeader 0 header))
    (secondProgram : RoleProgram operations functions programs (roleHeader 1 header))
    (projectsFirst : projectProtocol 0 callees definition = .ok firstProgram)
    (projectsSecond : projectProtocol 1 callees definition = .ok secondProgram)
    (inputs : Values (SideValue model ((single 0).union (single 1))) header.inputs)
    (outputs : Values (SideValue model ((single 0).union (single 1))) header.outputs)
    (returns : ReturnsAlone sampler
      (definition.meaning model functionTable table identity path ((single 0).union (single 1))
        inputs)
      (fun _ => 0) outputs) :
    ReturnTogether sampler
      (firstProgram.body.denote (roleMeaning model functionTable called (ownSites identity path))
        (Environment.ofValues
          (ownValues model (single 0) 0 (Side.single_inside 0) header.inputs
            (leftValues model (single 0) (single 1) inputs))))
      (secondProgram.body.denote (roleMeaning model functionTable called (ownSites identity path))
        (Environment.ofValues
          (ownValues model (single 1) 1 (Side.single_inside 1) header.inputs
            (rightValues model (single 0) (single 1) inputs))))
      Mail.empty Board.empty Heard.start Heard.start (fun _ => 0)
      (ownValues model (single 0) 0 (Side.single_inside 0) header.outputs
        (leftValues model (single 0) (single 1) outputs))
      (ownValues model (single 1) 1 (Side.single_inside 1) header.outputs
        (rightValues model (single 0) (single 1) outputs)) :=
  endpoints_return calleePrograms quiet sound definition enclosed identity path (single 0)
    (single 1) single_disjoint 0 1 (Side.only_single 0 header.roles)
    (Side.only_single 1 header.roles) (Side.single_inside 0) (Side.single_inside 1) heard
    firstProgram secondProgram projectsFirst projectsSecond inputs outputs Board.empty Heard.start
    Heard.start listeners.heardAll_start (fun _ => 0) returns

end Endpoints

end Zkc.Core
