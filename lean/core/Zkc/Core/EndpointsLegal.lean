module

public import Zkc.Core.EndpointsProgram
public import Zkc.Core.ProjectProgramMeaning

public section

/-! The restriction law and the endpoint lemma for every program.

Every program has the shape that the restriction law needs (`protocols_enclosed`, in
`Zkc.Core.Idle`), so the restriction law (`program_together`) and the endpoint lemma
(`program_endpoints_return`) hold for every program that `elaborate` accepts, without a
hypothesis about shape.

The restriction law is stated for listeners: a function of sites that says which of the two
sides hears the coins of each site (`Zkc.Core.Endpoints`). Every protocol of a program has
such listeners for two sides that each hold at most one of its roles
(`Protocols.entry_listened`, in `Zkc.Core.EndpointsListeners`), because the sites of a
well-formed definition are pairwise different. The endpoint lemma is about two sides that
each look like one role, so it takes those listeners and has no hypothesis about them.

Both take the condition that the functions given perform no effect (`QuietTable`), which the
functions of every program satisfy (`Functions.table_quiet`): a function that drew would
announce a coin at a site of its own, where no receiver hears it.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

section Programs

variable {model : Model} {typeTable : TypeTable} {operations : List OperationSignature}
  {functions : List FunctionHeader}

/-- The restriction law for every protocol of every program: no hypothesis about shape. For
given listeners, it holds under every path and for every two disjoint sides at which the
listeners are those of the protocol (`Protocols.listens`). -/
theorem program_together (sampler : Sampler model) (listeners : Listeners)
    (functionTable : FunctionTable model functions) (quiet : QuietTable functionTable)
    (identities : Identities) {protocols : List ProtocolHeader}
    (program : Protocols typeTable operations functions protocols) :
    TableTogether sampler listeners (program.listens listeners identities)
      (program.table model functionTable identities) :=
  protocols_together functionTable quiet identities program (protocols_enclosed program)

/-- The endpoint lemma for a program: for every protocol of a program that projection
accepts and two disjoint sides that each look like one role of the protocol, when the
grouped run for their union returns, the two role programs, applications kept as calls,
run against each other on the inputs each role holds from the start of a run (no message in
transit, no coin announced, none heard), return the outputs each role holds. The program is
any typed program: its definitions are without a residual violation. -/
theorem program_endpoints_return (sampler : Sampler model)
    (functionTable : FunctionTable model functions) (quiet : QuietTable functionTable)
    (identities : Identities)
    {protocols : List ProtocolHeader} (program : Protocols typeTable operations functions protocols)
    (projected : Projected operations functions protocols)
    (projects : projectProtocols program = .ok projected) {header : ProtocolHeader}
    (entry : Var protocols header) (first second : Side) (disjoint : first.Disjoint second)
    (firstRole secondRole : Nat) (onlyFirst : first.Only firstRole header.roles)
    (onlySecond : second.Only secondRole header.roles)
    (firstInside : first firstRole = true) (secondInside : second secondRole = true)
    (firstProgram : Var projected.headers (roleHeader firstRole header))
    (secondProgram : Var projected.headers (roleHeader secondRole header))
    (namedFirst : projected.callees.find entry firstRole = some firstProgram)
    (namedSecond : projected.callees.find entry secondRole = some secondProgram)
    (path : List Nat) (inputs : Values (SideValue model (first.union second)) header.inputs)
    (outputs : Values (SideValue model (first.union second)) header.outputs) (asked : Asked)
    (returns : ReturnsAlone sampler
      ((program.table model functionTable identities).get entry path (first.union second) inputs)
      asked outputs) :
    ReturnTogether sampler
      ((projected.programs.table model functionTable identities).get firstProgram path
        (ownValues model first firstRole firstInside header.inputs
          (leftValues model first second inputs)))
      ((projected.programs.table model functionTable identities).get secondProgram path
        (ownValues model second secondRole secondInside header.inputs
          (rightValues model first second inputs)))
      Mail.empty Board.empty Heard.start Heard.start asked
      (ownValues model first firstRole firstInside header.outputs
        (leftValues model first second outputs))
      (ownValues model second secondRole secondInside header.outputs
        (rightValues model first second outputs)) := by
  have programs := projectProtocols_sound (model := model) (functionTable := functionTable)
    identities program projected projects
  rw [programs.program entry firstRole firstProgram namedFirst path first onlyFirst firstInside,
    programs.program entry secondRole secondProgram namedSecond path second onlySecond
      secondInside]
  refine ((program_together sampler (program.listeners entry path first second) functionTable
    quiet identities program).together entry path first second disjoint
    (Protocols.entry_listened identities program entry path first second onlyFirst.atMostOne
      onlySecond.atMostOne) inputs).run PIR.Process.done _ _ Board.empty Heard.start Heard.start
    asked outputs _ _ (Listeners.heardAll_start _) ?_ ?_
  · intro value later laterFirst laterSecond counted _ returned
    cases returned
    exact .done _ _ _ _ _ _ _
  · rw [PIR.Process.bind_done]
    exact returns

end Programs

end Zkc.Core
