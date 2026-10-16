import Zkc.Source.Structured.ContractObligations
import Zkc.Source.Structured.ContractComposition

set_option autoImplicit false
namespace Tests.ContractCallRequests
open Zkc.Source Zkc.Source.Structured

variable {snapshot : Snapshot} {imported : Imported snapshot}
    {owner : ContractBinding imported} {F G : Type}
    [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]
    {environment : RelationEnvironment imported F G} {invocation : InvocationCoordinate}
    {context : ProtocolContext} {boundary : ContractBoundaryValues owner F G}
    {assignments : LogicalAssignments (assignment F G) owner invocation}

/-- The unresolved terminal retains an actual typed output selector. -/
def impossibleTerminal {type : Ty} (selector : BoundarySelector owner.protocol.signature type)
    (output : selector.port.direction = .output) : ExternalTerminal owner F G :=
  { parameterTypes := [], parameters := .nil, outputTypes := [type], nonempty := by simp,
    outputs := .cons ⟨selector, output⟩ .nil, meaning := fun _ _ => False }

/-- Even arbitrary successful local leaves cannot erase a selected terminal.
This includes owners with zero calls or zero authored clauses. -/
example {type : Ty} (selector : BoundarySelector owner.protocol.signature type)
    (output : selector.port.direction = .output)
    (CallRequest : CallOccurrence owner.protocol.body → Sort _) :
    ¬ Nonempty (SelectedObligations
      (environment := environment) (assignments := assignments) (context := context) (boundary := boundary)
      (.one (.terminal (impossibleTerminal selector output))) CallRequest) := by
  rintro ⟨evidence⟩
  rcases evidence.localRequests with ⟨parameters, outputs, _, _, impossible⟩
  exact impossible

/-- A True terminal is only an availability request for this output. It does
not constrain the value or prove an undeclared property of the callee. -/
def availableTerminal {type : Ty} (selector : BoundarySelector owner.protocol.signature type)
    (output : selector.port.direction = .output) : ExternalTerminal owner F G :=
  { parameterTypes := [], parameters := .nil, outputTypes := [type], nonempty := by simp,
    outputs := .cons ⟨selector, output⟩ .nil, meaning := fun _ _ => True }

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem availableTerminal_iff {type : Ty} (selector : BoundarySelector owner.protocol.signature type)
    (output : selector.port.direction = .output) :
    (availableTerminal selector output).Holds context boundary assignments ↔
      ∃ value, selector.read context boundary = some value := by
  cases read : selector.read context boundary <;>
    simp [ExternalTerminal.Holds, availableTerminal, ExternalTerminal.readParameters,
      ExternalTerminal.readOutputs, RoleFamily.sequence, read]

/-- Even the weakest terminal cannot read a fabricated result after stop. -/
example {Γ : List Ty} (call : CheckedApplication owner Γ) (self : Nat)
    (values : Environment (Component (assignment F G)) Γ) (reason : PIR.Stop)
    {type : Ty} (selector : BoundarySelector owner.protocol.signature type)
    (output : selector.port.direction = .output) :
    ¬ (availableTerminal selector output).Holds (context.enter call.site call.roles)
      (call.boundaryOfOutcome context self values (.stopped reason)) assignments :=
  ExternalTerminal.not_holds_stopped _ call context self values reason assignments

#print axioms availableTerminal_iff

end Tests.ContractCallRequests
