module

public import Zkc.Source.Structured.ContractExecution

@[expose] public section

set_option autoImplicit false
namespace Zkc.Source.Structured
namespace CheckedApplication

variable {snapshot : Snapshot} {imported : Imported snapshot}
  {callee : ContractBinding imported} {Γ : List Ty} {Value : Ty → Type}
  (call : CheckedApplication callee Γ)

/-- Project one participant's application outcome using the actual checked SSA
operands and entered role context. The outcome is the application's result,
whose returned outputs already carry execution's output masks. Supplying an
Outcome alone does not prove it was reached: consumers use the actual run result.
No other participant's copies or stopped output tuples are populated. -/
def boundaryOfOutcome (context : ProtocolContext) (self : Nat)
    (environment : Environment (Component Value) Γ)
    (outcome : PIR.Outcome (Values (Component Value) callee.protocol.outputs)) :
    BoundaryValuation Value callee.protocol.inputs callee.protocol.outputs :=
  BoundaryValuation.ofOutcome self
    (maskValues self ((context.enter call.site call.roles).mapScopes callee.protocol.inputScopes)
      (call.operands.eval environment)) outcome

theorem boundaryOfOutcome_returned (context : ProtocolContext) (self : Nat)
    (environment : Environment (Component Value) Γ)
    (results : Values (Component Value) callee.protocol.outputs) :
    call.boundaryOfOutcome context self environment (.returned results) =
      BoundaryValuation.ofReturned self
        (maskValues self ((context.enter call.site call.roles).mapScopes callee.protocol.inputScopes)
          (call.operands.eval environment)) results := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Input observations are available on both returned and stopped outcomes.
The exact caller operand is read, under the composed role map and input mask. -/
theorem boundaryOfOutcome_input (context : ProtocolContext) (self : Nat)
    (environment : Environment (Component Value) Γ)
    (outcome : PIR.Outcome (Values (Component Value) callee.protocol.outputs))
    {type : Ty} (selector : BoundarySelector callee.protocol.signature type)
    (ref : Var callee.protocol.inputs type) (input : selector.port = .input ref)
    (selectedRole : context.roles (roleSubstitution call.roles selector.role) = self) :
    selector.read (context.enter call.site call.roles)
      (call.boundaryOfOutcome context self environment outcome) =
      Participant.restrict
        ((((context.enter call.site call.roles).mapScopes callee.protocol.inputScopes)[ref.index]?.getD []).contains self)
        (environment (call.operands.get ref)) := by
  simp only [BoundarySelector.read, input, boundaryOfOutcome, BoundaryValuation.ofOutcome]
  have enteredRole : (context.enter call.site call.roles).roles selector.role = self := selectedRole
  simp only [enteredRole, ↓reduceIte]
  simpa only [Operands.get_eval] using
    (contract_mask_get self ((context.enter call.site call.roles).mapScopes callee.protocol.inputScopes)
      (call.operands.eval environment) ref)

theorem boundaryOfOutcome_returned_output (context : ProtocolContext) (self : Nat)
    (environment : Environment (Component Value) Γ)
    (results : Values (Component Value) callee.protocol.outputs)
    {type : Ty} (selector : BoundarySelector callee.protocol.signature type)
    (ref : Var callee.protocol.outputs type) (output : selector.port = .output ref)
    (selectedRole : context.roles (roleSubstitution call.roles selector.role) = self) :
    selector.read (context.enter call.site call.roles)
      (call.boundaryOfOutcome context self environment (.returned results)) = results.get ref :=
  selector.read_returned_output _ self _ results ref output selectedRole

theorem boundaryOfOutcome_stopped_output (context : ProtocolContext) (self : Nat)
    (environment : Environment (Component Value) Γ) (reason : PIR.Stop)
    {type : Ty} (selector : BoundarySelector callee.protocol.signature type)
    (ref : Var callee.protocol.outputs type) (output : selector.port = .output ref) :
    selector.read (context.enter call.site call.roles)
      (call.boundaryOfOutcome context self environment (.stopped reason)) = none :=
  selector.read_stopped_output _ self _ reason ref output

theorem boundaryOfOutcome_other_output (context : ProtocolContext) (self : Nat)
    (environment : Environment (Component Value) Γ)
    (outcome : PIR.Outcome (Values (Component Value) callee.protocol.outputs))
    {type : Ty} (selector : BoundarySelector callee.protocol.signature type)
    (ref : Var callee.protocol.outputs type) (output : selector.port = .output ref)
    (otherRole : context.roles (roleSubstitution call.roles selector.role) ≠ self) :
    selector.read (context.enter call.site call.roles)
      (call.boundaryOfOutcome context self environment outcome) = none :=
  selector.other_output_absent _ self _ outcome ref output otherRole

theorem boundaryOfOutcome_decision (boolean : Value .boolean = Bool)
    (context : ProtocolContext) (self : Nat) (environment : Environment (Component Value) Γ)
    (outcome : PIR.Outcome (Values (Component Value) callee.protocol.outputs))
    (selector : BoundarySelector callee.protocol.signature .boolean)
    (ref : Var callee.protocol.outputs .boolean) (output : selector.port = .output ref)
    (selectedRole : context.roles (roleSubstitution call.roles selector.role) = self) :
    selector.read (context.enter call.site call.roles)
      (call.boundaryOfOutcome context self environment outcome) = some (boolean.symm ▸ true) ↔
      BoundaryValuation.ReturnedSatisfies (fun results => results.get ref = some (boolean.symm ▸ true)) outcome :=
  selector.returnedSatisfies_decision boolean _ self _ outcome ref output selectedRole

variable {F G : Type}

/-- Construct the existing component input from this actual checked call's
operands and context. This does not assert that the enclosing caller reaches it. -/
def componentInput (context : ProtocolContext) (self : Nat)
    (environment : Environment (Component (assignment F G)) Γ) : ComponentInput callee F G :=
  ⟨context.enter call.site call.roles, self, call.operands.eval environment⟩

theorem boundaryOfOutcome_eq_componentBoundary (context : ProtocolContext) (self : Nat)
    (environment : Environment (Component (assignment F G)) Γ)
    (outcome : PIR.Outcome (Values (Component (assignment F G)) callee.protocol.outputs)) :
    call.boundaryOfOutcome context self environment outcome =
      (call.componentInput context self environment).boundary outcome := rfl

variable [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

/-- Inside the checked role context this is precisely the actual application
operation, with its real helper/protocol tables. The caller's reachability and
continuation are handled by the structural composition rule, not this equality. -/
theorem componentInput_process (context : ProtocolContext) (self : Nat)
    (environment : Environment (Component (assignment F G)) Γ)
    (inside : (context.enter call.site call.roles).contains callee.protocol.signature self = true) :
    (call.componentInput context self environment).process =
      protocolOperation (imported.program.payload.tables F G) self
        (.protocolApply callee.protocol.signature call.roles call.site)
        (call.operands.eval environment) .nil (imported.program.payload.protocolTable F G) context :=
  (apply_inside (observedSites F G) observeAction (imported.program.payload.tables F G)
    (imported.program.payload.protocolTable F G) callee.protocol.signature call.roles call.site
    context self (call.operands.eval environment) inside).symm

end CheckedApplication
end Zkc.Source.Structured
