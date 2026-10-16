import Zkc.Source.Structured.ContractComposition
import Tests.ContractCalls

set_option autoImplicit false
namespace Tests.ContractInvocation
open Zkc.Source Zkc.Source.Structured

/-- These lexical positions come from the actual nested repeat fixture. The
iteration numbers are explicit logical labels, not execution-reachability evidence. -/
def firstInvocation : InvocationCoordinate :=
  ⟨0, [.iteration 0 [1] 0, .application 0 Tests.ContractCalls.inner.position]⟩
def secondInvocation : InvocationCoordinate :=
  ⟨0, [.iteration 0 [1] 1, .application 0 Tests.ContractCalls.inner.position]⟩
example : firstInvocation ≠ secondInvocation := by decide

variable {snapshot : Snapshot} {imported : Imported snapshot}
  {callee : ContractBinding imported} {Γ : List Ty} {Value : Ty → Type}

/-- Distinct explicit indices give distinct invocation labels for every checked
call. This does not assert that either index is reached by an execution. -/
example (call : CheckedApplication callee Γ) (parent : InvocationCoordinate)
    (first second : call.Iterations) (different : first ≠ second) :
    call.childInvocation parent first ≠ call.childInvocation parent second :=
  fun same => different (call.childInvocation_iterations_injective parent same)

/-- Deliberate fixed experiment values, typed before any runtime input exists. -/
def fixedInstantiation (call : CheckedApplication callee Γ) (fixed : (type : Ty) → Value type) :
    AssignmentInstantiation Value call :=
  ⟨fun type _ => .supplied (fixed type), fun _ _ => .unavailable⟩

/-- Independent adversarial runtime boundaries cannot change this explicitly
selected mathematical parameter. No claim of runtime agreement follows. -/
example (call : CheckedApplication callee Γ) (fixed : (type : Ty) → Value type)
    (parent : InvocationCoordinate) (iterations : call.Iterations) (context : ProtocolContext)
    (left right : BoundaryValuation Value call.caller.protocol.inputs call.caller.protocol.outputs)
    (assignments : LogicalAssignments Value call.caller parent)
    {type : Ty} (selector : BoundarySelector callee.protocol.signature type) :
    ((fixedInstantiation call fixed).apply iterations context left assignments).parameters type selector =
      ((fixedInstantiation call fixed).apply iterations context right assignments).parameters type selector := rfl

/-- Separate invocation labels can explicitly share one fixed experiment,
without identifying their boundaries or adversary-owned runtime operands. -/
example (call : CheckedApplication callee Γ) (fixed : (type : Ty) → Value type)
    (parent : InvocationCoordinate) (first second : call.Iterations) (context : ProtocolContext)
    (left right : BoundaryValuation Value call.caller.protocol.inputs call.caller.protocol.outputs)
    (assignments : LogicalAssignments Value call.caller parent)
    {type : Ty} (selector : BoundarySelector callee.protocol.signature type) :
    ((fixedInstantiation call fixed).apply first context left assignments).parameters type selector =
      ((fixedInstantiation call fixed).apply second context right assignments).parameters type selector := rfl

/-- A parameter source and an actual boundary source are distinct explicit choices. -/
example (owner : ContractBinding imported) {type : Ty}
    (selector : BoundarySelector owner.protocol.signature type) :
    (AssignmentSource.parameter selector : AssignmentSource Value owner type) ≠ .boundary selector := by
  intro same
  cases same

/-- The type checker refuses implicit reuse at another invocation. -/
example (owner : ContractBinding imported)
    (assignments : LogicalAssignments Value owner firstInvocation) :
    Nonempty (LogicalAssignments Value owner firstInvocation) := by
  fail_if_success have wrong : LogicalAssignments Value owner secondInvocation := assignments
  exact ⟨assignments⟩

/-- The index is a logical discipline, not a capability boundary: explicit
repackaging can share the same assignment values under another label. -/
example (owner : ContractBinding imported)
    (assignments : LogicalAssignments Value owner firstInvocation) :
    Nonempty (LogicalAssignments Value owner secondInvocation) :=
  ⟨⟨assignments.parameters, assignments.witnesses⟩⟩

/-- Repeat passes a fresh induction value to the same callback context. The
logical coordinate distinction above does not alter these operational semantics. -/
example {F G : Type} (context : ProtocolContext) (self : Nat)
    (state : Values (Component (assignment F G)) Tests.ContractCalls.repeatSpec.state)
    (body : RegionFunction (Component (assignment F G)) (observedInterface F G)
      ([Ty.index, Ty.index], [Ty.index])) (index : Nat) :
    Repeat.step Tests.ContractCalls.repeatSpec context self .nil body state index =
      (body (.cons (some index)
        ((maskValues self (context.mapScopes Tests.ContractCalls.repeatSpec.stateScopes) state).append .nil))).bind
          (fun returned => .done (maskValues self
            (context.mapScopes Tests.ContractCalls.repeatSpec.stateScopes) returned)) := rfl

#print axioms Zkc.Source.Structured.CheckedApplication.childInvocation_iterations_injective
end Tests.ContractInvocation
