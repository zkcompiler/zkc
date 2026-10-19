module

public import Zkc.Source.Structured.ContractBoundary

@[expose] public section

set_option autoImplicit false
namespace Zkc.Source.Structured

namespace ApplicationOccurrence
variable {signature : ProtocolSignature} {roles : List Nat} {site : String}
  {Γ : List Ty} {operands : Operands Γ signature.inputs}

/-- Child zero descends into a callback/bind body; child one into a suffix.
The path is recovered from occurrence evidence for the actual checked tree. -/
def position : {Δ out : List Ty} → {body : Region protocolDialect Δ out} →
    ApplicationOccurrence signature roles site operands body → List Nat
  | _, _, _, .here _ => []
  | _, _, _, .next _ _ _ _ occurrence => 1 :: occurrence.position
  | _, _, _, .bindBody _ _ occurrence => 0 :: occurrence.position
  | _, _, _, .bindNext _ _ occurrence => 1 :: occurrence.position
  | _, _, _, .repeatBody _ _ _ _ _ occurrence => 0 :: occurrence.position

/-- Enclosing repeat positions and their admitted maxima, outermost first. -/
def repeats : {Δ out : List Ty} → {body : Region protocolDialect Δ out} →
    ApplicationOccurrence signature roles site operands body → List (List Nat × Nat)
  | _, _, _, .here _ => []
  | _, _, _, .next _ _ _ _ occurrence => occurrence.repeats.map fun (path, bound) => (1 :: path, bound)
  | _, _, _, .bindBody _ _ occurrence => occurrence.repeats.map fun (path, bound) => (0 :: path, bound)
  | _, _, _, .bindNext _ _ occurrence => occurrence.repeats.map fun (path, bound) => (1 :: path, bound)
  | _, _, _, .repeatBody spec _ _ _ _ occurrence =>
    ([], spec.maximum) :: occurrence.repeats.map (fun (path, bound) => (0 :: path, bound))

end ApplicationOccurrence

variable {snapshot : Snapshot} {imported : Imported snapshot} {callee : ContractBinding imported}
  {Γ : List Ty} {Value : Ty → Type}

/-- Explicit logical indices for every enclosing repeat. Being below the static
maximum is necessary; neither this index nor `childInvocation` identifies a
reached runtime iteration. Reachability and the run's count remain separate
execution obligations. No iteration identity comes from applicationPrefix. -/
abbrev CheckedApplication.Iterations (call : CheckedApplication callee Γ) :=
  (index : Fin call.occurrence.repeats.length) → Fin (call.occurrence.repeats.get index).2

def CheckedApplication.childInvocation (call : CheckedApplication callee Γ)
    (parent : InvocationCoordinate) (iterations : call.Iterations) : InvocationCoordinate :=
  ⟨parent.root, parent.frames ++
    List.ofFn (fun index => InvocationFrame.iteration call.caller.protocolIndex
      (call.occurrence.repeats.get index).1 (iterations index)) ++
    [.application call.caller.protocolIndex call.occurrence.position]⟩

/-- Instantiation is an explicit choice. A caller parameter, extracted witness,
or actual boundary copy may supply a callee logical slot. Runtime SSA operands
are never automatically declared authoritative parameters. -/
inductive AssignmentSource (Value : Ty → Type) (owner : ContractBinding imported) (type : Ty) where
  | unavailable
  | supplied (value : Value type)
  | parameter (selector : BoundarySelector owner.protocol.signature type)
  | witness (selector : BoundarySelector owner.protocol.signature type)
  | boundary (selector : BoundarySelector owner.protocol.signature type)

def AssignmentSource.read {owner : ContractBinding imported} {type : Ty}
    {invocation : InvocationCoordinate} (source : AssignmentSource Value owner type)
    (context : ProtocolContext)
    (boundary : BoundaryValuation Value owner.protocol.inputs owner.protocol.outputs)
    (assignments : LogicalAssignments Value owner invocation) : Option (Value type) :=
  match source with
  | .unavailable => none
  | .supplied value => some value
  | .parameter selector => assignments.parameters type selector
  | .witness selector => assignments.witnesses type selector
  | .boundary selector => selector.read context boundary

structure AssignmentInstantiation (Value : Ty → Type) (call : CheckedApplication callee Γ) where
  parameters : (type : Ty) → BoundarySelector callee.protocol.signature type → AssignmentSource Value call.caller type
  witnesses : (type : Ty) → BoundarySelector callee.protocol.signature type → AssignmentSource Value call.caller type

def AssignmentInstantiation.apply {call : CheckedApplication callee Γ}
    (instantiation : AssignmentInstantiation Value call) {parent : InvocationCoordinate}
    (iterations : call.Iterations) (context : ProtocolContext)
    (boundary : BoundaryValuation Value call.caller.protocol.inputs call.caller.protocol.outputs)
    (assignments : LogicalAssignments Value call.caller parent) :
    LogicalAssignments Value callee (call.childInvocation parent iterations) :=
  ⟨fun type selector => (instantiation.parameters type selector).read context boundary assignments,
    fun type selector => (instantiation.witnesses type selector).read context boundary assignments⟩

theorem AssignmentInstantiation.parameter {call : CheckedApplication callee Γ}
    (instantiation : AssignmentInstantiation Value call) {parent : InvocationCoordinate}
    (iterations : call.Iterations) (context : ProtocolContext)
    (boundary : BoundaryValuation Value call.caller.protocol.inputs call.caller.protocol.outputs)
    (assignments : LogicalAssignments Value call.caller parent) {type : Ty}
    (selector : BoundarySelector callee.protocol.signature type) :
    (instantiation.apply iterations context boundary assignments).parameters type selector =
      (instantiation.parameters type selector).read context boundary assignments := rfl

theorem AssignmentInstantiation.witness {call : CheckedApplication callee Γ}
    (instantiation : AssignmentInstantiation Value call) {parent : InvocationCoordinate}
    (iterations : call.Iterations) (context : ProtocolContext)
    (boundary : BoundaryValuation Value call.caller.protocol.inputs call.caller.protocol.outputs)
    (assignments : LogicalAssignments Value call.caller parent) {type : Ty}
    (selector : BoundarySelector callee.protocol.signature type) :
    (instantiation.apply iterations context boundary assignments).witnesses type selector =
      (instantiation.witnesses type selector).read context boundary assignments := rfl

end Zkc.Source.Structured
