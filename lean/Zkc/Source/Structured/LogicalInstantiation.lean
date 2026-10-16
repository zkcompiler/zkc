module

public import Zkc.Source.Structured.LogicalContext

@[expose] public section

/-! Logical substitution at actual checked applications. A callee's binders are
renamed into the caller's context; its legacy selector-named slots follow the
existing `AssignmentInstantiation`. Runtime operands are never declared
authoritative logical values. Invocation labels remain labels, not reachability. -/

set_option autoImplicit false
namespace Zkc.Source.Structured.Logical
open Zkc.Source Zkc.Source.Structured

variable {snapshot : Snapshot} {imported : Imported snapshot}
  {V : Vocabulary} {Value : Ty → Type} {interpretation : Interpretation V Value}

/-- The legacy view: selector-named slots of the one store. -/
def Store.legacy {owner : ContractBinding imported} {invocation : InvocationCoordinate}
    {context : List (LogicalType V.Sorts)} (store : Store interpretation owner invocation context) :
    LogicalAssignments Value owner invocation :=
  ⟨fun _ selector => store.get (.parameter selector), fun _ selector => store.get (.witness selector)⟩

/-- Embed existing assignments together with lexical binder values. This is an
adapter into the one store, not a second persistent assignment mechanism. -/
def Store.extend {owner : ContractBinding imported} {invocation : InvocationCoordinate}
    {context : List (LogicalType V.Sorts)} (old : LogicalAssignments Value owner invocation)
    (values : Values interpretation.Denote context) : Store interpretation owner invocation context :=
  ⟨fun key => match key with
    | .binder ref => some (values.get ref)
    | .parameter selector => old.parameters _ selector
    | .witness selector => old.witnesses _ selector⟩

theorem Store.legacy_extend {owner : ContractBinding imported} {invocation : InvocationCoordinate}
    {context : List (LogicalType V.Sorts)} (old : LogicalAssignments Value owner invocation)
    (values : Values interpretation.Denote context) :
    (Store.extend old values).legacy = old := rfl

/-- Existing sources become terms. Only `boundary` observes the runtime; the
legacy `parameter`/`witness` sources read the corresponding keys. -/
def lowerSource {owner : ContractBinding imported} {context : List (LogicalType V.Sorts)} {type : Ty} :
    AssignmentSource Value owner type → Term V Value owner.protocol.signature context (.native type)
  | .unavailable => .unavailable
  | .supplied value => .supplied value
  | .parameter selector => .key (.parameter selector)
  | .witness selector => .key (.witness selector)
  | .boundary selector => .observed selector

theorem lowerSource_read {owner : ContractBinding imported} {invocation : InvocationCoordinate}
    {context : List (LogicalType V.Sorts)} {type : Ty} (source : AssignmentSource Value owner type)
    (protocolContext : ProtocolContext)
    (boundary : BoundaryValuation Value owner.protocol.inputs owner.protocol.outputs)
    (store : Store interpretation owner invocation context) :
    (lowerSource (V := V) source).read interpretation protocolContext boundary store =
      source.read protocolContext boundary store.legacy := by
  cases source <;> rfl

variable {callee : ContractBinding imported} {Γ : List Ty}

/-- Every callee key receives a caller term. -/
abbrev CallSubstitution (V : Vocabulary) (Value : Ty → Type) (call : CheckedApplication callee Γ)
    (parent child : List (LogicalType V.Sorts)) :=
  {type : LogicalType V.Sorts} → Key V.Sorts callee.protocol.signature child type →
    Term V Value call.caller.protocol.signature parent type

/-- Uses the real checked occurrence and invocation indexing. This adds no
reachability, execution or mathematical correctness assumption. -/
def instantiate {parent child : List (LogicalType V.Sorts)} {invocation : InvocationCoordinate}
    (call : CheckedApplication callee Γ) (substitution : CallSubstitution V Value call parent child)
    (iterations : call.Iterations) (protocolContext : ProtocolContext)
    (boundary : BoundaryValuation Value call.caller.protocol.inputs call.caller.protocol.outputs)
    (store : Store interpretation call.caller invocation parent) :
    Store interpretation callee (call.childInvocation invocation iterations) child :=
  ⟨fun key => (substitution key).read interpretation protocolContext boundary store⟩

/-- Binders are renamed into the caller context; legacy slots follow the given
existing instantiation. Same-typed binders are never identified implicitly. -/
def inherit {parent child : List (LogicalType V.Sorts)} (call : CheckedApplication callee Γ)
    (rename : Renaming child parent) (legacy : AssignmentInstantiation Value call) :
    CallSubstitution V Value call parent child
  | _, .binder ref => .key (.binder (rename ref))
  | _, .parameter selector => lowerSource (legacy.parameters _ selector)
  | _, .witness selector => lowerSource (legacy.witnesses _ selector)

section Inheritance
variable {parent child : List (LogicalType V.Sorts)} {invocation : InvocationCoordinate}
  (call : CheckedApplication callee Γ) (rename : Renaming child parent)
  (legacy : AssignmentInstantiation Value call) (iterations : call.Iterations)
  (protocolContext : ProtocolContext)
  (boundary : BoundaryValuation Value call.caller.protocol.inputs call.caller.protocol.outputs)
  (store : Store interpretation call.caller invocation parent)

theorem inherit_binder {type : LogicalType V.Sorts} (ref : Var child type) :
    (instantiate call (inherit call rename legacy) iterations protocolContext boundary store).get
      (.binder ref) = store.get (.binder (rename ref)) := rfl

/-- The legacy projection of a logical instantiation is exactly the existing
`AssignmentInstantiation.apply`, for every checked call and store. -/
theorem inherit_legacy :
    (instantiate call (inherit call rename legacy) iterations protocolContext boundary store).legacy =
      legacy.apply iterations protocolContext boundary store.legacy := by
  unfold Store.legacy AssignmentInstantiation.apply instantiate
  congr 1 <;> funext type selector <;> exact lowerSource_read _ _ _ _

end Inheritance

/-- Re-index a store along a proved owner equality. -/
def Store.reowner {owner other : ContractBinding imported} {invocation : InvocationCoordinate}
    {context : List (LogicalType V.Sorts)} (same : owner = other)
    (store : Store interpretation owner invocation context) : Store interpretation other invocation context :=
  same ▸ store

/-- Inheritance composes through two checked calls; each keeps its own
occurrence, caller boundary and legacy instantiation. -/
theorem inherit_composes {parent child grandchild : List (LogicalType V.Sorts)}
    {invocation : InvocationCoordinate} {Δ : List Ty} {last : ContractBinding imported}
    (outer : CheckedApplication callee Γ) (inner : CheckedApplication last Δ)
    (caller_eq : inner.caller = callee)
    (first : Renaming child parent) (second : Renaming grandchild child)
    (outerLegacy : AssignmentInstantiation Value outer) (innerLegacy : AssignmentInstantiation Value inner)
    (outerIterations : outer.Iterations) (innerIterations : inner.Iterations)
    (protocolContext : ProtocolContext)
    (outerBoundary : BoundaryValuation Value outer.caller.protocol.inputs outer.caller.protocol.outputs)
    (innerBoundary : BoundaryValuation Value inner.caller.protocol.inputs inner.caller.protocol.outputs)
    (store : Store interpretation outer.caller invocation parent)
    {type : LogicalType V.Sorts} (ref : Var grandchild type) :
    (instantiate inner (inherit inner second innerLegacy) innerIterations protocolContext innerBoundary
      (Store.reowner caller_eq.symm
        (instantiate outer (inherit outer first outerLegacy) outerIterations protocolContext
          outerBoundary store))).get (.binder ref) = store.get (.binder (first (second ref))) := by
  subst callee
  rfl

/-- Selector substitution at the actual call with the logical argument kept
outside runtime ports: the binder is the caller's, the output is the callee's
actual returned component at the composed role. -/
theorem inherited_output {parent child : List (LogicalType V.Sorts)} {invocation : InvocationCoordinate}
    (call : CheckedApplication callee Γ) (rename : Renaming child parent)
    (legacy : AssignmentInstantiation Value call) (iterations : call.Iterations)
    (protocolContext : ProtocolContext)
    (callerBoundary : BoundaryValuation Value call.caller.protocol.inputs call.caller.protocol.outputs)
    (store : Store interpretation call.caller invocation parent)
    (environment : Nat → Environment (Component Value) Γ)
    (returned : Nat → Values (Component Value) callee.protocol.outputs)
    {type : Ty} (selector : BoundarySelector callee.protocol.signature type)
    (ref : Var callee.protocol.outputs type) (selected : selector.port = .output ref) :
    (Term.observed (V := V) (context := child) selector).read interpretation
        (protocolContext.enter call.site call.roles) (call.boundary protocolContext environment returned)
        (instantiate call (inherit call rename legacy) iterations protocolContext callerBoundary store) =
      let self := protocolContext.roles (roleSubstitution call.roles selector.role)
      Participant.restrict
        (((protocolContext.mapScopes (callee.protocol.outputScopes.map
          (List.map (roleSubstitution call.roles))))[ref.index]?.getD []).contains self)
        ((returned self).get ref) :=
  call.output_substitution protocolContext environment returned selector ref selected

end Zkc.Source.Structured.Logical
