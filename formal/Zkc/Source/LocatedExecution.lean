import Zkc.Source.Definitions

/-! Execute a resolved local body at one participant of a synchronous entry.

The selected local interpretation and handler receive only explicit arguments
and that participant's state. The joint observer retains a structured origin
and all local effects. Origins are diagnostic values, not transcript encodings.
This module does not generate participants or implement message delivery.
-/

set_option autoImplicit false

namespace Zkc.Source.LocatedExecution

/-- Frames are supplied by the enclosing structured invocation/loop traversal. -/
inductive Frame where
  | invocation (site : Nat)
  | iteration (site index : Nat)
  deriving DecidableEq, Repr

/-- The entry and selected instance identities remain parameters of the profile. -/
structure Origin (Role Entry Instance : Type) where
  role : Role
  entry : Entry
  instanceId : Instance
  path : List Frame
  site : Nat
  deriving DecidableEq, Repr

variable {Role Entry Instance : Type} {State Event : Role → Type}

/-- A family for the joint observer, not an environment exposed to every role. -/
abbrev States (State : Role → Type) := (role : Role) → State role

structure StateWithOrigin (Role Entry Instance : Type) (State : Role → Type) where
  locals : States State
  stoppedAt : Option (Origin Role Entry Instance)

structure LocatedEvent (Role Entry Instance : Type) (Event : Role → Type) where
  origin : Origin Role Entry Instance
  value : Event origin.role

/-- Update one role even when participants have different state types. -/
def update [DecidableEq Role] (states : States State) (role : Role) (value : State role) :
    States State := fun other =>
  if same : other = role then same.symm ▸ value else states other

@[simp] theorem update_self [DecidableEq Role] (states : States State)
    (role : Role) (value : State role) : update states role value role = value := by
  simp [update]

@[simp] theorem update_other [DecidableEq Role] (states : States State)
    (role other : Role) (value : State role) (different : other ≠ role) :
    update states role value other = states other := by
  simp [update, different]

/-- Lift one completed local action into the selected joint observation.
Entry/instance/path identification is retained on stops, including empty traces. -/
def lift [DecidableEq Role] {A : Type} (origin : Origin Role Entry Instance)
    (states : States State) (result : PIR.Execution (State origin.role) (Event origin.role) A) :
    PIR.Execution (StateWithOrigin Role Entry Instance State)
      (LocatedEvent Role Entry Instance Event) A :=
  ⟨result.outcome,
    ⟨update states origin.role result.state,
      match result.outcome with
      | .returned _ => none
      | .stopped _ => some origin⟩,
    result.events.map fun event => ⟨origin, event⟩⟩

variable {language : Language} {interface : PIR.Signature}

/-- `none` excludes ordinary communication and unclassified effects from a local block.
The classification is a selected interface contract, not an inferred handler property. -/
def localPolicy (locations : interface.Op → Option Role) (role : Role) :
    PIR.Interaction interface where
  Role := Option Role
  Phase := Unit
  owner := locations
  enabled _ op := locations op = some role
  advance _ _ _ := ()

/-- Reuse all-reply interaction conformance for the actual local body. -/
abbrev LocallyAdmitted (locations : interface.Op → Option Role) (role : Role)
    {A : Type} (body : PIR.Proc interface A) : Prop :=
  PIR.Conforms (localPolicy locations role) body ()

theorem reached_local {A : Type} (locations : interface.Op → Option Role) (role : Role)
    (body : PIR.Proc interface A) (admitted : LocallyAdmitted locations role body)
    (op : interface.Op) (next : interface.Reply op → PIR.Proc interface A)
    (path : PIR.Reaches (localPolicy locations role) body () (.call op next) ()) :
    locations op = some role :=
  PIR.reached_call_permitted (localPolicy locations role) body () () op next path admitted

/-- Reference execution, independently of admission. A local source block additionally
requires `LocallyAdmitted` for this actual body and its selected effect classification.
The interpretation/handler are fixed independently of this joint-state input. -/
def run [DecidableEq Role] (origin : Origin Role Entry Instance)
    (base : Interpretation language interface)
    {scope : List (DefinitionSignature language.Ty)} (definitions : Definitions language scope)
    {signature : DefinitionSignature language.Ty} (callee : Var scope signature)
    (args : Values base.Value signature.arguments)
    (handler : PIR.Handler interface (State origin.role) (Event origin.role))
    (states : States State) :
    PIR.Execution (StateWithOrigin Role Entry Instance State)
      (LocatedEvent Role Entry Instance Event) (base.Value signature.result) :=
  lift origin states ((definitions.operation base (.call callee) args).run
    handler (states origin.role))

/-- The active participant receives the actual post-state, including on stops. -/
theorem run_state [DecidableEq Role] (origin : Origin Role Entry Instance)
    (base : Interpretation language interface)
    {scope : List (DefinitionSignature language.Ty)} (definitions : Definitions language scope)
    {signature : DefinitionSignature language.Ty} (callee : Var scope signature)
    (args : Values base.Value signature.arguments)
    (handler : PIR.Handler interface (State origin.role) (Event origin.role))
    (states : States State) :
    (run origin base definitions callee args handler states).state.locals origin.role =
      ((definitions.operation base (.call callee) args).run
        handler (states origin.role)).state := by
  simp [run, lift]

/-- Other roles keep their actual state; a joint stop does not invent peer rejection. -/
theorem run_frame [DecidableEq Role] (origin : Origin Role Entry Instance)
    (base : Interpretation language interface)
    {scope : List (DefinitionSignature language.Ty)} (definitions : Definitions language scope)
    {signature : DefinitionSignature language.Ty} (callee : Var scope signature)
    (args : Values base.Value signature.arguments)
    (handler : PIR.Handler interface (State origin.role) (Event origin.role))
    (states : States State) (other : Role) (different : other ≠ origin.role) :
    (run origin base definitions callee args handler states).state.locals other = states other := by
  simp [run, lift, different]

/-- Inspect only the executing role's result, post-state, stop origin and events. -/
def localView {A : Type} (role : Role)
    (result : PIR.Execution (StateWithOrigin Role Entry Instance State)
      (LocatedEvent Role Entry Instance Event) A) :=
  (result.outcome, result.state.locals role, result.state.stoppedAt, result.events)

/-- Changing hidden peer state cannot change the selected action's complete local view. -/
theorem run_local [DecidableEq Role] (origin : Origin Role Entry Instance)
    (base : Interpretation language interface)
    {scope : List (DefinitionSignature language.Ty)} (definitions : Definitions language scope)
    {signature : DefinitionSignature language.Ty} (callee : Var scope signature)
    (args : Values base.Value signature.arguments)
    (handler : PIR.Handler interface (State origin.role) (Event origin.role))
    (left right : States State) (same : left origin.role = right origin.role) :
    localView origin.role (run origin base definitions callee args handler left) =
      localView origin.role (run origin base definitions callee args handler right) := by
  simp only [run, localView, lift, update_self, same]

/-- The caller suffix is never run after a stopped local body, even after local effects. -/
theorem run_stopped [DecidableEq Role] {B : Type} (origin : Origin Role Entry Instance)
    (base : Interpretation language interface)
    {scope : List (DefinitionSignature language.Ty)} (definitions : Definitions language scope)
    {signature : DefinitionSignature language.Ty} (callee : Var scope signature)
    (args : Values base.Value signature.arguments)
    (handler : PIR.Handler interface (State origin.role) (Event origin.role))
    (states : States State) (final : State origin.role) (events : List (Event origin.role))
    (reason : PIR.Stop)
    (stopped : (definitions.operation base (.call callee) args).run handler (states origin.role) =
      ⟨.stopped reason, final, events⟩)
    (next : base.Value signature.result → StateWithOrigin Role Entry Instance State →
      PIR.Execution (StateWithOrigin Role Entry Instance State)
        (LocatedEvent Role Entry Instance Event) B) :
    (run origin base definitions callee args handler states).follow next =
      ⟨.stopped reason, ⟨update states origin.role final, some origin⟩,
        events.map fun event => ⟨origin, event⟩⟩ := by
  simp only [run, stopped, lift, PIR.Execution.follow]

end Zkc.Source.LocatedExecution
