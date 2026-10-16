module

public import Zkc.Source.Component
public import Zkc.Semantics.Execution

@[expose] public section

/-! Shared open participant rules independent of a mathematical language.

The value family interprets the type vocabulary. Service signatures specify
argument and result types only; their behavior and sampling policy are separate.
In particular, a query tag does not imply uniform randomness.
-/

set_option autoImplicit false

namespace Zkc.Source.Participant

structure Services (Ty : Type) where
  Op : Type
  arguments : Op → List Ty
  result : Op → Ty

inductive Action (Role Ty : Type) (services : Services Ty) (Value : Ty → Type) where
  | send {ty} (site : String) (receiver : Role) (value : Value ty)
  | receive (ty : Ty) (site : String) (sender : Role)
  | query (site : String) (op : services.Op) (args : Values Value (services.arguments op))

/-- A receive obtains an independent typed reply, without a sender-value equation.
A query returns exactly the result type declared by its service signature. -/
abbrev interface (Role Ty : Type) (services : Services Ty)
    (Value : Ty → Type) : PIR.Signature where
  Op := Action Role Ty services Value
  Reply
    | .send .. => Unit
    | .receive ty .. => Value ty
    | .query _ op _ => Value (services.result op)

variable {Role Ty : Type} [DecidableEq Role] {services : Services Ty} {Value : Ty → Type}

/-- The sender retains its own value after sending. The receiver consumes the
actual reply, ignoring its local operand. Other roles obtain no component.
Sender precedence also defines the unadmitted case of equal endpoints. -/
def exchange (self sender receiver : Role) (site : String) {ty : Ty}
    (value : Option (Value ty)) : PIR.Proc (interface Role Ty services Value) (Option (Value ty)) :=
  if sender = self then
    match value with
    | none => .halt .incomplete
    | some sent => .call (.send site receiver sent) fun _ => .done (some sent)
  else if receiver = self then
    .call (.receive ty site sender) fun received => .done (some received)
  else .done none

/-- Only the owner requires every ordered argument and queries the service.
The service's actual reply supplies the result; no sampling law is assumed. -/
def query (self owner : Role) (site : String) (op : services.Op)
    (args : Values (fun ty => Option (Value ty)) (services.arguments op)) :
    PIR.Proc (interface Role Ty services Value) (Option (Value (services.result op))) :=
  if owner = self then
    match RoleFamily.sequence args with
    | none => .halt .incomplete
    | some values => .call (.query site op values) fun value => .done (some value)
  else .done none

/-- A missing owned condition is incomplete; a false one rejects. Other roles
continue without inspecting the condition or emitting an action. -/
def guard (self owner : Role) (condition : Option Bool) :
    PIR.Proc (interface Role Ty services Value) Unit :=
  if owner = self then
    match condition with
    | none => .halt .incomplete
    | some value => if value then .done () else .halt .reject
  else .done ()

/-- Selection can hide an existing component but cannot create one. -/
def restrict {A : Type} (selected : Bool) (value : Option A) : Option A :=
  if selected then value else none

/-- Owned closed work requires every argument, including for zero results.
Other participants skip the work entirely. The rule is independent of the
effect interface, so closed callbacks can retain internal observations. -/
def owned {I : PIR.Signature} {inputs outputs : List Ty}
    (self owner : Role) (work : Values Value inputs → PIR.Proc I (Values Value outputs))
    (args : Values (Component Value) inputs) : PIR.Proc I (Values (Component Value) outputs) :=
  if owner = self then
    match RoleFamily.sequence args with
    | none => .halt .incomplete
    | some values => (work values).bind fun results => .done results.present
  else .done (Values.absent Value outputs)

theorem owned_other {I : PIR.Signature} {inputs outputs : List Ty}
    (self owner : Role) (different : owner ≠ self)
    (work : Values Value inputs → PIR.Proc I (Values Value outputs))
    (args : Values (Component Value) inputs) :
    owned self owner work args = .done (Values.absent Value outputs) := by
  simp [owned, different]

theorem owned_present {I : PIR.Signature} {inputs outputs : List Ty}
    (self : Role) (work : Values Value inputs → PIR.Proc I (Values Value outputs))
    (args : Values Value inputs) :
    owned self self work args.present = (work args).bind fun results => .done results.present := by
  simp [owned]

end Zkc.Source.Participant
