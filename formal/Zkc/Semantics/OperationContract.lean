import Std

/-! Dependent request/reply legality for interpreted operations.

`LawfulHandler` constrains replies to legal requests. It deliberately imposes no
postcondition on residual state or events; complete execution contracts live in
`Zkc.Semantics.Contracts` and must be supplied for stateful replacement laws.
-/

set_option autoImplicit false

namespace Zkc.Semantics.OperationContract

abbrev Site := Nat

structure Signature where
  Op : Type
  Arg : Op → Type
  Result : (op : Op) → Arg op → Type
  legalArg : (op : Op) → Arg op → Prop
  legalResult : (op : Op) → (a : Arg op) → Result op a → Prop

structure Request (sig : Signature) where
  site : Site
  op : sig.Op
  arg : sig.Arg op

inductive Reply (sig : Signature) (r : Request sig) where
  | ok : sig.Result r.op r.arg → Reply sig r
  | reject : String → Reply sig r
  | unavailable : String → Reply sig r

def LegalReply {sig : Signature} (r : Request sig) : Reply sig r → Prop
  | .ok v => sig.legalResult r.op r.arg v
  | .reject _ => True
  | .unavailable _ => True

abbrev Handler (sig : Signature) (State Event : Type) :=
  (r : Request sig) → State → Reply sig r × State × List Event

/-- Reply legality on legal arguments, without a state/event preservation claim. -/
def LawfulHandler {sig : Signature} {State Event : Type}
    (h : Handler sig State Event) : Prop :=
  ∀ r s, sig.legalArg r.op r.arg → LegalReply r (h r s).1
end Zkc.Semantics.OperationContract
