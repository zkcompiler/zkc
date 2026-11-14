module

public import Zkc.Frontend.Typed.Basic
public import Zkc.Frontend.Semantics.Instance

@[expose] public section

set_option autoImplicit false

/-!
# Closed signatures

The signature of a declaration at static values: what a reference to the instance needs, and
nothing of its body. A caller is elaborated against the signature of its callee, so a callee
whose body is refused still gives its callers their types, and a body is elaborated at most once
whatever the number of its callers.

For a type, a static name and a module the signature is the content of the instance. For a
function and a protocol it is the head with every type closed and every size a number.
-/

namespace Zkc.Frontend.Typed

open Syntax

structure Parameter where
  name : String
  span : Span
  type : ClosedType
  deriving Inhabited

structure FunctionSignature where
  parameters : Array Parameter
  result : ClosedType
  /-- For a relation, the number of statement parameters: the witness parameters follow. -/
  statementParameters : Option Nat := none
  /-- A `spec def`, the formula of a relation, a law (SX1). -/
  specification : Bool := false
  /-- Bound to a row of the vocabulary: a call applies the row. -/
  row : Option RowRef := none
  /-- Bound to the formal library. -/
  external : Option String := none
  kernel : Option String := none
  deriving Inhabited

structure Port where
  name : String
  span : Span
  type : ClosedType
  holders : RoleSet
  /-- For a handle placed `@H -> R`, the readers. -/
  readers : Option RoleSet := none
  isPrivate : Bool := false
  /-- A `spec` port: it has no holder and no operand. -/
  specification : Bool := false
  deriving Inhabited

structure ResultPort where
  name : String
  type : ClosedType
  holders : RoleSet
  readers : Option RoleSet := none
  deriving Inhabited

structure ProtocolSignature where
  roster : Array String
  ports : Array Port
  results : Array ResultPort
  /-- The events of the text, the same at every instance (EV3): a caller names a site through
  them. -/
  events : Array SourceEvent
  specification : Bool := false
  deriving Inhabited

inductive Signature where
  /-- A type, a static name, a module: the content of the instance. -/
  | data (content : InstanceContent)
  | function (signature : FunctionSignature)
  | protocol (signature : ProtocolSignature)
  /-- A signature with a type of a later layer: what refers to the instance waits. -/
  | waiting (reason : String)
  deriving Inhabited

end Zkc.Frontend.Typed
