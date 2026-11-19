module

public import Zkc.Frontend.Typed.Tree
public import Zkc.Frontend.Basic.Diagnostic

@[expose] public section

set_option autoImplicit false

/-!
# What the passes leave beside a typed body

A pass reads the numbered tree of an instance and leaves a table or a verdict; it does not
change the tree. What depends on roles is in `Roles`, keyed by the number of a node or of a
binder; the occurrences of events are listed with the keys by which the layers below name
them.
-/

namespace Zkc.Frontend.Typed

open Syntax

/-- What the placement pass computes of the roles of a protocol body (HO1, HO2, CT1, EV5). -/
structure Roles where
  /-- The roles that can hold each binder, by its number: for a name bound inside a choice or a
  loop, those among them that take part have a value of it, and `computing` says who. A binder
  of a loop in sequence is bound again in every iteration, under one number: the table has the
  holders it has in the last. What is emitted per role is read from `computing`, whose keys are
  nodes. -/
  holders : Std.HashMap LocalId RoleSet := {}
  /-- The roles that compute: a binding, a pattern level, an update and a guard by the number
  of the statement; a collected value and a result of the body by the number of its
  expression. Inside a choice or a loop these are the participants among the holders. -/
  computing : Std.HashMap NodeId RoleSet := {}
  /-- The participants of an `if`, a `match` and a `for`, by the number of the statement. -/
  participants : Std.HashMap NodeId RoleSet := {}
  /-- The sender of a `send`, by the number of the statement. -/
  senders : Std.HashMap NodeId Nat := {}
  deriving Inhabited

/-- Source-ordered events for emission and generated views. An empty loop has no Core
instruction, but its sites still contribute empty collections to the source schema. -/
inductive CheckedEvent where
  | event (node : NodeId) (id : EventId) (what : Event) (iteration : Array Nat)
      (nested : Bool) (realized : Bool)
  /-- The zero-iteration body could not be typed apart. Its source sites are unresolved. -/
  | untypedLoop (span : Span)
  deriving Inhabited

/-- A typed body after the passes. -/
structure Checked where
  /-- The definition, its nodes numbered. -/
  definition : Definition
  roles : Roles := {}
  /-- The occurrences of its events, in the order of the tree. -/
  events : Array CheckedEvent := #[]
  deriving Inhabited

end Zkc.Frontend.Typed
