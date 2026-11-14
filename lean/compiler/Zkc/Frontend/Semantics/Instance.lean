module

public import Zkc.Frontend.Semantics.Static
public import Zkc.Frontend.Semantics.Refusal

@[expose] public section

set_option autoImplicit false

/-!
# Instances

An instance is a declaration with a closed value for each static parameter of its chain,
outermost scope first, without the specification-only ones (SP7, SP11). The table gives a key
one number, and an instance is elaborated once. A request for an instance that is in progress
is a declaration that reaches itself (NL1).

An instance is entered in the table of signatures of the store of results
(`Zkc.Frontend.Environment.Results`), whose entry keeps the declaration, the values, and what was
selected at them: the closed types of a signature, the members of a module.
-/

namespace Zkc.Frontend

/-- A declaration at values. `specification` holds the values of the specification-only
parameters, for a specification item only; a deployed declaration has none. -/
structure InstanceKey where
  declaration : DeclarationId
  arguments : Array StaticValue
  specification : Array Nat := #[]
  /-- For a law of an interface, the implementing module instance it is typed at: `Self` in it
  (SP10). -/
  owner : Option InstanceId := none
  /-- For a module instance that a module parameter stands for in the opaque typing (SP12): the
  parameter, and the type members that a `where` in scope equates with a type. Its other type
  members are fresh types. -/
  opaqueFor : Option (ParameterRef × Array String) := none
  deriving Inhabited, BEq, Hashable

/-- What a member of a module instance is. -/
inductive MemberValue where
  | type (type : ClosedType)
  | natural (value : Nat)
  | «module» («instance» : InstanceId)
  /-- A function or protocol member defined in source: the declaration that defines it. It is
  instantiated when it is called, at the module's values and its own. -/
  | definition (declaration : DeclarationId)
  /-- A function member that is a row of the vocabulary. -/
  | row (name : String)
  /-- A type member with static parameters of its own, of a module that a module parameter
  stands for in the opaque typing: each application is a fresh type, with the sorts of the
  member's bound (SP12). -/
  | opaqueType (sorts : Array String)
  deriving Inhabited

/-- What an instance is once elaborated, as far as a signature goes; the typing of bodies adds
to it. A type of a signature that is not evaluated here (it names a generated member, or a
specification-only parameter) is absent. -/
inductive InstanceContent where
  | alias (type : ClosedType)
  /-- A type bound to the vocabulary. -/
  | vocabularyType (type : ClosedType)
  | record (linear : Bool) (fields : Array (String × ClosedType))
  | «variant» (alternatives : Array (String × Array ClosedType))
  | staticName (value : Nat)
  /-- A function, a relation, an oracle function or a law: the types of its parameters and of
  its result. -/
  | signature (parameters : Array (String × Option ClosedType)) (result : Option ClosedType)
  /-- A protocol: the types of its ports and of its results. -/
  | protocol (ports : Array (String × Option ClosedType))
      (results : Array (String × Option ClosedType))
  /-- A module: the interfaces it names, at their static arguments, and its members by name. -/
  | «module» (interfaces : Array (DeclarationId × Array StaticValue))
      (members : Array (String × MemberValue))
  /-- A declaration whose content is not evaluated here: a specification type. -/
  | unevaluated
  /-- An instance that waits, with what it waits for: a constraint of its `where` that cannot be
  evaluated here, a form of a later layer. -/
  | waits (reason : String)
  deriving Inhabited

/-- The default instances of one declaration (SP7). -/
structure DefaultReport where
  declaration : DeclarationId
  count : Nat
  first : Option String
  /-- Why the declaration has no default instance, when it has none. -/
  none? : Option String := none
  deriving Inhabited

/-- A scheme as instantiation leaves it (SC1): the protocol instance it closes, and the suite of
its `construction derived(S)` line, read: the row of a catalogue suite, or why the scheme is not
constructed here. -/
structure SchemeEntry where
  name : String
  span : Syntax.Span
  protocol : InstanceId
  lines : Array Syntax.SchemeLine
  /-- The row of the catalogue suite, or the reason the scheme waits. -/
  suite : Except String String
  /-- A line that is not constructed here, as the reason the scheme waits. -/
  waits : Option String := none
  deriving Inhabited

end Zkc.Frontend
