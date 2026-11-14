module

public import Std.Data.HashMap
public import Zkc.Core.Types
public import Zkc.Frontend.Basic.Diagnostic
public import Zkc.Frontend.Semantics.Static

@[expose] public section

set_option autoImplicit false

/-!
# What the session keeps of an instance

The body of an instance is its typed tree, and the tables that the passes make of it
(`Typed.Definition`, `Typed.Checked`). Beside them the session keeps what the other instances,
the packages, the schemes and the tools ask of an instance without reading its tree: of a
function its closed signature, whether it can stop, and what it waits for; of a protocol its
ports and results with their holders, its sites in the order of their numbers, its flows and
its specification arguments.

The rows that bodies apply are here too: a row of the vocabulary with its kind and its type at
its static arguments, as the frontend names it. A package numbers what it reaches when it is
emitted.
-/

namespace Zkc.Frontend.Typing

abbrev RowId := Nat

/-- A static argument of a row. -/
inductive RowStatic where
  | type (type : ClosedType)
  | nat (value : Nat)
  deriving Inhabited, BEq, Hashable

/-- The identity of a row: its catalogue name and static arguments. -/
structure RowKey where
  name : String
  statics : Array RowStatic
  deriving Inhabited, BEq, Hashable

inductive RowKind where
  | pure
  /-- Defined on a domain: the row named, a pure row with the same inputs and one `bool`
  output, decides it. -/
  | restricted (domain : Option RowKey)
  /-- A law (TY15): it samples a value of its output; a `draw` or a `sample` applies it. -/
  | sampling
  deriving Inhabited, BEq

/-- A row of the vocabulary that the frontend applies, with its type at its static arguments. -/
structure Row where
  key : RowKey
  kind : RowKind
  inputs : Array ClosedType
  outputs : Array ClosedType
  deriving Inhabited

/-- A place of the text and the name of the member an operator there is (SP12): the file, the
first and the last byte, and the member's name. -/
abbrev ResolvedPlace := String × UInt32 × UInt32 × String

/-- What is kept of a function instance. -/
structure FunctionCode where
  /-- The name a table of names gives it: the instance as source writes it. -/
  name : String
  inputs : Array ClosedType
  outputs : Array ClosedType
  /-- Whether it can stop (FN2). -/
  canStop : Bool
  /-- A form of a later layer that the function or a callee needs, which keeps the packages that
  reach it from being emitted. -/
  waiting : Option String := none
  /-- A specification function: a `spec def`, the formula of a relation, a law (SX1). -/
  specificationOnly : Bool := false
  /-- Bound to the formal library: the external name. The function is a header. -/
  external : Option String := none
  /-- In the opaque elaboration of a definition generic over a module parameter (SP12): each
  place at which an operator, a form or a dot call was resolved to a member of the parameter's
  interface, with the member's name, and the parameter. -/
  resolved : Array (ResolvedPlace × ParameterRef) := #[]
  deriving Inhabited

/-- A core site of a protocol: the event of the text it belongs to (EV3), its part, the name
of the site, and the place of the event. The core's sites are numbers; the part of an event is
in this table only. -/
structure SiteEntry where
  event : Nat
  part : String
  name : Option String
  place : Syntax.Span
  /-- The iteration of each loop around the event whose iterations are in sequence, outermost
  first; empty for an event of no such loop, whose site stands for all its occurrences. -/
  iteration : Array Nat := #[]
  deriving Inhabited

/-- A specification argument of an application: the core site of the application, the port, the
expression and its type. It is typed and not emitted: no deployed code computes it (SX4). -/
structure SpecificationArgument where
  site : Nat
  port : String
  text : String
  type : String
  place : Syntax.Span
  deriving Inhabited

/-- A flow of a protocol body, in the order of its sites: an exchange, a draw of a law, or an
application, whose flows are those of its callee under the role map. The construction of a
scheme reads the flows of its protocol (SC3 to SC5). -/
inductive FlowEntry where
  | exchange (sender receiver : Nat) (type : ClosedType) (site : Nat)
  | draw (owner : Nat) (receivers : Array Nat) (law : RowId) (site : Nat)
  | apply (callee : InstanceId) (roleMap : Array Nat)
  deriving Inhabited

/-- What is kept of a protocol instance. -/
structure ProtocolCode where
  name : String
  roles : Array String
  /-- One input per holder of each port that is not `spec`, with its type and its holder. -/
  inputs : Array (ClosedType × Nat)
  /-- The number of the port of each input, among the ports that are not `spec`. -/
  inputPorts : Array Nat := #[]
  /-- One output per holder of each result. -/
  outputs : Array (ClosedType × Nat)
  /-- The ports and results with several holders: over the outputs or the inputs, and the
  positions of their copies. -/
  agreements : Array (Bool × Array Nat)
  /-- The sites, in the order of their numbers. -/
  sites : Array SiteEntry
  /-- The flows of the body, in the order of the sites. -/
  flows : Array FlowEntry := #[]
  /-- The specification arguments of its applications. -/
  specificationArguments : Array SpecificationArgument := #[]
  /-- In the opaque elaboration of a protocol generic over a module parameter (SP12): the
  places resolved to a member of the parameter's interface, and the parameter. -/
  resolved : Array (ResolvedPlace × ParameterRef) := #[]
  waiting : Option String := none
  specificationOnly : Bool := false
  deriving Inhabited

/-- What the typing of the body of an instance has come to. -/
inductive BodyState where
  | inProgress
  | done (code : FunctionCode)
  /-- Refused; the refusal is recorded. -/
  | failed
  /-- Not typed here, for the reason given: a form of a later layer. -/
  | waiting (reason : String)
  /-- Not typed to the end: a budget of the compiler ran out, in this body or in one it calls.
  It is not refused (SP10). -/
  | exhausted (exhaustion : Exhaustion)
  /-- Bound to a row: a call applies it. -/
  | row (row : RowId)
  /-- A protocol instance. -/
  | protocol (code : ProtocolCode)
  deriving Inhabited

/-- The obligation that a typed law leaves (SP10): the module instance it is about, the law at
its instance, and its place. That it holds is a statement of the formal library. -/
structure Obligation where
  «module» : String
  law : String
  place : Syntax.Span
  deriving Inhabited

end Zkc.Frontend.Typing
