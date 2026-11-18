module

public import Zkc.Core.Program.HeaderSummary
public import Zkc.Core.Program.Syntax
public import Zkc.Core.Program.Refusal
public import Zkc.Core.Program.Shape
public import Zkc.Core.Program.Located
public import Zkc.Core.Program.Requirement

@[expose] public section

/-!
The operations of the three dialects by names, the program by names of them that a frontend
gives, and a refusal of such a program.

The operations of a function (`LocalRaw`) are a row of the vocabulary, an operation that the core
owns by its name (`OwnedName`) with its types and its numbers, a literal and a call; those of a
protocol (`ProtocolRaw`) and of a role program (`RoleRaw`) say who computes, the events and who
keeps a narrowed value. A definition by names (`Definition`) is a function with a `HeaderSummary` or a
protocol. Its body is a region over the operations of its dialect. A program by names
(`NamedProgram`) stores its definitions in order. A
refusal of a program (`ProgramRefusal`) is a refusal of `Program/Refusal.lean` with the types
and the written operations of a function as values.
-/

namespace Zkc.Core

/-- The operations of a protocol. Who computes, who takes part in an event (its class, with
its type) and who keeps a narrowed value is written; the holders of every value follow. -/
inductive ProtocolRaw (V : Vocabulary) where
  | compute (roles : List Role) (o : LocalRaw V)
  | event (cls : EventClass V) (τ : V.Ty)
  | narrow (roles : List Role)
  | apply (callee : Key) (roles : List Role)
deriving DecidableEq

/-- The operations of a role program, as the printer of a typed program writes them: a
role's part of an event is its `Part` with the located type of what it has afterwards. -/
inductive RoleRaw (V : Vocabulary) where
  | compute (roles : List Role) (o : LocalRaw V)
  | absent (items : List (LTy V))
  | effect (part : Part V) (result : LTy V)
  | keep (holders : Holders)
  | apply (callee : Key) (roles : List Role)
deriving DecidableEq

/-- A definition by names. The body's inputs are its ports. Function headers retain positional clauses
and expressions over input and result positions. -/
inductive Definition (V : Vocabulary) where
  | fn (key : Key) (ins outs : List V.Ty) (canStop : Bool) (kernel : Option Key)
      (summary : HeaderSummary V) (body : Region (LocalRaw V) Unit)
      (notes : BodyAnalysis.Annotations (LocalRaw V) := [])
  | protocol (key : Key) (roles : Nat) (ins outs : List (LTy V))
      (body : Region (ProtocolRaw V) (List Role))
  deriving DecidableEq

/-- The key of a definition by names. -/
def Definition.key {V : Vocabulary} : Definition V → Key
  | .fn key .. => key
  | .protocol key .. => key

/-- A program by names: its definitions in order, each applying only earlier ones. -/
structure NamedProgram (V : Vocabulary) where
  definitions : List (Definition V)
  deriving DecidableEq

/-- A refusal of a program: of a function, with its types and its written operations as
values. -/
abbrev ProgramRefusal (V : Vocabulary) : Type := Refusal V.Ty (LocalRaw V)

/-- The rule, location and dialect-specific payload of a named definition failure. -/
inductive DefinitionRefusal (V : Vocabulary) where
  | fn (refusal : ProgramRefusal V)
  | protocol (refusal : Refusal (LTy V) (ProtocolRaw V))
deriving DecidableEq

/-- The typed diagnostic from definition checking, a particular role projection, or association resolution. -/
inductive AdmissionRefusal (V : Vocabulary) where
  | definition (refusal : DefinitionRefusal V)
  | projection (refusal : Refusal (LTy V) (RoleRaw V))
  | association (refusal : ProgramRefusal V)
deriving DecidableEq

end Zkc.Core
