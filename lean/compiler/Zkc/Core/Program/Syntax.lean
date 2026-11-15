module

public import Zkc.Core.Program.Shape
public import Zkc.Core.Program.Located

@[expose] public section

/-!
The program by names: what a frontend gives to the core.

One first-order syntax, generic in the operation and in who performs. A region is a list of
instructions and an exit. An instruction is an operation (its results, the operation, its
operands) or one of the forms of control (a guard, a choice, a case analysis, a loop, a
block, an attempt), each with its key and its nested regions; the control is written once here, and a
dialect lists only its operations. The key is the producer's: it is the key of the event, the
block or the application that the instruction is. A name is a number, resolved lexically: the
latest binding in scope. A nested region sees the names around it.
-/

namespace Zkc.Core

abbrev Name := Nat

/-- How often a loop runs, by names: a written number of times, or as often as the value of a
name says. -/
inductive Repeat where
  | fixed (n : Nat)
  | count (name : Name)
deriving DecidableEq, Repr

mutual
  /-- An instruction by names. `Who` is who performs a form of control: nobody in a function,
  roles in a protocol or a role program. The region of a loop has the iteration number and
  the carried values as its inputs, and exits with the carried values and one value of each
  collected type; the loop's results are the last carried values and the collections. -/
  inductive Instruction (Op Who : Type) where
    | op (key : Key) (results : List Name) (o : Op) (operands : List Name)
    | guard (key : Key) (who : Who) (condition : Name) (why : Reason)
    | choose (key : Key) (who : Who) (condition : Name) (results : List Name)
        (onTrue onFalse : Region Op Who)
    | cases (key : Key) (who : Who) (subject : Name) (results : List Name)
        (arms : List (Region Op Who))
    | loop (key : Key) (who : Who) (times : Repeat) (carried : List Name) (results : List Name)
        (body : Region Op Who)
    | block (key : Key) (number : Nat) (results : List Name) (body : Region Op Who)
    /-- An attempt that `who` own: the input of its body is the number of the attempt; the
    results are what the body exits with. -/
    | attempt (key : Key) (who : Who) (results : List Name) (body : Region Op Who)
  inductive Region (Op Who : Type) where
    | mk (inputs : List Name) (body : List (Instruction Op Who)) (exit : List Name)
end

/-- An operation that the core owns, by name. -/
inductive OwnedName where
  | natAdd | natSub | natLe | boolNot | seqLength | seqAt | make | take | inject
deriving DecidableEq, Repr

/-- The operations of a function. An owned operation carries its types and its static
naturals (the position of `inject`). -/
inductive LocalRaw (V : Vocabulary) where
  | row (key : V.RowKey) (statics : List Static)
  | owned (name : OwnedName) (at_ : List V.Ty) (statics : List Nat)
  | literal (τ : V.Ty) (data : List Nat)
  | call (callee : Key)
deriving DecidableEq

/-- The operations of a protocol. Who computes, who takes part in an event (its class, with
its type) and who keeps a narrowed value is written; the holders of every value follow. -/
inductive ProtocolRaw (V : Vocabulary) where
  | compute (roles : List Role) (o : LocalRaw V)
  | event (cls : EventClass V) (τ : V.Ty)
  | narrow (roles : List Role)
  | apply (callee : Key) (roles : List Role)

/-- The operations of a role program, as the printer of a typed program writes them: a
role's part of an event is its `Part` with the located type of what it has afterwards. -/
inductive RoleRaw (V : Vocabulary) where
  | compute (roles : List Role) (o : LocalRaw V)
  | absent (items : List (LTy V))
  | effect (part : Part V) (result : LTy V)
  | keep (holders : Holders)
  | apply (callee : Key) (roles : List Role)

/-- A definition by names. The body's inputs are its ports. -/
inductive Definition (V : Vocabulary) where
  | fn (key : Key) (ins outs : List V.Ty) (canStop : Bool) (kernel : Option Key)
      (body : Region (LocalRaw V) Unit)
  | protocol (key : Key) (roles : Nat) (ins outs : List (LTy V))
      (body : Region (ProtocolRaw V) (List Role))

/-- The key of a definition by names. -/
def Definition.key {V : Vocabulary} : Definition V → Key
  | .fn key .. => key
  | .protocol key .. => key

/-- A program by names: its definitions in order, each applying only earlier ones. -/
structure NamedProgram (V : Vocabulary) where
  definitions : List (Definition V)

end Zkc.Core
