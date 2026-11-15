module

public import Zkc.Core.Program.Syntax

@[expose] public section

/-!
The rules of refusal of the core, and what a rule found, as data: the frontend words them. A
problem is a rule and what it found at an instruction of a body; a refusal (`Admission/`) is a
problem at a place of a program.
-/

namespace Zkc.Core

/-- The rules of refusal of the core: each names what a program satisfies. -/
inductive Rule where
  /-- A name is in scope. -/
  | scope
  /-- The operands of an operation have the types that it takes. -/
  | operands
  /-- An instruction names each of its results. -/
  | results
  /-- A region or a function names each of its inputs. -/
  | inputs
  /-- An operation is a row of the vocabulary at its static arguments. -/
  | row
  /-- An operation that the core owns is named with its types and its static naturals. -/
  | owned
  /-- The data of a literal reads as its type. -/
  | literal
  /-- One definition before the caller has the key of the callee. -/
  | callee
  /-- Those who guard or choose may do so on the type of the condition. -/
  | condition
  /-- The regions of a choice give the same types. -/
  | regions
  /-- Those who perform a form of control may give what it gives. -/
  | gives
  /-- The subject of a case analysis is a variant that they may choose on. -/
  | variant
  /-- A case analysis has an arm for each alternative. -/
  | arms
  /-- The arms of a case analysis give the same types. -/
  | armTypes
  /-- The body of a loop gives back the carried values. -/
  | carried
  /-- A loop repeats as often as a count that they may repeat by. -/
  | count
  /-- Who performs an attempt may own one. -/
  | attempt
  /-- The body of a definition gives the results of its header. -/
  | outputs
  /-- The instructions of a body have their own addresses. -/
  | distinct
  /-- Every value of a linear type is used once. -/
  | linear
  /-- The header of a function says whether it can stop with a reason, as its body does. -/
  | stops
  /-- No definition before a definition has its key. -/
  | key
  /-- A definition is a function: the rules of the protocol dialect are not built. -/
  | protocol
  /-- The association of a program names definitions of the program. -/
  | association
deriving DecidableEq, Repr

/-- What a rule found, with the types `T` of a dialect and its written operations `Raw` as
values. -/
inductive Detail (T Raw : Type) where
  /-- A name that is not in scope. -/
  | name (name : Name)
  /-- The types expected and the types found. -/
  | types (expected found : List T)
  /-- A type that the rule does not allow there. -/
  | type (found : T)
  /-- The number expected and the number found. -/
  | number (expected found : Nat)
  /-- A written operation that names no operation. -/
  | operation (written : Raw)
  /-- The key of a callee, and the number of definitions before the caller that have it. -/
  | callee (key : Key) (found : Nat)
  /-- Types of values of which one may not be given. -/
  | given (types : List T)
  /-- The key of a definition. -/
  | key (key : Key)
  /-- Whether the header says that the function can stop, and whether its body can. -/
  | stops (header body : Bool)
  /-- Nothing beyond the rule and the place. -/
  | nothing
deriving DecidableEq

/-- What elaboration finds wrong in a body: the rule, the blocks around the instruction and its
key when it is at one, and what the rule found. -/
structure Problem (T Raw : Type) where
  rule : Rule
  blocks : List (Key × Nat) := []
  instruction : Option Key := none
  detail : Detail T Raw

/-- A problem of a rule, at an instruction. -/
def Problem.at {T Raw : Type} (problem : Problem T Raw) (blocks : List (Key × Nat)) (key : Key) :
    Problem T Raw :=
  { problem with blocks := blocks, instruction := some key }

/-- A problem of a rule at an instruction. -/
def problemAt {T Raw : Type} (blocks : List (Key × Nat)) (key : Key) (rule : Rule)
    (detail : Detail T Raw) : Problem T Raw :=
  { rule := rule, blocks := blocks, instruction := some key, detail := detail }

/-- A problem of a rule, about a body as a whole. -/
def problemOf {T Raw : Type} (rule : Rule) (detail : Detail T Raw) : Problem T Raw :=
  { rule := rule, detail := detail }

end Zkc.Core
