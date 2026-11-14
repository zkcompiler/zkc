module

public import Zkc.Core.Keys

public section

/-! The named program: what a producer hands the core.

A value is a name, a number unique in its definition. Local code is instructions over names;
a nested region names its own inputs and reads the names around it. In a protocol body a name
stands for one value per holder, and its holders are fixed where it is bound:

- `compute roles steps`: each result of the steps is held by `roles`; every role performs
  the steps, in order, on its copies;
- `exchange`: the result is held by the sender, whose copy is the value sent, and by the
  receiver;
- `draw`: the result is held by the owner and the receivers; `sample`: by the owner;
- `apply`: one result per result port of the callee, held by the roles that its holders are
  mapped to;
- `choose`, `repeat`, `block`: the results have the holders that the operation states;
- `join`: the result is held by the roles of the copies it joins.

A port is stated once with its holders. Every instruction carries the producer's tag, which
a refusal names. A named program states no position, no capture, no copy per role, no site
number and no maximum of a protocol loop: the lowering (`Zkc.Core.Lower`) makes them.

The tables of a named package (types, declarations, rows) are those of the raw package, and
types are in their raw form.
-/

set_option autoImplicit false

namespace Zkc.Core.Named

/-- A value of a definition: a number unique in the definition. -/
abbrev ValueName := Nat

/-- The producer's tag of an instruction: what a refusal names. -/
abbrev Tag := Nat

/-- How a region ends. -/
inductive Exit where
  | ret (values : List ValueName)
  | stop (reason : PIR.Stop)
  deriving Repr, Inhabited

/-- The count of a loop: a number of the operation, or a value. -/
inductive Count where
  | static (count : Nat)
  | runtime (value : ValueName)
  deriving Repr, Inhabited

mutual
  /-- A local operation. -/
  inductive LocalOp where
    | op (row : Nat) (operands : List ValueName)
    | call (callee : Nat) (operands : List ValueName)
    /-- Two regions without inputs of their own: the region of `true`, then of `false`. -/
    | conditional (condition : ValueName) (outputs : List Ty) (onTrue onFalse : Region)
    /-- One region per alternative, whose one input is the payload. -/
    | «match» (declaration : Nat) (value : ValueName) (outputs : List Ty) (arms : List Region)
    /-- One region whose inputs are the iteration number and then the carried values; it
    returns one value per collected type and then the carried values. `carried` are the values
    before the first iteration. The results are the collections and then the carried values. A
    local loop over a value may state a maximum. -/
    | loop (count : Count) (maximum : Option Nat) (carried : List ValueName) (collected : List Ty)
        (body : Region)
    | guard (reason : Reason) (condition : ValueName)
    | literal (value : Raw.Literal)
    | builtin (operation : Raw.Builtin) (operands : List ValueName)
    /-- A region over the names around it, with stated output types; its results are what it
    returns. -/
    | block (outputs : List Ty) (body : Region)

  /-- A local operation, the names of its results, and the producer's tag. -/
  inductive Instruction where
    | mk (tag : Tag) (results : List ValueName) (step : LocalOp)

  /-- A local region: the names of its own inputs, its instructions, and how it ends. -/
  inductive Region where
    | mk (inputs : List ValueName) (instructions : List Instruction) (exit : Exit)
end

instance : Inhabited Region := ⟨.mk [] [] (.ret [])⟩

/-- A value that an operation of a protocol body gives, as a type and the roles that hold
it. -/
structure Output where
  type : Ty
  holders : List Nat
  deriving Repr, Inhabited

/-- A site of a protocol body: its key, and its name in the table of names. -/
structure Site where
  key : SiteKey
  name : String
  deriving Repr, Inhabited

mutual
  /-- An operation of a protocol body. -/
  inductive ProtocolOp where
    /-- Each role performs the local instructions, in order, on its own copies of the values
    they read; every name they bind is held by the roles. The instructions of a statement are
    one sequence: a role performs the whole of it before the next role does. The instruction
    that carries a `compute` names no result of its own. -/
    | compute (roles : List Nat) (steps : List Instruction)
    | exchange (sender receiver : Nat) (site : Site) (value : ValueName)
    | draw (owner : Nat) (receivers : List Nat) (site : Site) (law : Nat)
        (operands : List ValueName)
    | sample (owner : Nat) (site : Site) (law : Nat) (operands : List ValueName)
    /-- A choice of the participants on a value that each holds. On a condition: the region
    of `true`, then of `false`, without inputs. On a variant: one region per alternative, whose
    one input is the payload, held by every participant. -/
    | choose (participants : List Nat) (subject : ValueName) (tag : ChoiceTag)
        (outputs : List Output) (arms : List ProtocolRegion)
    /-- A loop of the participants. The inputs of the region are the iteration number, held
    by every participant, and then the carried values; it returns one value per collected
    entry and then the carried values. `carried` are the values before the first iteration,
    each with its holders. The results are the collections and then the carried values. -/
    | «repeat» (participants : List Nat) (count : Count)
        (carried : List (ValueName × List Nat)) (collected : List Output) (body : ProtocolRegion)
    /-- The caller's roles `roleMap[0], roleMap[1], …` run an earlier protocol: one operand per
    port, one result per result. -/
    | apply (callee : Nat) (roleMap : List Nat) (site : Site) (operands : List ValueName)
    /-- A region over the names around it: a program point. Its results are what it
    returns. -/
    | block (point : PointKey) (outputs : List Output) (body : ProtocolRegion)
    /-- Copies that the producer says are one value: the result is held by the roles of the
    copies, and its copy at each role is the value named there. It makes no instruction; that
    the copies are one value is for the check of copies to find where the program needs it. -/
    | join (copies : List (ValueName × Nat))

  inductive ProtocolInstruction where
    | mk (tag : Tag) (results : List ValueName) (step : ProtocolOp)

  inductive ProtocolRegion where
    | mk (inputs : List ValueName) (instructions : List ProtocolInstruction) (exit : Exit)
end

instance : Inhabited ProtocolRegion := ⟨.mk [] [] (.ret [])⟩

/-- A function. The inputs of its body are named by the body. -/
structure Function where
  specificationOnly : Bool
  inputs : List Ty
  outputs : List Ty
  body : Option Region
  deriving Inhabited

/-- A protocol. A port is stated once with its holders; the inputs of the body name the
ports, and the body returns one name per result. -/
structure Protocol where
  specificationOnly : Bool
  roles : Nat
  inputs : List Output
  outputs : List Output
  body : ProtocolRegion
  deriving Inhabited

/-- A named package: the tables of a raw package, and named definitions. `names` gives the
names of the functions, of the protocols and of their roles; the names of the sites are
those of the events. -/
structure Package where
  types : List CatalogueRow
  records : List RecordDeclaration
  variants : List VariantDeclaration
  operations : List Operation
  functions : List Function
  protocols : List Protocol
  functionNames : List String
  protocolNames : List String
  roleNames : List (List String)
  deriving Inhabited

end Zkc.Core.Named
