module

public import Zkc.Core.Meaning

public section

/-! Raw positional syntax of one program.

Every reference is a number. A value is named by its number in its region: the inputs
first, then the results of each instruction, in the order they are bound. An operation
row is named by its position in the table, a function by its position among the
functions and a protocol by its position among the protocols. The simple data of the
typed model (types, located types, reasons, kinds, catalogue rows) is reused, with one
difference: a record or a variant type names its declaration by its number only. Its raw
form is `Ty.strip`; elaboration reads the use and the shape from the package's
declarations (`Ty.fill`), and the use and shape that a raw declared type carries are not
read. A literal is not reused: a typed `fin` literal is below its bound and a typed byte
below 256, and the raw literal is the numbers that elaboration checks.

A program is its functions followed by its protocols. A function may call the functions
before it; a protocol may call every function and apply the protocols before it.

`conditional` and `choose` state their output types, a `loop` states the types it
collects, and `block` is a nested region over the whole surrounding context with stated
output types, the syntax of `Region.bind`. With these every typed term has exactly one
raw syntax.
-/

set_option autoImplicit false

namespace Zkc.Core

/-! ## Declared types by number -/

mutual
  /-- The raw form of a type: a record or a variant names its declaration by its number
  only. -/
  @[expose] def Ty.strip : Ty → Ty
    | .bool => .bool
    | .nat => .nat
    | .fin bound => .fin bound
    | .nominal row => .nominal row
    | .seq element size => .seq (Ty.strip element) size
    | .tuple components => .tuple (Ty.stripAll components)
    | .record declaration _ _ => .record declaration .free []
    | .variant declaration _ => .variant declaration []

  @[expose] def Ty.stripAll : List Ty → List Ty
    | [] => []
    | type :: rest => Ty.strip type :: Ty.stripAll rest
end

mutual
  /-- The type that a raw type stands for in a type table: a record or a variant has the
  use and the shape of its declaration. Nothing when it names an undeclared one. -/
  @[expose] def Ty.fill (typeTable : TypeTable) : Ty → Option Ty
    | .bool => some .bool
    | .nat => some .nat
    | .fin bound => some (.fin bound)
    | .nominal row => some (.nominal row)
    | .seq element size =>
        match Ty.fill typeTable element with
        | some element => some (.seq element size)
        | none => none
    | .tuple components =>
        match Ty.fillAll typeTable components with
        | some components => some (.tuple components)
        | none => none
    | .record declaration _ _ =>
        match typeTable.records[declaration]? with
        | some found => some (.record declaration found.use found.fields)
        | none => none
    | .variant declaration _ =>
        match typeTable.variants[declaration]? with
        | some found => some (.variant declaration found.alternatives)
        | none => none

  @[expose] def Ty.fillAll (typeTable : TypeTable) : List Ty → Option (List Ty)
    | [] => some []
    | type :: rest =>
        match Ty.fill typeTable type, Ty.fillAll typeTable rest with
        | some type, some rest => some (type :: rest)
        | _, _ => none
end

/-- The raw form of the tag of a choice: a variant names its declaration by its number
only. -/
@[expose] def ChoiceTag.strip : ChoiceTag → ChoiceTag
  | .condition => .condition
  | .arm count => .arm count
  | .alternative declaration _ => .alternative declaration []

/-- The tag that a raw tag stands for in a type table: a variant has the alternatives of
its declaration. Nothing when it names an undeclared one. -/
@[expose] def ChoiceTag.fill (typeTable : TypeTable) : ChoiceTag → Option ChoiceTag
  | .condition => some .condition
  | .arm count => some (.arm count)
  | .alternative declaration _ =>
      match typeTable.variants[declaration]? with
      | some found => some (.alternative declaration found.alternatives)
      | none => none

/-- The raw form of a located type. -/
@[expose] def Located.strip (located : Located) : Located := ⟨located.type.strip, located.holder⟩

@[expose] def Located.stripAll : List Located → List Located
  | [] => []
  | located :: rest => located.strip :: Located.stripAll rest

/-- The located types that raw ones stand for. -/
@[expose] def Located.fillAll (typeTable : TypeTable) : List Located → Option (List Located)
  | [] => some []
  | located :: rest =>
      match Ty.fill typeTable located.type, Located.fillAll typeTable rest with
      | some type, some rest => some (⟨type, located.holder⟩ :: rest)
      | _, _ => none

namespace Raw

/-- A literal as written. A `fin` literal and the bytes of a `bytes` literal are numbers
that elaboration checks against their bounds. -/
inductive Literal where
  | nat (value : Nat)
  | bool (value : Bool)
  | fin (bound value : Nat)
  | nominal (row : Nat) (data : List Nat)
  | bytes (data : List Nat)
  deriving Repr, Inhabited, DecidableEq

/-- An operation the core owns, as written: the operation and its static data. A position
among the components of a tuple or the alternatives of a variant is a number, and the
bounds of a widening are numbers; elaboration checks them. -/
inductive Builtin where
  | natAdd | natMul | natPow | natEqual | natLess | natSub | natDiv | natRem
  | boolAnd | boolOr | boolNot | boolEqual
  | seqLength (element : Ty) (size : Option Nat)
  | seqAt (element : Ty) (size : Option Nat)
  | seqSlice (element : Ty) (size result : Option Nat)
  | seqConcat (element : Ty) (left right : Option Nat)
  | seqFill (element : Ty) (count : Nat)
  | seqMake (element : Ty) (count : Nat)
  | seqSized (element : Ty) (size : Nat)
  | seqUnsized (element : Ty) (size : Nat)
  | natBelow (bound : Nat)
  | finToNat (bound : Nat)
  | finWiden (bound wider : Nat)
  | tupleMake (components : List Ty)
  | tupleGet (components : List Ty) (position : Nat)
  | recordMake (declaration : Nat)
  | recordGet (declaration position : Nat)
  | variantMake (declaration position : Nat)
  deriving Repr, Inhabited, DecidableEq

/-- The name the reference gives an operation the core owns. A tuple and a sized sequence
are both made by `local.make`; a widening has a name of its own, since the reference names
none. -/
def Builtin.name : Builtin → String
  | .natAdd => "nat.add" | .natMul => "nat.mul" | .natPow => "nat.pow"
  | .natEqual => "nat.equal" | .natLess => "nat.less" | .natSub => "nat.sub"
  | .natDiv => "nat.div" | .natRem => "nat.rem"
  | .boolAnd => "bool.and" | .boolOr => "bool.or" | .boolNot => "bool.not"
  | .boolEqual => "bool.equal"
  | .seqLength .. => "seq.length" | .seqAt .. => "seq.at" | .seqSlice .. => "seq.slice"
  | .seqConcat .. => "seq.concat" | .seqFill .. => "seq.fill" | .seqSized .. => "seq.sized"
  | .seqUnsized .. => "seq.unsized" | .natBelow _ => "nat.below" | .finToNat _ => "fin.to_nat"
  | .finWiden .. => "fin.widen" | .seqMake .. | .tupleMake _ | .recordMake _ => "local.make"
  | .tupleGet .. | .recordGet .. => "local.get" | .variantMake .. => "local.variant"

/-- The names of the operations the core owns. No row of an operation table has one. -/
def builtinNames : List String :=
  ["nat.add", "nat.sub", "nat.mul", "nat.div", "nat.rem", "nat.pow", "nat.equal", "nat.less",
   "bool.and", "bool.or", "bool.not", "bool.equal", "seq.length", "seq.at", "seq.slice",
   "seq.concat", "seq.fill", "seq.sized", "seq.unsized", "nat.below", "fin.to_nat",
   "fin.widen", "local.make", "local.get", "local.variant"]

/-- The operation of a name whose static data are none. -/
def Builtin.plain? : String → Option Builtin
  | "nat.add" => some .natAdd | "nat.mul" => some .natMul | "nat.pow" => some .natPow
  | "nat.equal" => some .natEqual | "nat.less" => some .natLess | "nat.sub" => some .natSub
  | "nat.div" => some .natDiv | "nat.rem" => some .natRem
  | "bool.and" => some .boolAnd | "bool.or" => some .boolOr | "bool.not" => some .boolNot
  | "bool.equal" => some .boolEqual
  | _ => none

/-- How the count of a raw `loop` is given: a number of the instruction, or the number of
a value with an optional maximum. -/
inductive LoopCount where
  | static (count : Nat)
  | runtime (maximum : Option Nat) (value : Nat)
  deriving Repr, Inhabited, DecidableEq

/-- The count of the typed operation. -/
@[expose] def LoopCount.typed : LoopCount → Zkc.Core.LoopCount
  | .static count => .static count
  | .runtime maximum _ => .runtime maximum

/-- The count operand: none for a count of the instruction. -/
@[expose] def LoopCount.operands : LoopCount → List Nat
  | .static _ => []
  | .runtime _ value => [value]

mutual
  /-- One local instruction. Operands are value numbers. -/
  inductive LocalStep where
    | op (row : Nat) (operands : List Nat)
    | call (callee : Nat) (operands : List Nat)
    | conditional (condition : Nat) (captures : List Nat) (outputs : List Ty)
        (onTrue onFalse : LocalRegion)
    /-- `match` on a value of the variant `declaration`: one region per alternative, in
    order, from its payload and the captures. -/
    | «match» (declaration value : Nat) (captures : List Nat) (outputs : List Ty)
        (arms : LocalArms)
    /-- `loop`: the count, the carried values, the captures, the types of the values that
    each iteration collects, and the region. -/
    | loop (count : LoopCount) (carried captures : List Nat) (collected : List Ty)
        (body : LocalRegion)
    | guard (reason : Reason) (condition : Nat)
    | literal (value : Literal)
    | builtin (operation : Builtin) (operands : List Nat)

  /-- A local region: instructions, then the returned values or a `stop`. -/
  inductive LocalRegion where
    | ret (values : List Nat)
    | stop (reason : PIR.Stop)
    | step (instruction : LocalStep) (next : LocalRegion)
    | block (outputs : List Ty) (body next : LocalRegion)

  /-- The regions of a `match`, one per alternative. -/
  inductive LocalArms where
    | none
    | arm (region : LocalRegion) (rest : LocalArms)
end

/-- The `bool` that an instruction is the literal of. -/
@[expose] def LocalStep.literalBool : LocalStep → Option Bool
  | .literal (.bool value) => some value
  | _ => none

/-- A region returns one value, the one with the given number, and does nothing else. -/
@[expose] def LocalRegion.returnsOnly (number : Nat) : LocalRegion → Bool
  | .ret [returned] => Nat.beq returned number
  | _ => false

/-- The `bool` literal that a region with `inputs` inputs returns, when the region is one
`literal` instruction of a `bool` and the return of that one value: the form that the check
of facts reads in the regions of an `if`. The result of the first instruction of a region
has the number of the region's inputs. -/
@[expose] def LocalRegion.literalBool (inputs : Nat) : LocalRegion → Option Bool
  | .step instruction next => cond (next.returnsOnly inputs) instruction.literalBool none
  | _ => none

/-- The arms with the given regions. -/
@[expose] def LocalArms.ofList : List LocalRegion → LocalArms
  | [] => .none
  | region :: rest => .arm region (ofList rest)

/-- The regions of the arms. -/
def LocalArms.toList : LocalArms → List LocalRegion
  | .none => []
  | .arm region rest => region :: rest.toList

/-- How the count of a raw `repeat` is given: a number of the instruction, or the maximum
and the numbers of the values that the participants hold, in their order. -/
inductive RepeatCount where
  | static (count : Nat)
  | runtime (maximum : Nat) (counts : List Nat)
  deriving Repr, Inhabited, DecidableEq

/-- The count of the typed operation. -/
@[expose] def RepeatCount.typed : RepeatCount → Zkc.Core.RepeatCount
  | .static count => .static count
  | .runtime maximum _ => .runtime maximum

/-- The count operands: none for a count of the instruction. -/
@[expose] def RepeatCount.operands : RepeatCount → List Nat
  | .static _ => []
  | .runtime _ counts => counts

mutual
  /-- One protocol instruction. -/
  inductive ProtocolStep where
    | at (role : Nat) (instruction : LocalStep)
    | exchange (sender receiver site value : Nat)
    | draw (owner : Nat) (receivers : List Nat) (site law : Nat) (operands : List Nat)
    | sample (owner site law : Nat) (operands : List Nat)
    /-- `repeat`: the participants, the count, the carried values, the captures, the located
    types of the values that each iteration collects, and the region. -/
    | repeat (participants : List Nat) (count : RepeatCount) (carried captures : List Nat)
        (collected : List Located) (body : ProtocolRegion)
    /-- `choose`: the participants, the values that hold their tags, the tag, the captures,
    the outputs and one region per value of the tag. A tag that is a variant names its
    declaration by its number only. -/
    | choose (participants tags : List Nat) (tag : ChoiceTag) (captures : List Nat)
        (outputs : List Located) (arms : ProtocolArms)
    | apply (callee : Nat) (roleMap : List Nat) (site : Nat) (operands : List Nat)

  inductive ProtocolRegion where
    | ret (values : List Nat)
    | stop (reason : PIR.Stop)
    | step (instruction : ProtocolStep) (next : ProtocolRegion)
    | block (outputs : List Located) (body next : ProtocolRegion)

  /-- The regions of a `choose`, one per arm. -/
  inductive ProtocolArms where
    | none
    | arm (region : ProtocolRegion) (rest : ProtocolArms)
end

/-- The arms with the given regions. -/
@[expose] def ProtocolArms.ofList : List ProtocolRegion → ProtocolArms
  | [] => .none
  | region :: rest => .arm region (ofList rest)

/-- The regions of the arms. -/
def ProtocolArms.toList : ProtocolArms → List ProtocolRegion
  | .none => []
  | .arm region rest => region :: rest.toList

/-- An agreement: over the outputs or the inputs, and the positions of its ports. -/
structure Agreement where
  overOutputs : Bool
  ports : List Nat
  deriving DecidableEq, Repr

/-- A function. Without a body it is known by its header only. -/
structure Function where
  specificationOnly : Bool
  inputs : List Ty
  outputs : List Ty
  body : Option LocalRegion

/-- A protocol. Its agreements list those over the inputs before those over the
outputs. -/
structure Protocol where
  specificationOnly : Bool
  roles : Nat
  inputs : List Located
  outputs : List Located
  agreements : List Agreement
  body : ProtocolRegion

/-- The side table of names. It carries no meaning. -/
structure Names where
  functions : List String
  protocols : List String
  /-- The role names of each protocol. A protocol without role names has none. -/
  roles : List (List String)
  /-- The site names of each protocol. -/
  sites : List (List String)
  deriving DecidableEq, Repr

/-- One program of a package with the package's tables and names. The declarations of
records and variants carry the shapes of their types; a type of the program names a
declaration by its number only. -/
structure Package where
  types : List CatalogueRow
  records : List RecordDeclaration
  variants : List VariantDeclaration
  operations : List Operation
  functions : List Function
  protocols : List Protocol
  names : Option Names

/-! ## Declarations as a reader gives them

A text names a declaration by its number, also inside the declarations. The raw tables
carry whole types, so a reader gives every declared type in them the use and the shape of
its declaration. This is where a declaration that contains itself is refused: no whole
type has one. -/

/-- A type with every declared type it names given the use and the shape of its
declaration. `visiting` lists the declarations being given theirs, as
`(isVariant, number)`; a declaration that names one of them contains itself. A number that
names no declaration is kept; elaboration refuses it. -/
partial def declaredType (records : Array RecordDeclaration) (variants : Array VariantDeclaration)
    (visiting : List (Bool × Nat)) : Ty → Except String Ty
  | .seq element size => return .seq (← declaredType records variants visiting element) size
  | .tuple components =>
      return .tuple (← components.mapM (declaredType records variants visiting))
  | .record declaration use fields => do
      if visiting.contains (false, declaration) then
        throw s!"record declaration {declaration} contains itself"
      match records[declaration]? with
      | some record =>
          return .record declaration record.use
            (← record.fields.mapM (declaredType records variants ((false, declaration) :: visiting)))
      | none => pure (.record declaration use fields)
  | .variant declaration alternatives => do
      if visiting.contains (true, declaration) then
        throw s!"variant declaration {declaration} contains itself"
      match variants[declaration]? with
      | some variant =>
          return .variant declaration (← variant.alternatives.mapM
            (declaredType records variants ((true, declaration) :: visiting)))
      | none => pure (.variant declaration alternatives)
  | other => pure other

/-- The tables of declarations as the raw package carries them: whole types. -/
def declaredTables (records : List RecordDeclaration) (variants : List VariantDeclaration) :
    Except String (List RecordDeclaration × List VariantDeclaration) := do
  let recordArray := records.toArray
  let variantArray := variants.toArray
  let wholeRecords ← ((List.range records.length).zip records).mapM fun (number, record) =>
    return (⟨record.use, ← record.fields.mapM
      (declaredType recordArray variantArray [(false, number)])⟩ : RecordDeclaration)
  let wholeVariants ← ((List.range variants.length).zip variants).mapM fun (number, variant) =>
    return (⟨← variant.alternatives.mapM
      (declaredType recordArray variantArray [(true, number)])⟩ : VariantDeclaration)
  return (wholeRecords, wholeVariants)

end Raw

/-- The role names of a protocol are absent or one per role. -/
def roleNames : List (List String) → List Nat → Bool
  | [], [] => true
  | names :: rest, roles :: counts =>
      (names.isEmpty || Nat.beq names.length roles) && roleNames rest counts
  | [], _ :: _ => false
  | _ :: _, [] => false

/-- The first violated condition of the name tables: one name per function and per
protocol, one list of role names and one of site names per protocol, and the role names
of a protocol absent or one per role. `roles` lists the role counts of the protocols in
order. -/
def namesViolation (names : Option Raw.Names) (functions : Nat) (roles : List Nat) :
    Option Violation :=
  match names with
  | none => none
  | some names =>
      firstViolation
        [(Nat.beq names.functions.length functions, .nameTable),
         (Nat.beq names.protocols.length roles.length, .nameTable),
         (Nat.beq names.sites.length roles.length, .nameTable),
         (roleNames names.roles roles, .nameTable)]

end Zkc.Core
