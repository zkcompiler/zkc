module

public import Zkc.Core.Raw

public section

/-! The closure of an entry of a raw package.

The closure of an entry is the package of what the entry reaches, numbered anew, with
everything else dropped. A package numbers six kinds of items: nominal type rows, record
declarations, variant declarations, operation rows, functions and protocols. An item refers
to others: a type row to the type rows its `type` statics name, a declaration to what the
types of its fields or alternatives name, an operation row to what its statics and its
signature name and to its domain row, a function to what its signature names, its operation
rows, its callees and its declarations, a protocol to what its ports name and to everything
its body uses, the protocols it applies among them.

What an entry reaches is listed by a depth-first walk over the references of each item, in
the order they occur in it, in post-order: an item is listed after everything it reaches,
and once. The new number of an item is its position among the listed items of its kind.
The listing depends only on the content of what is reached, never on the numbers the
package gave it, so a definition or a row that the entry does not reach changes neither
the closure nor its numbering.

The format requires that a function call only earlier functions, that a protocol apply
only earlier protocols, that a `type` static name only earlier type rows and that a domain
row be an earlier row. Each of these references is listed before the item that makes it,
so the closure meets the four conditions, and the entry is the last item of its kind. The
declarations of records and variants have no order.

The walk carries fuel, the number of items of the package and one more: in a package
without cycles, which every well-formed package is, a path of the walk visits each item at
most once, so the fuel does not run out. An item is listed only when the package has it: a
number that names no item of its kind is renumbered to one that names none either. An item
that reaches itself, which no well-formed package has, is still listed once.

What is known of a closure is what elaboration decides of it: a closure that elaborates is
well formed. No theorem here relates the closure to the package it was taken from. It is
not proved that the closure of a package that elaborates elaborates, nor that a definition
of the closure means what it meant in the package. A statement about a definition of the
package (that it never stops `undefined`, a law of a function, a property of a protocol)
is therefore not a statement about the definition of the closure: it holds of the closure
when it is proved of the closure. The missing statement is that, for a model carried along
the renumbering (the carrier of a nominal row, the meaning of an operation row and the
meaning of a function known by its header, each at its new number), every function that
the closure keeps has the process it had on the same arguments, and every protocol the
process it had for every side, read at the renumbered types. The checks of the closures of
the fixtures compare the two on inputs, and do not replace it. -/

set_option autoImplicit false

namespace Zkc.Core

namespace Raw

/-- An item that a package numbers, by its kind and its number. -/
inductive Reference where
  | typeRow (row : Nat)
  | record (declaration : Nat)
  | variant (declaration : Nat)
  | operation (row : Nat)
  | function (number : Nat)
  | protocol (number : Nat)
  deriving DecidableEq, Repr

/-- Two references name the same item. -/
@[expose] def Reference.same : Reference → Reference → Bool
  | .typeRow first, .typeRow second => Nat.beq first second
  | .record first, .record second => Nat.beq first second
  | .variant first, .variant second => Nat.beq first second
  | .operation first, .operation second => Nat.beq first second
  | .function first, .function second => Nat.beq first second
  | .protocol first, .protocol second => Nat.beq first second
  | _, _ => false

end Raw

open Raw (Reference)

/-! ## References of types and static data -/

mutual
  /-- The items a type names, in the order they occur: a nominal row, and a record or a
  variant declaration before what the types of its shape name. A raw type carries no shape,
  a whole type carries its declaration's. -/
  @[expose] def Ty.references : Ty → List Reference
    | .bool => []
    | .nat => []
    | .fin _ => []
    | .nominal row => [.typeRow row]
    | .seq element _ => Ty.references element
    | .tuple components => Ty.referencesAll components
    | .record declaration _ fields => .record declaration :: Ty.referencesAll fields
    | .variant declaration alternatives => .variant declaration :: Ty.referencesAll alternatives

  @[expose] def Ty.referencesAll : List Ty → List Reference
    | [] => []
    | type :: rest => Ty.references type ++ Ty.referencesAll rest
end

/-- The items the types of located types name, in order. -/
@[expose] def Located.referencesAll : List Located → List Reference
  | [] => []
  | located :: rest => located.type.references ++ Located.referencesAll rest

/-- The items the `type` statics of a row name, in order. -/
@[expose] def Static.referencesAll : List Static → List Reference
  | [] => []
  | .type given :: rest => given.references ++ Static.referencesAll rest
  | _ :: rest => Static.referencesAll rest

/-- The items the tag of a choice names: a variant's declaration, then what its payload
types name. -/
@[expose] def ChoiceTag.references : ChoiceTag → List Reference
  | .condition => []
  | .arm _ => []
  | .alternative declaration alternatives => .variant declaration :: Ty.referencesAll alternatives

namespace Raw

/-- The items the static data of an operation the core owns name. -/
@[expose] def Builtin.references : Builtin → List Reference
  | .seqLength element _ => element.references
  | .seqAt element _ => element.references
  | .seqSlice element _ _ => element.references
  | .seqConcat element _ _ => element.references
  | .seqFill element _ => element.references
  | .seqMake element _ => element.references
  | .seqSized element _ => element.references
  | .seqUnsized element _ => element.references
  | .tupleMake components => Ty.referencesAll components
  | .tupleGet components _ => Ty.referencesAll components
  | .recordMake declaration => [.record declaration]
  | .recordGet declaration _ => [.record declaration]
  | .variantMake declaration _ => [.variant declaration]
  | _ => []

/-- The items a literal names: the row of a nominal literal. -/
@[expose] def Literal.references : Literal → List Reference
  | .nominal row _ => [.typeRow row]
  | _ => []

/-! ## References of regions -/

mutual
  /-- The items a local instruction names, in the order they occur in it. -/
  @[expose] def LocalStep.references : LocalStep → List Reference
    | .op row _ => [.operation row]
    | .call callee _ => [.function callee]
    | .conditional _ _ outputs onTrue onFalse =>
        Ty.referencesAll outputs ++
          (LocalRegion.references onTrue ++ LocalRegion.references onFalse)
    | .match declaration _ _ outputs arms =>
        .variant declaration :: (Ty.referencesAll outputs ++ LocalArms.references arms)
    | .loop _ _ _ collected body => Ty.referencesAll collected ++ LocalRegion.references body
    | .guard _ _ => []
    | .literal value => value.references
    | .builtin operation _ => operation.references

  /-- The items a local region names, instruction by instruction. -/
  @[expose] def LocalRegion.references : LocalRegion → List Reference
    | .ret _ => []
    | .stop _ => []
    | .step instruction next => LocalStep.references instruction ++ LocalRegion.references next
    | .block outputs body next =>
        Ty.referencesAll outputs ++ (LocalRegion.references body ++ LocalRegion.references next)

  @[expose] def LocalArms.references : LocalArms → List Reference
    | .none => []
    | .arm region rest => LocalRegion.references region ++ LocalArms.references rest
end

mutual
  /-- The items a protocol instruction names, in the order they occur in it. -/
  @[expose] def ProtocolStep.references : ProtocolStep → List Reference
    | .at _ instruction => instruction.references
    | .exchange _ _ _ _ => []
    | .draw _ _ _ law _ => [.operation law]
    | .sample _ _ law _ => [.operation law]
    | .repeat _ _ _ _ collected body =>
        Located.referencesAll collected ++ ProtocolRegion.references body
    | .choose _ _ tag _ outputs arms =>
        tag.references ++ (Located.referencesAll outputs ++ ProtocolArms.references arms)
    | .apply callee _ _ _ => [.protocol callee]

  /-- The items a protocol region names, instruction by instruction. -/
  @[expose] def ProtocolRegion.references : ProtocolRegion → List Reference
    | .ret _ => []
    | .stop _ => []
    | .step instruction next =>
        ProtocolStep.references instruction ++ ProtocolRegion.references next
    | .block outputs body next =>
        Located.referencesAll outputs ++
          (ProtocolRegion.references body ++ ProtocolRegion.references next)

  @[expose] def ProtocolArms.references : ProtocolArms → List Reference
    | .none => []
    | .arm region rest => ProtocolRegion.references region ++ ProtocolArms.references rest
end

/-! ## What an item reaches -/

/-- The package has the item: its number is below the size of its table. -/
@[expose] def Package.holds (package : Package) : Reference → Bool
  | .typeRow row => Nat.blt row package.types.length
  | .record declaration => Nat.blt declaration package.records.length
  | .variant declaration => Nat.blt declaration package.variants.length
  | .operation row => Nat.blt row package.operations.length
  | .function number => Nat.blt number package.functions.length
  | .protocol number => Nat.blt number package.protocols.length

/-- The items that one item of a package names directly, in the order they occur in it:

- a type row: what its `type` statics name;
- a record or a variant declaration: what the types of its fields or alternatives name;
- an operation row: what its statics, its inputs and its outputs name, then its domain row;
- a function: what its inputs and its outputs name, then what its body names;
- a protocol: what its input and output ports name, then what its body names.

An item the package does not have names nothing. -/
@[expose] def Package.references (package : Package) : Reference → List Reference
  | .typeRow row =>
      match package.types[row]? with
      | some found => Static.referencesAll found.statics
      | none => []
  | .record declaration =>
      match package.records[declaration]? with
      | some found => Ty.referencesAll found.fields
      | none => []
  | .variant declaration =>
      match package.variants[declaration]? with
      | some found => Ty.referencesAll found.alternatives
      | none => []
  | .operation row =>
      match package.operations[row]? with
      | some found =>
          Static.referencesAll found.identity.statics ++
            (Ty.referencesAll found.signature.inputs ++
              (Ty.referencesAll found.signature.outputs ++
                match found.signature.kind with
                | .restricted (some domain) => [.operation domain]
                | _ => []))
      | none => []
  | .function number =>
      match package.functions[number]? with
      | some found =>
          Ty.referencesAll found.inputs ++
            (Ty.referencesAll found.outputs ++
              match found.body with
              | some body => body.references
              | none => [])
      | none => []
  | .protocol number =>
      match package.protocols[number]? with
      | some found =>
          Located.referencesAll found.inputs ++
            (Located.referencesAll found.outputs ++ found.body.references)
      | none => []

/-- The number of items of a package. -/
@[expose] def Package.itemCount (package : Package) : Nat :=
  package.types.length + package.records.length + package.variants.length +
    package.operations.length + package.functions.length + package.protocols.length

/-- The listing extended by what an item reaches, in post-order: an item the package has
and that is not listed yet is listed after everything it reaches. Each step down the walk
takes one unit of fuel. -/
@[expose] def Package.reach (package : Package) : Nat → Reference → List Reference →
    List Reference
  | 0, _, listed => listed
  | fuel + 1, item, listed =>
      if !package.holds item || listed.any item.same then listed
      else
        let below := (package.references item).foldl
          (fun listed reference => package.reach fuel reference listed) listed
        if below.any item.same then below else below ++ [item]

/-- What a list of roots reaches, in post-order, the roots in their order. -/
@[expose] def Package.reached (package : Package) (roots : List Reference) : List Reference :=
  roots.foldl (fun listed root => package.reach (package.itemCount + 1) root listed) []

/-! ## Numbering anew -/

/-- The old numbers of the reached items of each kind, in their new order: the new number
of an item is the position of its old number in the list of its kind. -/
structure Renumbering where
  typeRows : List Nat
  records : List Nat
  variants : List Nat
  operations : List Nat
  functions : List Nat
  protocols : List Nat
  deriving DecidableEq, Repr

/-- The position of a number in a list: the new number of an old one. A number that is not
in the list has the length of the list, a number that names nothing. -/
@[expose] def positionIn : List Nat → Nat → Nat
  | [], _ => 0
  | first :: rest, old => if Nat.beq first old then 0 else positionIn rest old + 1

@[expose] def Reference.typeRow? : Reference → Option Nat
  | .typeRow row => some row
  | _ => none

@[expose] def Reference.record? : Reference → Option Nat
  | .record declaration => some declaration
  | _ => none

@[expose] def Reference.variant? : Reference → Option Nat
  | .variant declaration => some declaration
  | _ => none

@[expose] def Reference.operation? : Reference → Option Nat
  | .operation row => some row
  | _ => none

@[expose] def Reference.function? : Reference → Option Nat
  | .function number => some number
  | _ => none

@[expose] def Reference.protocol? : Reference → Option Nat
  | .protocol number => some number
  | _ => none

/-- The numbering of a listing: each kind in the order of the listing. -/
@[expose] def Renumbering.of (reached : List Reference) : Renumbering :=
  ⟨reached.filterMap Reference.typeRow?, reached.filterMap Reference.record?,
    reached.filterMap Reference.variant?, reached.filterMap Reference.operation?,
    reached.filterMap Reference.function?, reached.filterMap Reference.protocol?⟩

end Raw

open Raw (Renumbering positionIn)

mutual
  /-- A type with every number it holds renumbered, the shape it carries included. -/
  @[expose] def Ty.renumber (renumbering : Renumbering) : Ty → Ty
    | .bool => .bool
    | .nat => .nat
    | .fin bound => .fin bound
    | .nominal row => .nominal (positionIn renumbering.typeRows row)
    | .seq element size => .seq (Ty.renumber renumbering element) size
    | .tuple components => .tuple (Ty.renumberAll renumbering components)
    | .record declaration use fields =>
        .record (positionIn renumbering.records declaration) use
          (Ty.renumberAll renumbering fields)
    | .variant declaration alternatives =>
        .variant (positionIn renumbering.variants declaration)
          (Ty.renumberAll renumbering alternatives)

  @[expose] def Ty.renumberAll (renumbering : Renumbering) : List Ty → List Ty
    | [] => []
    | type :: rest => Ty.renumber renumbering type :: Ty.renumberAll renumbering rest
end

@[expose] def Located.renumber (renumbering : Renumbering) (located : Located) : Located :=
  ⟨located.type.renumber renumbering, located.holder⟩

@[expose] def Static.renumber (renumbering : Renumbering) : Static → Static
  | .type given => .type (given.renumber renumbering)
  | .domain name => .domain name
  | .nat value => .nat value

@[expose] def CatalogueRow.renumber (renumbering : Renumbering) (row : CatalogueRow) :
    CatalogueRow :=
  ⟨row.name, row.statics.map (Static.renumber renumbering)⟩

@[expose] def OperationKind.renumber (renumbering : Renumbering) : OperationKind → OperationKind
  | .restricted (some domain) => .restricted (some (positionIn renumbering.operations domain))
  | .restricted none => .restricted none
  | .pure => .pure
  | .sampling => .sampling

@[expose] def Operation.renumber (renumbering : Renumbering) (row : Operation) : Operation :=
  ⟨row.identity.renumber renumbering,
    ⟨Ty.renumberAll renumbering row.signature.inputs,
      Ty.renumberAll renumbering row.signature.outputs,
      row.signature.kind.renumber renumbering⟩⟩

@[expose] def RecordDeclaration.renumber (renumbering : Renumbering)
    (declaration : RecordDeclaration) : RecordDeclaration :=
  ⟨declaration.use, Ty.renumberAll renumbering declaration.fields⟩

@[expose] def VariantDeclaration.renumber (renumbering : Renumbering)
    (declaration : VariantDeclaration) : VariantDeclaration :=
  ⟨Ty.renumberAll renumbering declaration.alternatives⟩

@[expose] def ChoiceTag.renumber (renumbering : Renumbering) : ChoiceTag → ChoiceTag
  | .condition => .condition
  | .arm count => .arm count
  | .alternative declaration alternatives =>
      .alternative (positionIn renumbering.variants declaration)
        (Ty.renumberAll renumbering alternatives)

namespace Raw

@[expose] def Builtin.renumber (renumbering : Renumbering) : Builtin → Builtin
  | .seqLength element size => .seqLength (element.renumber renumbering) size
  | .seqAt element size => .seqAt (element.renumber renumbering) size
  | .seqSlice element size result => .seqSlice (element.renumber renumbering) size result
  | .seqConcat element left right => .seqConcat (element.renumber renumbering) left right
  | .seqFill element count => .seqFill (element.renumber renumbering) count
  | .seqMake element count => .seqMake (element.renumber renumbering) count
  | .seqSized element size => .seqSized (element.renumber renumbering) size
  | .seqUnsized element size => .seqUnsized (element.renumber renumbering) size
  | .tupleMake components => .tupleMake (Ty.renumberAll renumbering components)
  | .tupleGet components position =>
      .tupleGet (Ty.renumberAll renumbering components) position
  | .recordMake declaration => .recordMake (positionIn renumbering.records declaration)
  | .recordGet declaration position =>
      .recordGet (positionIn renumbering.records declaration) position
  | .variantMake declaration position =>
      .variantMake (positionIn renumbering.variants declaration) position
  | .natAdd => .natAdd
  | .natMul => .natMul
  | .natPow => .natPow
  | .natEqual => .natEqual
  | .natLess => .natLess
  | .natSub => .natSub
  | .natDiv => .natDiv
  | .natRem => .natRem
  | .boolAnd => .boolAnd
  | .boolOr => .boolOr
  | .boolNot => .boolNot
  | .boolEqual => .boolEqual
  | .natBelow bound => .natBelow bound
  | .finToNat bound => .finToNat bound
  | .finWiden bound wider => .finWiden bound wider

@[expose] def Literal.renumber (renumbering : Renumbering) : Literal → Literal
  | .nominal row data => .nominal (positionIn renumbering.typeRows row) data
  | .nat value => .nat value
  | .bool value => .bool value
  | .fin bound value => .fin bound value
  | .bytes data => .bytes data

mutual
  @[expose] def LocalStep.renumber (renumbering : Renumbering) : LocalStep → LocalStep
    | .op row operands => .op (positionIn renumbering.operations row) operands
    | .call callee operands => .call (positionIn renumbering.functions callee) operands
    | .conditional condition captures outputs onTrue onFalse =>
        .conditional condition captures (Ty.renumberAll renumbering outputs)
          (LocalRegion.renumber renumbering onTrue) (LocalRegion.renumber renumbering onFalse)
    | .match declaration value captures outputs arms =>
        .match (positionIn renumbering.variants declaration) value captures
          (Ty.renumberAll renumbering outputs) (LocalArms.renumber renumbering arms)
    | .loop count carried captures collected body =>
        .loop count carried captures (Ty.renumberAll renumbering collected)
          (LocalRegion.renumber renumbering body)
    | .guard reason condition => .guard reason condition
    | .literal value => .literal (value.renumber renumbering)
    | .builtin operation operands => .builtin (operation.renumber renumbering) operands

  @[expose] def LocalRegion.renumber (renumbering : Renumbering) : LocalRegion → LocalRegion
    | .ret values => .ret values
    | .stop reason => .stop reason
    | .step instruction next =>
        .step (LocalStep.renumber renumbering instruction) (LocalRegion.renumber renumbering next)
    | .block outputs body next =>
        .block (Ty.renumberAll renumbering outputs) (LocalRegion.renumber renumbering body)
          (LocalRegion.renumber renumbering next)

  @[expose] def LocalArms.renumber (renumbering : Renumbering) : LocalArms → LocalArms
    | .none => .none
    | .arm region rest =>
        .arm (LocalRegion.renumber renumbering region) (LocalArms.renumber renumbering rest)
end

mutual
  @[expose] def ProtocolStep.renumber (renumbering : Renumbering) : ProtocolStep → ProtocolStep
    | .at role instruction => .at role (instruction.renumber renumbering)
    | .exchange sender receiver site value => .exchange sender receiver site value
    | .draw owner receivers site law operands =>
        .draw owner receivers site (positionIn renumbering.operations law) operands
    | .sample owner site law operands =>
        .sample owner site (positionIn renumbering.operations law) operands
    | .repeat participants count carried captures collected body =>
        .repeat participants count carried captures
          (collected.map (Located.renumber renumbering))
          (ProtocolRegion.renumber renumbering body)
    | .choose participants tags tag captures outputs arms =>
        .choose participants tags (tag.renumber renumbering) captures
          (outputs.map (Located.renumber renumbering)) (ProtocolArms.renumber renumbering arms)
    | .apply callee roleMap site operands =>
        .apply (positionIn renumbering.protocols callee) roleMap site operands

  @[expose] def ProtocolRegion.renumber (renumbering : Renumbering) :
      ProtocolRegion → ProtocolRegion
    | .ret values => .ret values
    | .stop reason => .stop reason
    | .step instruction next =>
        .step (ProtocolStep.renumber renumbering instruction)
          (ProtocolRegion.renumber renumbering next)
    | .block outputs body next =>
        .block (outputs.map (Located.renumber renumbering))
          (ProtocolRegion.renumber renumbering body) (ProtocolRegion.renumber renumbering next)

  @[expose] def ProtocolArms.renumber (renumbering : Renumbering) : ProtocolArms → ProtocolArms
    | .none => .none
    | .arm region rest =>
        .arm (ProtocolRegion.renumber renumbering region) (ProtocolArms.renumber renumbering rest)
end

@[expose] def Function.renumber (renumbering : Renumbering) (function : Function) : Function :=
  ⟨function.specificationOnly, Ty.renumberAll renumbering function.inputs,
    Ty.renumberAll renumbering function.outputs,
    function.body.map (LocalRegion.renumber renumbering)⟩

@[expose] def Protocol.renumber (renumbering : Renumbering) (protocol : Protocol) : Protocol :=
  ⟨protocol.specificationOnly, protocol.roles, protocol.inputs.map (Located.renumber renumbering),
    protocol.outputs.map (Located.renumber renumbering), protocol.agreements,
    protocol.body.renumber renumbering⟩

/-- The names of the renumbered definitions, in their new order. -/
@[expose] def Names.renumber (renumbering : Renumbering) (names : Names) : Names :=
  ⟨renumbering.functions.map (names.functions.getD · ""),
    renumbering.protocols.map (names.protocols.getD · ""),
    renumbering.protocols.map (names.roles.getD · []),
    renumbering.protocols.map (names.sites.getD · [])⟩

/-- The entries of a table at the old numbers of a list, in its order. -/
@[expose] def entriesAt {α : Type} (table : List α) (numbers : List Nat) : List α :=
  numbers.filterMap (table[·]?)

/-- The package of the items of a renumbering, in their new order, every number renumbered.
A package without names gives none. -/
@[expose] def Package.renumber (package : Package) (renumbering : Renumbering) : Package :=
  ⟨(entriesAt package.types renumbering.typeRows).map (CatalogueRow.renumber renumbering),
    (entriesAt package.records renumbering.records).map (RecordDeclaration.renumber renumbering),
    (entriesAt package.variants renumbering.variants).map
      (VariantDeclaration.renumber renumbering),
    (entriesAt package.operations renumbering.operations).map (Operation.renumber renumbering),
    (entriesAt package.functions renumbering.functions).map (Function.renumber renumbering),
    (entriesAt package.protocols renumbering.protocols).map (Protocol.renumber renumbering),
    package.names.map (Names.renumber renumbering)⟩

/-! ## Closures -/

/-- The numbering of what a list of roots reaches. -/
@[expose] def Package.renumberingOf (package : Package) (roots : List Reference) : Renumbering :=
  Renumbering.of (package.reached roots)

/-- The closure of a list of roots: what they reach, numbered anew. A statement proved of
the package is not thereby one of the closure: no theorem relates their meanings. -/
@[expose] def Package.closureOfRoots (package : Package) (roots : List Reference) : Package :=
  package.renumber (package.renumberingOf roots)

/-- The closure of a protocol: the package of what it reaches, the protocol last. -/
@[expose] def Package.closure (package : Package) (entry : Nat) : Package :=
  package.closureOfRoots [.protocol entry]

/-- The closure of a function: the package of what it reaches, the function last, without
protocols. -/
@[expose] def Package.functionClosure (package : Package) (entry : Nat) : Package :=
  package.closureOfRoots [.function entry]

end Raw

end Zkc.Core
