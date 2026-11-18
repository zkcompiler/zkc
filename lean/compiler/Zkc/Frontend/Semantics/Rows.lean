module

public import Zkc.Frontend.Typed.Summary
public import Zkc.Frontend.Semantics.StandardTypes

@[expose] public section

set_option autoImplicit false

/-!
# The rows that the frontend applies

A row is asked for by its catalogue name and its static arguments; its kind and its type at them
are read from the vocabulary of the core (`Zkc.Vocabulary.standard`), which holds the rows of
§7.4 that are not operations the core owns, the rows of the units of a field, the function
members of the sorts and the rows of the core library's modules. A row on a type of the
vocabulary takes that type as its static argument: `field.add` on `koala-bear` is the row
`field.add` at the type `koala-bear`. A row on collections takes the element type and, for a
sized collection, the size.

The rows beyond the forty-nine of §7.4 that the checker applies:

- `field.is_nonzero`, the domain row of the restricted row `field.nonzero`. The comparison of a
  field element with the literal `0` is this row, and `field.nonzero` is justified by its value
  known to be true;
- `field.from_nonzero`, the widening of `nonzero<F>` to `F` (TY5): the two are distinct types of
  the core, so the widening is an operation;
- `field.mul`, `field.neg` and `field.pow` at the type `nonzero<F>`: the units are closed under
  `*`, `/`, `^` by a natural and prefix `-`, with `field.inverse`. A sum of units gives an `F`.
-/

namespace Zkc.Frontend.Typing

/-- A row asked for: its catalogue name and static arguments. -/
structure RowRequest where
  name : String
  statics : Array RowStatic
  deriving Inhabited

def RowRequest.key (request : RowRequest) : RowKey := { name := request.name, statics := request.statics }

namespace StandardRow
open Zkc.Vocabulary (Among Atom Element FieldRow GroupRow SeqRow)
open StandardNames

def fieldOp : String → Option FieldRow
  | "field.add" => some .add
  | "field.sub" => some .sub
  | "field.mul" => some .mul
  | "field.neg" => some .neg
  | "field.inverse" => some .inverse
  | "field.pow" => some .pow
  | "field.equal" => some .equal
  | "field.is_nonzero" => some .isNonzero
  | "field.nonzero" => some .nonzero
  | "field.from_nonzero" => some .fromNonzero
  | "field.from_nat" => some .fromNat
  | "field.to_nat" => some .toNat
  | "field.components" => some .components
  | "field.from_components" => some .fromComponents
  | "field.embed" => some .embed
  | "field.coefficients" => some .coefficients
  | "field.from_coefficients" => some .fromCoefficients
  | "field.root" => some .root
  | "ring.mul" => some .mul
  | "ring.pow" => some .pow
  | _ => none

def groupOp : String → Option GroupRow
  | "group.zero" => some .zero
  | "group.add" => some .add
  | "group.sub" => some .sub
  | "group.neg" => some .neg
  | "group.scale" => some .scale
  | "group.equal" => some .equal
  | "group.generator" => some .generator
  | _ => none

def seqOp : String → Option SeqRow
  | "seq.add" => some .add
  | "seq.sub" => some .sub
  | "seq.scale" => some .scale
  | "seq.sum" => some .sum
  | "seq.product" => some .product
  | "seq.inner" => some .inner
  | "seq.equal" => some .equal
  | _ => none

def atomOf? (type : ClosedType) : Option Atom :=
  (fieldOf? type).map .field <|> (groupOf? type).map .group

partial def elementOf? : ClosedType → Option Element
  | .seq item (some size) => return .sized (← elementOf? item) size
  | t => (atomOf? t).map .atom

/-- The source signature of scale and inner names the element's Scalar member.
A sized collection has the group operations but declares no such source member. -/
def sequenceKey? (name : String) (t : ClosedType) (size : Option Nat) : Option Zkc.Vocabulary.RowKey := do
  let op ← seqOp name
  let element ← elementOf? t
  match op, element with
  | .scale, .sized .. | .inner, .sized .. => none
  | _, _ => return .seq op element size

/-- Resolve a source row and its static arguments to the corresponding standard key.
The core signature decides whether the operation exists at those arguments. -/
def resolve (request : RowRequest) : Option Zkc.Vocabulary.RowKey := do
  match request.name, request.statics.toList with
  | "pairing.pair", [] => return .pair
  | "hash.sha256", [] => return .hash .sha256
  | "hash.keccak256", [] => return .hash .keccak256
  | "hash.shake128", [.nat n] => return .hash (.shake128 n)
  | "hash.shake256", [.nat n] => return .hash (.shake256 n)
  | name, [.type t, .nat n] => sequenceKey? name t (some n)
  | name, [.type t] =>
    if let some op := fieldOp name then
      match t with
      | .nonzero base =>
        match name with
        | "field.mul" | "field.neg" | "field.pow" => return .field op (← fieldOf? base) .nonzero
        | _ => none
      | base =>
        let among := if op = .inverse || op = .fromNonzero then Among.nonzero else .all
        return .field op (← fieldOf? base) among
    else if let some op := groupOp name then return .group op (← atomOf? t)
    else sequenceKey? name t none
  | _, _ => none

end StandardRow

/-- Resolve a source operation against the same typed vocabulary used by admission.
A draw reads its law signature at the requested result type. -/
def executableRow? (request : RowRequest) : Option Row := do
  if request.name == "law.uniform" then
    let [.type result] := request.statics.toList | none
    let law ← Zkc.Vocabulary.law (.uniform (← StandardNames.typeOf? result))
    return ⟨request.key, .sampling, (← law.ins.mapM StandardNames.closed?).toArray, #[← StandardNames.closed? law.out]⟩
  let row ← Zkc.Vocabulary.row (← StandardRow.resolve request)
  let kind ← match row.kind with
    | .pure => some RowKind.pure
    | .restricted (.field .isNonzero f .all) =>
      some (.restricted (some ⟨"field.is_nonzero", #[.type (StandardNames.fieldType f)]⟩))
    | .restricted _ => none
  return ⟨request.key, kind, (← row.ins.mapM StandardNames.closed?).toArray, (← row.outs.mapM StandardNames.closed?).toArray⟩

/-- A type argument representable in the source row catalogue. Named tuple
components give the same row signature as their positional representation. -/
partial def sourceArgument? : ClosedType → Option ClosedType
  | .bool => some .bool
  | .nat => some .nat
  | .index n => some (.index n)
  | .nonzero t => return .nonzero (← sourceArgument? t)
  | .seq t n => return .seq (← sourceArgument? t) n
  | .tuple ts _ => do
    let ts ← ts.mapM sourceArgument?
    return .tuple ts (ts.map fun _ => none)
  | .nominal row #[] => some (.nominal row #[])
  | _ => none

partial def lawArgument (type : ClosedType) : Bool :=
  match StandardNames.typeOf? type with
  | some t => Zkc.Vocabulary.isLaw t
  | none => match type with
    | .seq _ (some 0) => true
    | .tuple ts _ => ts.all lawArgument
    | .seq t (some _) => lawArgument t
    | _ => false

/-- Several source signatures are supplied by the linked deployment provider or
refer to types outside the standard core rows. Source typing still checks their ABI. -/
def sourceRow? (request : RowRequest) : Option Row := do
  let pureRow (ins outs : Array ClosedType) : Row := ⟨request.key, .pure, ins, outs⟩
  let bytes : ClosedType := .seq (.index 256) none
  let state := StandardNames.named "suite.merlin3.bls12-381.fr64be/0.state"
  let label := StandardNames.named "suite.merlin3.bls12-381.fr64be/0.label"
  match request.name, request.statics.toList with
  | "seq.equal", [.type t, .nat n] =>
    let collection := ClosedType.seq (← sourceArgument? t) (some n)
    return pureRow #[collection, collection] #[.bool]
  | "seq.equal", [.type t] =>
    let collection := ClosedType.seq (← sourceArgument? t) none
    return pureRow #[collection, collection] #[.bool]
  | "group.zero", [.type (.seq t (some n))] =>
    let _ ← StandardRow.elementOf? t
    return pureRow #[] #[.seq t (some n)]
  | name, [.type (.seq t (some n))] =>
    if ["group.add", "group.sub", "group.equal", "group.neg"].contains name then
      let _ ← StandardRow.elementOf? t
      let item := ClosedType.seq t (some n)
      return pureRow (if name == "group.neg" then #[item] else #[item, item])
        (if name == "group.equal" then #[.bool] else #[item])
    else unary name (.seq t (some n)) bytes state label pureRow
  | name, [.type t] => unary name t bytes state label pureRow
  | "suite.merlin3.bls12-381.fr64be/0.start", [] => return pureRow #[label] #[state]
  | "layout.canonical.open", [] => return pureRow #[] #[bytes]
  | "layout.canonical.close", [] | "layout.canonical.read", [] => return pureRow #[bytes] #[bytes]
  | "layout.canonical.exhausted", [] => return pureRow #[bytes] #[.bool]
  | _, _ => none
where
  unary (name : String) (t bytes state label : ClosedType)
      (pureRow : Array ClosedType → Array ClosedType → Row) : Option Row := do
    let t ← sourceArgument? t
    match name with
    | "layout.canonical.put" => return pureRow #[bytes, t] #[bytes]
    | "layout.canonical.take" => return pureRow #[bytes] #[.bool, t, bytes]
    | "suite.merlin3.bls12-381.fr64be/0.absorb" => return pureRow #[state, label, t] #[state]
    | "suite.merlin3.bls12-381.fr64be/0.derive" =>
      guard (lawArgument t)
      return pureRow #[state, label] #[t, state]
    | "law.uniform" =>
      guard (lawArgument t)
      return ⟨request.key, .sampling, #[], #[t]⟩
    | _ => none

def rowOf? (request : RowRequest) : Option Row :=
  executableRow? request <|> sourceRow? request

/-- Names owned by the standard source vocabulary. A failed lookup at given
arguments cannot fall back to a declaration of a new project primitive. -/
def reservedRow (name : String) : Bool :=
  (StandardRow.fieldOp name).isSome || (StandardRow.groupOp name).isSome || (StandardRow.seqOp name).isSome ||
    ["pairing.pair", "hash.sha256", "hash.keccak256", "hash.shake128", "hash.shake256", "law.uniform",
      "layout.canonical.open", "layout.canonical.put", "layout.canonical.close", "layout.canonical.read",
      "layout.canonical.take", "layout.canonical.exhausted", "suite.merlin3.bls12-381.fr64be/0.start",
      "suite.merlin3.bls12-381.fr64be/0.absorb", "suite.merlin3.bls12-381.fr64be/0.derive"].contains name

/-- A row whose one static argument is a type. -/
def rowAt (name : String) (type : ClosedType) : RowRequest := { name, statics := #[.type type] }

/-- A row on collections of `element`: its statics are the element type and, for a sized
collection, the size. -/
def collectionRow (name : String) (element : ClosedType) (size : Option Nat) : RowRequest :=
  { name, statics := match size with
      | some n => #[.type element, .nat n]
      | none => #[.type element] }

namespace Rows

def fieldBinary (name : String) (field : ClosedType) : RowRequest := rowAt s!"field.{name}" field

def fieldNeg (field : ClosedType) : RowRequest := rowAt "field.neg" field

def fieldInverse (field : ClosedType) : RowRequest := rowAt "field.inverse" field

def fieldPow (field : ClosedType) : RowRequest := rowAt "field.pow" field

def fieldEqual (field : ClosedType) : RowRequest := rowAt "field.equal" field

def fieldIsNonzero (field : ClosedType) : RowRequest := rowAt "field.is_nonzero" field

/-- The refining row of TY5: restricted, with the domain row `field.is_nonzero`. -/
def fieldNonzero (field : ClosedType) : RowRequest := rowAt "field.nonzero" field

def fieldFromNonzero (field : ClosedType) : RowRequest := rowAt "field.from_nonzero" field

/-- The product of two units. -/
def unitMul (field : ClosedType) : RowRequest := rowAt "field.mul" (.nonzero field)

/-- The negation of a unit. -/
def unitNeg (field : ClosedType) : RowRequest := rowAt "field.neg" (.nonzero field)

/-- A power of a unit. -/
def unitPow (field : ClosedType) : RowRequest := rowAt "field.pow" (.nonzero field)

def ringMul (ring : ClosedType) : RowRequest := rowAt "ring.mul" ring

def ringPow (ring : ClosedType) : RowRequest := rowAt "ring.pow" ring

def groupZero (group : ClosedType) : RowRequest := rowAt "group.zero" group

def groupBinary (name : String) (group : ClosedType) : RowRequest := rowAt s!"group.{name}" group

def groupNeg (group : ClosedType) : RowRequest := rowAt "group.neg" group

/-- The action of the scalar of a group. -/
def groupScale (group : ClosedType) : RowRequest := rowAt "group.scale" group

def groupEqual (group : ClosedType) : RowRequest := rowAt "group.equal" group

/-- Element-wise `+` and `-` on a sized collection of elements of a `Group` (TY11). -/
def seqBinary (name : String) (element : ClosedType) (size : Nat) : RowRequest :=
  collectionRow s!"seq.{name}" element (some size)

def seqScale (element : ClosedType) (size : Nat) : RowRequest :=
  collectionRow "seq.scale" element (some size)

def seqEqual (element : ClosedType) (size : Option Nat) : RowRequest :=
  collectionRow "seq.equal" element size

/-- `seq.sum` and `seq.product`: the fold of the element row over a collection. -/
def seqFold (name : String) (element : ClosedType) (size : Option Nat) : RowRequest :=
  collectionRow s!"seq.{name}" element size

def seqInner (element : ClosedType) (size : Nat) : RowRequest :=
  collectionRow "seq.inner" element (some size)

end Rows

/-- The row that a function member of a sort applies (§7.4): `group.generator`,
`field.from_nat`, `field.to_nat`, …, by the member's name. -/
def sortMemberRow (member : String) : Option String :=
  match member with
  | "generator" => some "group.generator"
  | "from_nat" | "to_nat" | "components" | "from_components" | "embed" | "coefficients"
  | "from_coefficients" | "root" => some s!"field.{member}"
  | _ => none

end Zkc.Frontend.Typing
