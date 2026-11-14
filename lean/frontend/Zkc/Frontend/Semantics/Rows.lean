module

public import Zkc.Frontend.Typed.Summary
public import Zkc.Frontend.Semantics.VocabularyTable

@[expose] public section

set_option autoImplicit false

/-!
# The rows that the frontend applies

A row is asked for by its catalogue name and its static arguments; its kind and its type at them
are read from the vocabulary of the core (`Zkc.Core.Vocabulary.table`), which holds the rows of
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

/-- A static argument of a row as the vocabulary reads it. -/
def RowStatic.toVocabulary : RowStatic → Option Zkc.Core.Vocabulary.Value
  | .type closed => (vocabularyOfClosed closed).map .type
  | .nat value => some (.natural value)

/-- The row of the vocabulary that a request names, with its kind and its type. -/
def rowOf? (request : RowRequest) : Option Row := do
  let arguments ← request.statics.toList.mapM RowStatic.toVocabulary
  let signature ← Zkc.Core.Vocabulary.table.signature? request.name arguments
  let kind : RowKind := match signature.kind with
    | .pure => .pure
    | .restricted none => .restricted none
    | .restricted (some domain) => .restricted (some { name := domain, statics := request.statics })
    | .sampling => .sampling
  return { key := request.key, kind
           inputs := (signature.inputs.map closedOfVocabulary).toArray
           outputs := (signature.outputs.map closedOfVocabulary).toArray }

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
