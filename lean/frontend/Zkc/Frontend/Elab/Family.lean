module

public import Zkc.Frontend.Elab.Basic

@[expose] public section

set_option autoImplicit false

/-!
# The operators of a type

Which operators a type has, and by what, is decided by its sort (NL6, TY6, TY11, TY12). One
function gives the family of a type, and every operator reads the family: `+`, `-`, `*`, `/`,
`^`, prefix `-`, a number, `==`, a fold and an inner product.

A field is a ring and a ring is a group: a type with the sort `Field` is of the family of
fields whatever other sorts it has, and one with `Ring` and not `Field` is of the family of
rings.
-/

namespace Zkc.Frontend.Elab

open Static

/-- The family of operators of a type. -/
inductive Family where
  /-- `nat` and `index<n>`: the operations of naturals. -/
  | natural
  /-- `nonzero<F>`: the rows of the units of the field `F`. -/
  | unit (field : ClosedType)
  /-- A type of the sort `Field`. -/
  | field
  /-- A type of the sort `Ring` that is no field. -/
  | ring
  /-- A type of the sort `Group` that is no ring. -/
  | group
  /-- A sized collection of elements of a group, a ring or a field: element by element (TY11). -/
  | points (element : ClosedType) (size : Nat)
  /-- A record or a variant: the functions of its home module (NL6). -/
  | declared
  /-- A `spec type`: no operator. -/
  | specification
  /-- A type without operators of its own. -/
  | other
  deriving Inhabited

/-- The family of a type. -/
def familyOf (type : ClosedType) : CompileM Family := do
  match type with
  | .nat | .index _ => return .natural
  | .nonzero field => return .unit field
  | .specification _ => return .specification
  | .record _ | .«variant» _ => return .declared
  | .seq element (some size) =>
    if ← isGroup element then return .points element size else return .other
  | .nominal .. | .«opaque» .. =>
    if ← isField type then return .field
    if ← isRing type then return .ring
    if ← isGroup type then return .group
    return .other
  | _ => return .other

namespace Family

/-- An element of a group, a ring or a field. -/
def isElement : Family → Bool
  | .field | .ring | .group => true
  | _ => false

/-- A type with `+`: an element or a sized collection of elements. -/
def hasSum : Family → Bool
  | .field | .ring | .group | .points .. => true
  | _ => false

/-- A type with a product of two of its values: a ring or a field. -/
def hasProduct : Family → Bool
  | .field | .ring => true
  | _ => false

/-- A type whose `*` is the scaling by a scalar: a group that is no ring, and a sized
collection. -/
def isScaled : Family → Bool
  | .group | .points .. => true
  | _ => false

/-- The row of `add` or `sub` on two values of the type. -/
def sumRow? (family : Family) (type : ClosedType) (name : String) : Option Typing.RowRequest :=
  match family with
  | .field => some (Typing.Rows.fieldBinary name type)
  | .ring | .group => some (Typing.Rows.groupBinary name type)
  | .points element size => some (Typing.Rows.seqBinary name element size)
  | _ => none

/-- The row of the scaling of a value of the type by a scalar. -/
def scaleRow? (family : Family) (type : ClosedType) : Option Typing.RowRequest :=
  match family with
  | .group => some (Typing.Rows.groupScale type)
  | .points element size => some (Typing.Rows.seqScale element size)
  | _ => none

/-- The row of prefix `-` on a value of the type. -/
def negRow? (family : Family) (type : ClosedType) : Option Typing.RowRequest :=
  match family with
  | .unit base => some (Typing.Rows.unitNeg base)
  | .field => some (Typing.Rows.fieldNeg type)
  | .ring | .group => some (Typing.Rows.groupNeg type)
  | _ => none

/-- The row of `^` on a value of the type and a natural. -/
def powerRow? (family : Family) (type : ClosedType) : Option Typing.RowRequest :=
  match family with
  | .unit base => some (Typing.Rows.unitPow base)
  | .field => some (Typing.Rows.fieldPow type)
  | .ring => some (Typing.Rows.ringPow type)
  | _ => none

/-- The row of `==` on two elements of the type. -/
def equalRow? (family : Family) (type : ClosedType) : Option Typing.RowRequest :=
  match family with
  | .field => some (Typing.Rows.fieldEqual type)
  | .ring | .group => some (Typing.Rows.groupEqual type)
  | _ => none

end Family

/-- The type at which the summands of a literal expression check: a sum of units is no unit,
so a `nonzero<F>` expected of a sum is `F`. -/
def literalBase : ClosedType → ClosedType
  | .nonzero field => field
  | other => other

/-- The type at which a literal on the right of `*`, `/` or `%` checks, from the type of the
left operand (TY6): the units of a field under `/`; the scalars of a group, or of a sized
collection of group elements, under `*`; the type itself otherwise. A natural gives none: its
sibling is a natural. -/
def rightOperandType (operator : Operator) (type : ClosedType) :
    CompileM (Option ClosedType) := do
  if isNatural type then return none
  let base := literalBase type
  let family ← familyOf base
  match operator with
  | .divide => return some (if family matches .field then .nonzero base else base)
  | _ =>
    if let .nonzero _ := type then return some type
    if family.isScaled then return (← scalarOf base)
    return some base

end Zkc.Frontend.Elab
