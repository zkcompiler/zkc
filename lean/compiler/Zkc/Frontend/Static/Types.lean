module

public import Zkc.Frontend.Static.Basic
public import Zkc.Frontend.Semantics.Rows

@[expose] public section

set_option autoImplicit false

/-!
# Closed types: equality, joins and sorts

Two types are equal when they are the same closed type (TY3); the names of the components of a
tuple type are annotations and do not count. The join of two types is the least type both widen
to (TY5). Whether a type is of a sort is read from the vocabulary.
-/

namespace Zkc.Frontend.Static

/-- Equality of closed types, without the names of tuple components. -/
partial def typeEq : ClosedType → ClosedType → Bool
  | .tuple a _, .tuple b _ => a.size == b.size && (a.zip b).all fun (x, y) => typeEq x y
  | .seq a m, .seq b n => m == n && typeEq a b
  | .nonzero a, .nonzero b => typeEq a b
  | a, b => a == b

/-- The collection of no elements of any type: the type of `[]` where no type is expected,
`[(); 0]`. Every value of that type is `[]`, a declared one included (TY6). -/
def isEmptyCollection : ClosedType → Bool
  | .seq element (some 0) => typeEq element .unit
  | _ => false

/-- The least type both types widen to (TY5). `[]` joins any collection. -/
partial def join (a b : ClosedType) : Option ClosedType :=
  if typeEq a b then some a else
  if isEmptyCollection a then
    match b with
    | .seq element size => some (.seq element (if size == some 0 then some 0 else none))
    | _ => none
  else if isEmptyCollection b then join b a else
  match a, b with
  | .index s, .index t => some (.index (max s t))
  | .index _, .nat | .nat, .index _ => some .nat
  | .nonzero f, other | other, .nonzero f => if typeEq f other then some other else none
  | .seq x m, .seq y n => do
    let element ← join x y
    return .seq element (if m == n then m else none)
  | .tuple xs names, .tuple ys _ => do
    if xs.size != ys.size then none
    let components ← (xs.zip ys).mapM fun (x, y) => join x y
    return .tuple components names
  | _, _ => none

def isNatural : ClosedType → Bool
  | .nat | .index _ => true
  | _ => false

/-- The payload type of an alternative: the empty tuple, its one type, or the tuple of its
types. -/
def payloadType (payload : Array ClosedType) : ClosedType :=
  if payload.size == 1 then payload[0]! else .tuple payload (payload.map fun _ => none)

def hasSortM (type : ClosedType) (sort : String) : CompileM Bool :=
  return hasSort (← getVocabulary) type sort

/-- A type of the vocabulary with the sort `Field`. -/
def isField (type : ClosedType) : CompileM Bool := do
  match type with
  | .nominal .. | .«opaque» .. => hasSortM type "Field"
  | _ => return false

def isRing (type : ClosedType) : CompileM Bool := do
  match type with
  | .nominal .. | .«opaque» .. => hasSortM type "Ring"
  | _ => return false

def isGroup (type : ClosedType) : CompileM Bool := do
  match type with
  | .nominal .. | .«opaque» .. => hasSortM type "Group"
  | _ => return false

/-- A sized collection of elements of a `Group` (TY11). -/
def isGroupCollection (type : ClosedType) : CompileM Bool := do
  match type with
  | .seq element (some _) => isGroup element
  | _ => return false

/-- A member type of a type of the vocabulary. -/
def typeMember? (type : ClosedType) (member : String) : CompileM (Option ClosedType) := do
  match type with
  | .nominal row _ =>
    return ((← getVocabulary).type? row).bind fun entry =>
      (entry.typeMembers.find? (·.1 == member)).map (·.2)
  | _ => return none

def naturalMember? (type : ClosedType) (member : String) : CompileM (Option Nat) := do
  match type with
  | .nominal row _ =>
    return ((← getVocabulary).type? row).bind fun entry =>
      (entry.naturalMembers.find? (·.1 == member)).map (·.2)
  | _ => return none

/-- The `Scalar` of a group, or of the elements of a sized collection of group elements. -/
def scalarOf (type : ClosedType) : CompileM (Option ClosedType) := do
  match type with
  | .seq element (some _) => typeMember? element "Scalar"
  | other => typeMember? other "Scalar"

/-- A closed type with every occurrence of one type replaced by another. -/
partial def replaceType (type : ClosedType) (old new : ClosedType) : ClosedType :=
  if type == old then new else
  match type with
  | .nonzero field => .nonzero (replaceType field old new)
  | .seq element size => .seq (replaceType element old new) size
  | .tuple components names => .tuple (components.map (replaceType · old new)) names
  | other => other

/-- In the opaque elaboration, a row of a sort at a fresh type (SP12): its type at the
representative of the strongest sort of the fresh type, with the fresh type for the
representative. The code of the opaque elaboration is not kept, so the row is never emitted. -/
def opaqueRow? (request : Typing.RowRequest) : CompileM (Option Typing.Row) := do
  let vocabulary := (← getVocabulary)
  let mut statics := request.statics
  let mut replaced : Array (ClosedType × ClosedType) := #[]
  for index in [0:statics.size] do
    let .type (.«opaque» «module» member arguments sorts) := statics[index]! | continue
    let some sort := ["PrimeField", "Field", "Ring", "PrimeOrderGroup", "Group"].find? fun sort =>
        sorts.contains sort && (vocabulary.representative? sort).isSome
      | return none
    let some row := vocabulary.representative? sort | return none
    let representative := ClosedType.nominal row #[]
    statics := statics.set! index (.type representative)
    replaced := replaced.push (representative, .«opaque» «module» member arguments sorts)
  if replaced.isEmpty then return none
  let some row := Typing.rowOf? { request with statics } | return none
  let back (type : ClosedType) : ClosedType :=
    replaced.foldl (init := type) fun type (representative, fresh) => replaceType type representative fresh
  return some { row with key := request.key, inputs := row.inputs.map back, outputs := row.outputs.map back }

/-- The row of the vocabulary that a request names. -/
def vocabularyRow (request : Typing.RowRequest) : CompileM Typing.Row := do
  match Typing.rowOf? request with
  | some row => return row
  | none =>
    if let some row ← opaqueRow? request then return row
    throw (.waiting s!"the row `{request.name}` at these static arguments, which the vocabulary does not have")

end Zkc.Frontend.Static
