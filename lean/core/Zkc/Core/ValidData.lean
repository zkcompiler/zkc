module

public import Zkc.Core.VocabularyModel

@[expose] public section

/-! Valid data by type: values of the types of a package that validation accepts
(`Vocabulary.validInput`), for the inputs of runs and for the coins of their draws and
samples.

A **draw** gives one value of a type. The first draws are the boundary draws: the `n`-th gives
every leaf its `n`-th boundary value, cycling through them, and a collection without a size
`n` elements (cycling through none, one and two). The mixed draws come next: each leaf takes
one of its boundary values, chosen by a number of a stream, so that the leaves of one value
differ (a collection of zeros and ones, a base and a point that are not the same). The boundary
values of a leaf, in order:

- `bool`: `false`, `true`;
- `index<b>`: 0, 1, `b - 1`;
- `nat`: 0, 1, 2, 255;
- an element of a prime field: 0, 1, the order less one; of `nonzero` of it: 1, the order less
  one;
- an element of an extension: zero, one, every coefficient the order less one;
- a point of G1: the point at infinity, the generator, its negation.

Every other draw takes its leaves from a stream of numbers. A leaf that has a law is the value
of its law (`Vocabulary.Law`): `bool`, `index<b>`, an element of a field or of an extension
and a unit of one, and a point of G1, whose scalar is below 2^16 here and not below the order
of the group (a small multiple keeps the drawing fast; a point is validated by a multiplication
by the order of the group, which is costly). What has no law is drawn for inputs only: a `nat`
below 1024, a collection without a size of fewer than four elements, an alternative of a
variant by a number.

A nominal type without arithmetic in the model (the state of a transcript, a label, G2),
`index<0>` and a variant without an alternative have no value to draw: the draw gives the
reason. A record and a variant are drawn by the fields and the alternatives that the type
carries, which are what validation reads.

The streams are numbers below 2^256 made from a seed and a key by a 64-bit mixing function,
so that a draw depends only on the seed, the key and the type. -/

set_option autoImplicit false

namespace Zkc.Core.ValidData

open Zkc.Core.Concrete (Datum)
open Vocabulary

/-- A stream of numbers: the `i`-th number. -/
abbrev Stream := Nat → Nat

/-- A 64-bit mixing step (the finaliser of SplitMix64). -/
def mix (value : Nat) : Nat :=
  let modulus := 2 ^ 64
  let x := (value + 0x9e3779b97f4a7c15) % modulus
  let x := (x ^^^ (x >>> 30)) * 0xbf58476d1ce4e5b9 % modulus
  let x := (x ^^^ (x >>> 27)) * 0x94d049bb133111eb % modulus
  x ^^^ (x >>> 31)

/-- The numbers of a seed and a key, each below 2^256. -/
def stream (seed : Nat) (key : List Nat) : Stream := fun index =>
  let start := (key ++ [index]).foldl (init := mix seed) fun state part =>
    mix ((state ^^^ (part % 2 ^ 64)) + part / 2 ^ 64)
  let w0 := mix start
  let w1 := mix (w0 + 1)
  let w2 := mix (w1 + 2)
  let w3 := mix (w2 + 3)
  w0 + w1 * 2 ^ 64 + w2 * 2 ^ 128 + w3 * 2 ^ 192

/-- How the values of a draw are chosen. -/
inductive Draw where
  /-- Every leaf its boundary value of this number, cycling through them. -/
  | boundary (index : Nat)
  /-- Every leaf one of its boundary values, chosen by the next number of the stream. -/
  | mixed (numbers : Stream)
  /-- Every leaf from the next number of the stream. -/
  | taken (numbers : Stream)

/-- The number of boundary draws: the seeds below it are boundary draws. -/
def boundaryDraws : Nat := 3

/-- The number of mixed draws, after the boundary draws. -/
def mixedDraws : Nat := 11

/-- The draw of a seed under a key: a boundary draw for the first seeds, a mixed draw of the
stream of the seed and the key for the next ones, numbers of that stream for the others. -/
def Draw.ofSeed (seed : Nat) (key : List Nat) : Draw :=
  if seed < boundaryDraws then .boundary seed
  else if seed < boundaryDraws + mixedDraws then .mixed (stream seed key)
  else .taken (stream seed key)

/-- The value of a list at a number, cycling; the default for an empty list. -/
def cycle {α : Type} [Inhabited α] (values : List α) (index : Nat) : α :=
  if values.isEmpty then default else values[index % values.length]!

/-- A leaf: one of its boundary values, or one made from the next number of the stream; with
the position of the next number. -/
def leaf (draw : Draw) (boundaries : List Datum) (fromNumber : Nat → Datum) (next : Nat) :
    Datum × Nat :=
  match draw with
  | .boundary index => (cycle boundaries index, next)
  | .mixed numbers => (cycle boundaries (numbers next), next + 1)
  | .taken numbers => (fromNumber (numbers next), next + 1)

/-- How many elements a collection without a size has. -/
def unsizedLength (draw : Draw) (next : Nat) : Nat × Nat :=
  match draw with
  | .boundary index => (index % 3, next)
  | .mixed numbers => (numbers next % 3, next + 1)
  | .taken numbers => (numbers next % 4, next + 1)

/-- The bound on the scalar of a point that a stream gives. -/
def pointScalars : Nat := 2 ^ 16

/-- The coefficients of an extension, `degree` numbers below the order. -/
def coefficients (degree : Nat) (value : Nat → Nat) : Datum :=
  Extension.ofCoefficients ((List.range degree).map value)

/-- A value of an element type of the vocabulary. -/
def element (draw : Draw) (unit : Bool) : Element → Nat → Except String (Datum × Nat)
  | .prime order, next =>
    if unit then
      if order < 2 then .error s!"a field of order {order} has no unit"
      else .ok (leaf draw [.number 1, .number (order - 1)] (Law.unit order) next)
    else .ok (leaf draw [.number 0, .number 1, .number (order - 1)] (Law.field order) next)
  | .extension order degree _, next =>
    let zero := coefficients degree fun _ => 0
    let one := coefficients degree fun index => if index == 0 then 1 else 0
    let largest := coefficients degree fun _ => order - 1
    match draw with
    | .boundary index =>
      .ok (cycle (if unit then [one, largest] else [zero, one, largest]) index, next)
    | .mixed numbers =>
      .ok (cycle (if unit then [one, largest] else [zero, one, largest]) (numbers next), next + 1)
    | .taken numbers => .ok (Law.extension order degree unit numbers next, next + degree)
  | .curve, next =>
    if unit then .error "a point of G1 is no unit"
    else
      let generator := Datum.ofPoint Concrete.generator
      .ok (leaf draw [Datum.ofPoint none, generator, Datum.ofPoint (negatePoint Concrete.generator)]
        (Law.point pointScalars) next)

/-- A value of a closed type of the vocabulary, from the position `next` of the stream on; with
the position after it. -/
partial def closed (table : Table) (draw : Draw) : Closed → Nat → Except String (Datum × Nat)
  | .bool, next =>
    .ok (leaf draw [Datum.ofBool false, Datum.ofBool true] Law.bool next)
  | .nat, next =>
    .ok (leaf draw [.number 0, .number 1, .number 2, .number 255] (fun n => .number (n % 1024)) next)
  | .index bound, next =>
    if bound == 0 then .error "`index<0>` has no value"
    else .ok (leaf draw [.number 0, .number (1 % bound), .number (bound - 1)] (Law.index bound) next)
  | .nonzero field, next =>
    match elementOf table field with
    | some found => element draw true found next
    | none => .error "`nonzero` of a type without arithmetic has no value to draw"
  | .seq item size, next => do
    let (count, next) := match size with
      | some size => (size, next)
      | none => unsizedLength draw next
    let (items, next) ← (List.range count).foldlM (init := (#[], next)) fun (items, next) _ => do
      let (value, next) ← closed table draw item next
      return (items.push value, next)
    return (.sequence items.toList, next)
  | .tuple components, next => do
    let (items, next) ← components.foldlM (init := (#[], next)) fun (items, next) component => do
      let (value, next) ← closed table draw component next
      return (items.push value, next)
    return (.sequence items.toList, next)
  | .row name, next =>
    match elementOf table (.row name) with
    | some found => element draw false found next
    | none => .error s!"`{name}` has no values that the model of the vocabulary computes"

/-- A value of a type of a package, whose nominal rows are those of `types`, from the position
`next` of the stream on; with the position after it. -/
partial def value (table : Table) (types : Array CatalogueRow) (draw : Draw) :
    Ty → Nat → Except String (Datum × Nat)
  | .seq item size, next => do
    let (count, next) := match size with
      | some size => (size, next)
      | none => unsizedLength draw next
    let (items, next) ← (List.range count).foldlM (init := (#[], next)) fun (items, next) _ => do
      let (datum, next) ← value table types draw item next
      return (items.push datum, next)
    return (.sequence items.toList, next)
  | .tuple components, next => values table types draw components next
  | .record _ _ fields, next => values table types draw fields next
  | .variant _ alternatives, next => do
    if alternatives.isEmpty then throw "a variant without an alternative has no value"
    let (position, next) := match draw with
      | .boundary index => (index % alternatives.length, next)
      | .mixed numbers | .taken numbers => (numbers next % alternatives.length, next + 1)
    let (payload, next) ← value table types draw (alternatives[position]!) next
    return (.sequence [.number position, payload], next)
  | type, next =>
    match closedOf types type with
    | some found => closed table draw found next
    | none => .error "a type that the vocabulary does not close"
where
  values (table : Table) (types : Array CatalogueRow) (draw : Draw) (components : List Ty)
      (next : Nat) : Except String (Datum × Nat) := do
    let (items, next) ← components.foldlM (init := (#[], next)) fun (items, next) component => do
      let (datum, next) ← value table types draw component next
      return (items.push datum, next)
    return (.sequence items.toList, next)

/-- Values of the types of the inputs of a run, one per type, in order, from one draw. -/
def inputs (table : Table) (types : Array CatalogueRow) (draw : Draw) (inputTypes : List Ty) :
    Except String (List Datum) := do
  let (data, _) ← inputTypes.foldlM (init := (#[], 0)) fun (data, next) type => do
    let (datum, next) ← value table types draw type next
    return (data.push datum, next)
  return data.toList

/-- The value of a coin: the `count`-th coin at a site whose key is given, a value of the type
of its law, drawn under the seed. -/
def coin (table : Table) (types : Array CatalogueRow) (seed : Nat) (key : List Nat) (count : Nat)
    (type : Ty) : Except String Datum :=
  (·.1) <$> value table types (Draw.ofSeed seed (key ++ [count])) type 0

end Zkc.Core.ValidData
