module

public import Zkc.Core.VocabularyModel

public section

/-! What the rows of the arithmetic of an element type compute in the model of a package.

A row of a package is the vocabulary's row of its name at its static arguments. For the rows
of the arithmetic of a field, of a group and of a sized collection of elements, this module
states the value that the model of the package gives at typed values, as the operation of the
element type (`Element`) on their data:

- `model_fieldAdd`, `model_fieldSub`, `model_fieldMul`, `model_groupAdd`, `model_groupScale`:
  one element;
- `model_fieldEqual`, `model_groupEqual`: a `bool`;
- `model_seqSum`: one element of a sized collection; `model_seqAdd`, `model_seqSub`,
  `model_seqScale`: a sized collection of the size of its inputs;
- `model_literal`: the literal of a nominal type that has arithmetic is the image of its
  number.

Each is stated at a row of the package whose name and static arguments are given, for any
element type; what the operation of a prime field or of the curve is on data is the definition
of `Element` (`Zkc.Core.VocabularyElements`). A statement about a model of the mathematics
relates it to these values.
-/

set_option autoImplicit false

namespace Zkc.Core.Vocabulary

open Zkc.Source
open Zkc.Core.Concrete (Datum)

/-- The rows of the arithmetic that this module states. -/
@[expose] def arithmeticRows : List String :=
  ["field.add", "field.sub", "field.mul", "field.equal", "group.add", "group.scale",
    "group.equal", "seq.add", "seq.sub", "seq.scale", "seq.sum"]

/-- No row of the arithmetic has the name of a row of a suite. -/
private theorem arithmeticRow_not_suite {name : String} (arithmetic : name ∈ arithmeticRows)
    (member : String)
    (differs : (arithmeticRows.all fun row =>
      Vocabulary.table.modules.all fun entry => row != entry.row ++ "." ++ member) = true) :
    merlinSuite? Vocabulary.table name member = none :=
  merlinSuite?_none name member (List.all_eq_true.mp differs name arithmetic)

/-- A row of the arithmetic is computed by the arithmetic of its type: no row of a suite, of
the layout or of a hash has its name. -/
theorem applyRow_arithmeticRow {name : String} (arithmetic : name ∈ arithmeticRows)
    (arguments : List Value) (inputs : List Datum) :
    applyRow Vocabulary.table name arguments inputs =
      apply Vocabulary.table name arguments inputs := by
  have start := arithmeticRow_not_suite arithmetic "start" (by decide +kernel)
  have absorb := arithmeticRow_not_suite arithmetic "absorb" (by decide +kernel)
  have derive := arithmeticRow_not_suite arithmetic "derive" (by decide +kernel)
  have other : name ≠ "layout.canonical.take" := by
    rintro rfl
    exact absurd arithmetic (by decide)
  have none : applyBytes Vocabulary.table name arguments inputs = none := by
    unfold applyBytes applyWritten
    simp only [other, start, derive, absorb, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    split <;> first | rfl | exact absurd arithmetic (by decide)
  unfold applyRow
  simp only [none]
  split
  · exact absurd arithmetic (by decide)
  · exact absurd arithmetic (by decide)
  · rfl

/-! ## What each row computes on data -/

section Applied

variable {table : Table} {closed : Closed} {element : Element}

/-- The element type of the first static argument. -/
private theorem reads (found : elementOf table closed = some element) (rest : List Value) :
    (typeArgument (Value.type closed :: rest) 0).bind (elementOf table) = some element := by
  simp [typeArgument, found]

theorem apply_fieldAdd (found : elementOf table closed = some element) (a b : Datum) :
    apply table "field.add" [.type closed] [a, b] = .ok [element.add a b] := by
  unfold apply
  simp only [reads found, bind, Except.bind, pure, Except.pure]
  rfl

theorem apply_fieldSub (found : elementOf table closed = some element) (a b : Datum) :
    apply table "field.sub" [.type closed] [a, b] = .ok [element.sub a b] := by
  unfold apply
  simp only [reads found, bind, Except.bind, pure, Except.pure]
  rfl

theorem apply_fieldMul (found : elementOf table closed = some element) (a b : Datum) :
    apply table "field.mul" [.type closed] [a, b] = .ok [element.mul a b] := by
  unfold apply
  simp only [reads found, bind, Except.bind, pure, Except.pure]
  rfl

theorem apply_fieldEqual (found : elementOf table closed = some element) (a b : Datum) :
    apply table "field.equal" [.type closed] [a, b] = .ok [Datum.ofBool (element.equal a b)] := by
  unfold apply
  simp only [reads found, bind, Except.bind, pure, Except.pure]
  rfl

theorem apply_groupAdd (found : elementOf table closed = some element) (a b : Datum) :
    apply table "group.add" [.type closed] [a, b] = .ok [element.add a b] := by
  unfold apply
  simp only [reads found, bind, Except.bind, pure, Except.pure]
  rfl

theorem apply_groupScale (found : elementOf table closed = some element) (a s : Datum) :
    apply table "group.scale" [.type closed] [a, s] = .ok [element.scale a s] := by
  unfold apply
  simp only [reads found, bind, Except.bind, pure, Except.pure]
  rfl

theorem apply_groupEqual (found : elementOf table closed = some element) (a b : Datum) :
    apply table "group.equal" [.type closed] [a, b] = .ok [Datum.ofBool (element.equal a b)] := by
  unfold apply
  simp only [reads found, bind, Except.bind, pure, Except.pure]
  rfl

theorem apply_seqSum (found : elementOf table closed = some element) (size : Nat) (a : Datum) :
    apply table "seq.sum" [.type closed, .natural size] [a] =
      .ok [a.items.foldl element.add element.zero] := by
  unfold apply
  simp only [reads found, bind, Except.bind, pure, Except.pure]
  rfl

theorem apply_seqAdd (found : elementOf table closed = some element) (size : Nat) (a b : Datum) :
    apply table "seq.add" [.type closed, .natural size] [a, b] =
      .ok [.sequence ((a.items.zip b.items).map fun (x, y) => element.add x y)] := by
  unfold apply
  simp only [reads found, bind, Except.bind, pure, Except.pure]
  rfl

theorem apply_seqSub (found : elementOf table closed = some element) (size : Nat) (a b : Datum) :
    apply table "seq.sub" [.type closed, .natural size] [a, b] =
      .ok [.sequence ((a.items.zip b.items).map fun (x, y) => element.sub x y)] := by
  unfold apply
  simp only [reads found, bind, Except.bind, pure, Except.pure]
  rfl

theorem apply_seqScale (found : elementOf table closed = some element) (size : Nat) (a s : Datum) :
    apply table "seq.scale" [.type closed, .natural size] [a, s] =
      .ok [.sequence (a.items.map fun x => element.scale x s)] := by
  unfold apply
  simp only [reads found, bind, Except.bind, pure, Except.pure]
  rfl

end Applied

/-! ## The rows in the model of a package -/

section Model

variable {package : Raw.Package} {row : Nat} {operation : Operation} {closed : Closed}
  {element : Element}

/-- A pure row of the model of a package, when the row is a row of the arithmetic at static
arguments and that row gives the data of typed values: those values. -/
private theorem model_applied {name : String} {statics : List Value}
    (found : package.operations[row]? = some operation)
    (named : operation.identity.name.toString = name) (arithmetic : name ∈ arithmeticRows)
    (read : argumentsOf package.types.toArray operation.identity = some statics)
    {inputs outputs : List Ty} (populated : Ty.allPopulated outputs = true)
    (arguments : Values Concrete.Value inputs) {values : Values Concrete.Value outputs}
    (applied : apply Vocabulary.table name statics (Concrete.toData inputs arguments) =
      .ok (Concrete.toData outputs values)) :
    (model Vocabulary.table package).pure ⟨row, inputs, outputs⟩ populated arguments = values :=
  model_pure_applied Vocabulary.table package found named read populated arguments
    ((applyRow_arithmeticRow arithmetic _ _).trans applied)

variable (found : package.operations[row]? = some operation)
  (read : argumentsOf package.types.toArray operation.identity = some [.type closed])
  (arithmetic : elementOf Vocabulary.table closed = some element)

include found read arithmetic

theorem model_fieldAdd (named : operation.identity.name.toString = "field.add")
    {first second output : Nat} (populated : Ty.allPopulated [.nominal output] = true)
    (a b : Datum) :
    (model Vocabulary.table package).pure ⟨row, [.nominal first, .nominal second], [.nominal output]⟩
        populated (.cons a (.cons b .nil)) =
      .cons (ty := Ty.nominal output) (element.add a b) .nil :=
  model_applied found named (by decide) read populated _ (apply_fieldAdd arithmetic a b)

theorem model_fieldSub (named : operation.identity.name.toString = "field.sub")
    {first second output : Nat} (populated : Ty.allPopulated [.nominal output] = true)
    (a b : Datum) :
    (model Vocabulary.table package).pure ⟨row, [.nominal first, .nominal second], [.nominal output]⟩
        populated (.cons a (.cons b .nil)) =
      .cons (ty := Ty.nominal output) (element.sub a b) .nil :=
  model_applied found named (by decide) read populated _ (apply_fieldSub arithmetic a b)

theorem model_fieldMul (named : operation.identity.name.toString = "field.mul")
    {first second output : Nat} (populated : Ty.allPopulated [.nominal output] = true)
    (a b : Datum) :
    (model Vocabulary.table package).pure ⟨row, [.nominal first, .nominal second], [.nominal output]⟩
        populated (.cons a (.cons b .nil)) =
      .cons (ty := Ty.nominal output) (element.mul a b) .nil :=
  model_applied found named (by decide) read populated _ (apply_fieldMul arithmetic a b)

theorem model_fieldEqual (named : operation.identity.name.toString = "field.equal")
    {first second : Nat} (populated : Ty.allPopulated [.bool] = true) (a b : Datum) :
    (model Vocabulary.table package).pure ⟨row, [.nominal first, .nominal second], [.bool]⟩
        populated (.cons a (.cons b .nil)) =
      .cons (ty := Ty.bool) (element.equal a b) .nil :=
  model_applied found named (by decide) read populated _ (apply_fieldEqual arithmetic a b)

theorem model_groupAdd (named : operation.identity.name.toString = "group.add")
    {first second output : Nat} (populated : Ty.allPopulated [.nominal output] = true)
    (a b : Datum) :
    (model Vocabulary.table package).pure ⟨row, [.nominal first, .nominal second], [.nominal output]⟩
        populated (.cons a (.cons b .nil)) =
      .cons (ty := Ty.nominal output) (element.add a b) .nil :=
  model_applied found named (by decide) read populated _ (apply_groupAdd arithmetic a b)

theorem model_groupScale (named : operation.identity.name.toString = "group.scale")
    {first second output : Nat} (populated : Ty.allPopulated [.nominal output] = true)
    (a s : Datum) :
    (model Vocabulary.table package).pure ⟨row, [.nominal first, .nominal second], [.nominal output]⟩
        populated (.cons a (.cons s .nil)) =
      .cons (ty := Ty.nominal output) (element.scale a s) .nil :=
  model_applied found named (by decide) read populated _ (apply_groupScale arithmetic a s)

theorem model_groupEqual (named : operation.identity.name.toString = "group.equal")
    {first second : Nat} (populated : Ty.allPopulated [.bool] = true) (a b : Datum) :
    (model Vocabulary.table package).pure ⟨row, [.nominal first, .nominal second], [.bool]⟩
        populated (.cons a (.cons b .nil)) =
      .cons (ty := Ty.bool) (element.equal a b) .nil :=
  model_applied found named (by decide) read populated _ (apply_groupEqual arithmetic a b)

end Model

/-! ## The rows of sized collections -/

/-- A sized collection of elements of a nominal type. -/
abbrev Sized (entry size : Nat) : Type := Concrete.Value (.seq (.nominal entry) (some size))

/-- The datum of a sized collection of a nominal type is the sequence of its elements. -/
theorem toDatum_sized {entry size : Nat} (values : Sized entry size) :
    Concrete.toDatum (.seq (.nominal entry) (some size)) values = .sequence values.val := by
  show Datum.sequence (values.val.map (Concrete.toDatum (.nominal entry))) = _
  rw [show (Concrete.toDatum (.nominal entry) : Datum → Datum) = id from rfl, List.map_id]

/-- The elements of two collections of one size, combined in pairs, are as many. -/
theorem length_pairs {left right size : Nat} (combine : Datum → Datum → Datum)
    (first : Sized left size) (second : Sized right size) :
    ((first.val.zip second.val).map fun (x, y) => combine x y).length = size := by
  rw [List.length_map, List.length_zip, first.property, second.property, Nat.min_self]

/-- The elements of a collection, each mapped, are as many. -/
theorem length_mapped {entry size : Nat} (change : Datum → Datum) (values : Sized entry size) :
    (values.val.map change).length = size := by
  rw [List.length_map, values.property]

/-- The data of one sized collection. -/
private theorem toData_collection {entry size : Nat} (values : Sized entry size) :
    Concrete.toData [.seq (.nominal entry) (some size)] (.cons values .nil) =
      [.sequence values.val] := by
  show [Concrete.toDatum _ values] = _
  rw [toDatum_sized]

/-- The data of two sized collections. -/
private theorem toData_collections {left right size : Nat} (first : Sized left size)
    (second : Sized right size) :
    Concrete.toData [.seq (.nominal left) (some size), .seq (.nominal right) (some size)]
        (.cons first (.cons second .nil)) =
      [.sequence first.val, .sequence second.val] := by
  show [Concrete.toDatum _ first, Concrete.toDatum _ second] = _
  rw [toDatum_sized, toDatum_sized]

/-- The data of a sized collection and an element. -/
private theorem toData_scaled {entry scalar size : Nat} (values : Sized entry size)
    (multiplier : Datum) :
    Concrete.toData [.seq (.nominal entry) (some size), .nominal scalar]
        (.cons values (.cons (ty := Ty.nominal scalar) multiplier .nil)) =
      [.sequence values.val, multiplier] := by
  show [Concrete.toDatum _ values, multiplier] = _
  rw [toDatum_sized]

section Collections

variable {package : Raw.Package} {row : Nat} {operation : Operation} {closed : Closed}
  {element : Element} {size : Nat}
  (found : package.operations[row]? = some operation)
  (read : argumentsOf package.types.toArray operation.identity =
    some [.type closed, .natural size])
  (arithmetic : elementOf Vocabulary.table closed = some element)

include found read arithmetic

theorem model_seqSum (named : operation.identity.name.toString = "seq.sum")
    {entry output : Nat} (populated : Ty.allPopulated [.nominal output] = true)
    (values : Sized entry size) :
    (model Vocabulary.table package).pure ⟨row, [.seq (.nominal entry) (some size)], [.nominal output]⟩
        populated (.cons values .nil) =
      .cons (ty := Ty.nominal output) (values.val.foldl element.add element.zero) .nil :=
  model_applied found named (by decide) read populated _
    ((congrArg (apply Vocabulary.table "seq.sum" _) (toData_collection values)).trans
      (apply_seqSum arithmetic size _))

theorem model_seqAdd (named : operation.identity.name.toString = "seq.add")
    {left right output : Nat}
    (populated : Ty.allPopulated [.seq (.nominal output) (some size)] = true)
    (first : Sized left size) (second : Sized right size) :
    (model Vocabulary.table package).pure
        ⟨row, [.seq (.nominal left) (some size), .seq (.nominal right) (some size)],
          [.seq (.nominal output) (some size)]⟩ populated (.cons first (.cons second .nil)) =
      .cons (ty := Ty.seq (.nominal output) (some size))
        ⟨(first.val.zip second.val).map fun (x, y) => element.add x y,
          length_pairs element.add first second⟩ .nil :=
  model_applied found named (by decide) read populated _
    (((congrArg (apply Vocabulary.table "seq.add" _) (toData_collections first second)).trans
      (apply_seqAdd arithmetic size _ _)).trans
        (congrArg Except.ok (toData_collection (entry := output)
          ⟨_, length_pairs element.add first second⟩).symm))

theorem model_seqSub (named : operation.identity.name.toString = "seq.sub")
    {left right output : Nat}
    (populated : Ty.allPopulated [.seq (.nominal output) (some size)] = true)
    (first : Sized left size) (second : Sized right size) :
    (model Vocabulary.table package).pure
        ⟨row, [.seq (.nominal left) (some size), .seq (.nominal right) (some size)],
          [.seq (.nominal output) (some size)]⟩ populated (.cons first (.cons second .nil)) =
      .cons (ty := Ty.seq (.nominal output) (some size))
        ⟨(first.val.zip second.val).map fun (x, y) => element.sub x y,
          length_pairs element.sub first second⟩ .nil :=
  model_applied found named (by decide) read populated _
    (((congrArg (apply Vocabulary.table "seq.sub" _) (toData_collections first second)).trans
      (apply_seqSub arithmetic size _ _)).trans
        (congrArg Except.ok (toData_collection (entry := output)
          ⟨_, length_pairs element.sub first second⟩).symm))

theorem model_seqScale (named : operation.identity.name.toString = "seq.scale")
    {entry scalar output : Nat}
    (populated : Ty.allPopulated [.seq (.nominal output) (some size)] = true)
    (values : Sized entry size) (multiplier : Datum) :
    (model Vocabulary.table package).pure
        ⟨row, [.seq (.nominal entry) (some size), .nominal scalar],
          [.seq (.nominal output) (some size)]⟩ populated
        (.cons values (.cons (ty := Ty.nominal scalar) multiplier .nil)) =
      .cons (ty := Ty.seq (.nominal output) (some size))
        ⟨values.val.map fun x => element.scale x multiplier,
          length_mapped (fun x => element.scale x multiplier) values⟩ .nil :=
  model_applied found named (by decide) read populated _
    (((congrArg (apply Vocabulary.table "seq.scale" _) (toData_scaled values multiplier)).trans
      (apply_seqScale arithmetic size _ _)).trans
        (congrArg Except.ok (toData_collection (entry := output)
          ⟨_, length_mapped (fun x => element.scale x multiplier) values⟩).symm))

end Collections

/-! ## Literals -/

/-- The literal of a nominal type that has arithmetic: the image of its number. -/
theorem model_literal {package : Raw.Package} {row : Nat} {closed : Closed} {element : Element}
    (closedIs : closedOf package.types.toArray (.nominal row) = some closed)
    (arithmetic : elementOf Vocabulary.table closed = some element) (data : List Nat) :
    (model Vocabulary.table package).literal row data = element.ofNat (data.headD 0) := by
  simp [model, literalDatum, closedIs, arithmetic]

/-! ## The fields and the group that the vocabulary computes -/

/-- The scalar field of BLS12-381 is the prime field of its order. -/
theorem element_bls12381Fr :
    elementOf Vocabulary.table (.row "bls12-381.fr") = some (.prime bls12381Order) := rfl

/-- The group G1 of BLS12-381 is computed by the arithmetic of the curve. -/
theorem element_bls12381G1 : elementOf Vocabulary.table (.row "bls12-381.g1") = some .curve := rfl

/-- The scalars of the curve are reduced modulo the order of the scalar field. -/
theorem scalarModulus_eq : Concrete.scalarModulus = bls12381Order := Concrete.scalarModulus_eq

/-- The point at infinity is of the group. -/
theorem inGroup_infinity : inGroup none = true := Concrete.infinity_ofGroup

end Zkc.Core.Vocabulary
