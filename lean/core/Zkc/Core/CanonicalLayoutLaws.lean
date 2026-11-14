module

public import Zkc.Core.LayoutLaws
public import Zkc.Core.VocabularyModel

public section

/-! The laws of the canonical layout in the model of the vocabulary.

`Layout.Lawful` (`Zkc.Core.LayoutLaws`) is what the serialize step needs of a layout in a
model. This module gives it for the layout that a declaration describes over the rows of a
package, in the model of the vocabulary's rows of that package (`Vocabulary.model`).

- `Layout.DeclaredBy`: what `Layout.ofRaw` makes of a declared layout: its three types are
  the declared ones, its four rows of the entry are the declared ones, and a row that puts
  or takes a value of a type is one of the declared ones (`Layout.ofRaw_declaredBy`).
- `Layout.Canonical package layout`: the layout is the canonical one of the package. The
  writer, the reader and the proof are bytes; the rows of the entry are the package's rows
  named `layout.canonical.open`, `close`, `read` and `exhausted` at no static argument; and a
  row that puts or takes a value of a type is the package's row named `layout.canonical.put`
  or `take` at the closed type that the type stands for (`closedOf`). So the row that puts
  and the row that takes a value of one type are at one closed type.
- `Layout.canonical_of_declared`: the layout that a declaration describes is the canonical
  one when the core elaborates the package, the rows of the package are the vocabulary's
  (`mismatches Vocabulary.table package = []`), and the rows that the declaration names have
  the six names (`Raw.Layout.namesCanonical`, which reads the names alone and is decided on a
  package). The static arguments, the types of the rows and the three types of bytes are
  derived: a row with a name of the vocabulary that the comparison passes has the
  vocabulary's signature.
- `Layout.Canonical.laws`: the laws. The wire is bytes with `++`; a value of a type is
  written as the bytes that the format of its closed type writes for its datum
  (`encodeMessage`); a value is writable when its type has a format and its datum is of the
  domain of the format (`writes`, a `Bool`); a writer and a reader are their bytes. Each law
  is the statement about one row in the model of a package (`model_open`, `model_put`,
  `model_close`, `model_read`, `model_take`, `model_exhausted`) with the laws of the format
  (`formatOf_lawful`).
- `Layout.Canonical.format_of_admitted`: in a package that the vocabulary admits
  (`missing Vocabulary.table package = []`) a type that the canonical layout puts or takes a
  value of has a format. The laws do not need it: a value of a type without a format is not
  writable. With it, what is writable of such a type is the domain of its format.
- `canonicalLaws`, `canonicalLawsWithoutPoint`: the laws from what is checked of a package
  and its declaration. One hypothesis is not decided on the package: the compressed encoding
  of G1 (`PointCompression`), asked only when a type that the declared layout puts or takes
  has a point of G1 in it (`Raw.Declaration.movesPoint`).

What a writable value is for the types that messages have, and which values that the rows
of the model compute are writable, is in `Zkc.Core.CanonicalLayoutValues`.

This module reads the bodies of `Layout.ofRaw`, of the lookup of a row and of the comparison
of a package with the vocabulary, which their modules expose.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source
open Zkc.Core.Concrete (Datum)

/-! ## The layout that a declaration describes -/

/-- The row found at a position is at that position. -/
theorem rowWith_index {operations : List OperationSignature} (rows : Scope operations)
    {signature : OperationSignature} {row : Nat} {reference : Var operations signature}
    (found : rowWith rows signature row = some reference) : reference.index = row := by
  unfold rowWith Scope.atType? at found
  split at found
  · cases found
    rfl
  · cases found

/-- The first row with a signature among candidates is one of the candidates. -/
theorem firstRowWith_mem {operations : List OperationSignature} (rows : Scope operations)
    {signature : OperationSignature} :
    ∀ {candidates : List Nat} {reference : Var operations signature},
      firstRowWith rows signature candidates = some reference → reference.index ∈ candidates
  | [], _, found => by cases found
  | row :: later, reference, found => by
    unfold firstRowWith at found
    split at found
    · rename_i first isFirst
      cases found
      exact List.mem_cons.mpr (.inl (rowWith_index rows isFirst))
    · exact List.mem_cons_of_mem _ (firstRowWith_mem rows found)

/-- A layout is the one that a declared layout describes: its types are the declared ones,
its rows of the entry are the declared ones, and a row that puts or takes a value is one of
the declared ones. -/
structure Layout.DeclaredBy {operations : List OperationSignature} (raw : Raw.Layout)
    (layout : Layout operations) : Prop where
  writer : layout.writer = raw.writer
  reader : layout.reader = raw.reader
  proof : layout.proof = raw.proof
  start : layout.start.index = raw.start
  close : layout.close.index = raw.close
  read : layout.read.index = raw.read
  exhausted : layout.exhausted.index = raw.exhausted
  put : ∀ {type : Ty} {put : Var operations ⟨[layout.writer, type], [layout.writer], .pure⟩},
    layout.put type = some put → put.index ∈ raw.putting
  take : ∀ {type : Ty}
    {take : Var operations ⟨[layout.reader], [.bool, type, layout.reader], .pure⟩},
    layout.take type = some take → take.index ∈ raw.taking

/-- The layout that `Layout.ofRaw` makes of a declared layout is the one it describes. -/
theorem Layout.ofRaw_declaredBy {operations : List OperationSignature} {rows : Scope operations}
    {raw : Raw.Layout} {layout : Layout operations}
    (declared : Layout.ofRaw rows raw = some layout) : layout.DeclaredBy raw := by
  unfold Layout.ofRaw at declared
  split at declared
  · rename_i start close read exhausted isStart isClose isRead isExhausted
    split at declared
    · split at declared
      · split at declared
        · cases declared
          exact ⟨rfl, rfl, rfl, rowWith_index rows isStart, rowWith_index rows isClose,
            rowWith_index rows isRead, rowWith_index rows isExhausted,
            fun found => firstRowWith_mem rows found, fun found => firstRowWith_mem rows found⟩
        · cases declared
      · cases declared
    · cases declared
  · cases declared

namespace Vocabulary

/-! ## The types of a package as closed types of the vocabulary -/

mutual
  /-- Closed types that the comparison finds equal are one closed type. -/
  theorem Closed.eq_of_beq : ∀ (first second : Closed), Closed.beq first second = true →
      first = second
    | .bool, second, same => by cases second <;> first | rfl | simp [Closed.beq] at same
    | .nat, second, same => by cases second <;> first | rfl | simp [Closed.beq] at same
    | .index bound, second, same => by
      cases second with
      | index other => simp only [Closed.beq, beq_iff_eq] at same; rw [same]
      | _ => simp [Closed.beq] at same
    | .nonzero field, second, same => by
      cases second with
      | nonzero other =>
        rw [Closed.eq_of_beq field other (by simpa only [Closed.beq] using same)]
      | _ => simp [Closed.beq] at same
    | .seq element size, second, same => by
      cases second with
      | seq other otherSize =>
        simp only [Closed.beq, Bool.and_eq_true, beq_iff_eq] at same
        rw [Closed.eq_of_beq element other same.1, same.2]
      | _ => simp [Closed.beq] at same
    | .tuple components, second, same => by
      cases second with
      | tuple others =>
        rw [Closed.eq_of_beqList components others (by simpa only [Closed.beq] using same)]
      | _ => simp [Closed.beq] at same
    | .row name, second, same => by
      cases second with
      | row other => simp only [Closed.beq, beq_iff_eq] at same; rw [same]
      | _ => simp [Closed.beq] at same

  theorem Closed.eq_of_beqList : ∀ (first second : List Closed),
      Closed.beqList first second = true → first = second
    | [], second, same => by cases second <;> first | rfl | simp [Closed.beqList] at same
    | head :: rest, second, same => by
      cases second with
      | nil => simp [Closed.beqList] at same
      | cons other others =>
        simp only [Closed.beqList, Bool.and_eq_true] at same
        rw [Closed.eq_of_beq head other same.1, Closed.eq_of_beqList rest others same.2]
end

/-- Every type of a list that a reading reads is itself in a type table, when each type that
the reading reads is. -/
private theorem fillAll_of_read (typeTable : TypeTable) (read : Ty → Option Closed)
    (each : ∀ (type : Ty) (closed : Closed), read type = some closed →
      Ty.fill typeTable type = some type) :
    ∀ (types : List Ty) {closed : List Closed}, types.mapM read = some closed →
      Ty.fillAll typeTable types = some types
  | [], _, _ => rfl
  | type :: rest, closed, readAll => by
    rw [List.mapM_cons] at readAll
    cases readType : read type with
    | none => simp [readType] at readAll
    | some first =>
      cases readRest : rest.mapM read with
      | none => simp [readType, readRest] at readAll
      | some others =>
        simp only [Ty.fillAll, each type first readType,
          fillAll_of_read typeTable read each rest readRest]

/-- A type of a package that a reading of some depth reads as a closed type of the vocabulary
is itself in every type table: it has no record and no variant in it. -/
private theorem fill_of_closed (typeTable : TypeTable) {types : Array CatalogueRow} :
    ∀ (depth : Nat) (type : Ty) (closed : Closed), closedOf.go types depth type = some closed →
      Ty.fill typeTable type = some type
  | 0, _, _, read => by simp [closedOf.go] at read
  | depth + 1, type, closed, read => by
    cases type with
    | bool => rfl
    | nat => rfl
    | fin bound => rfl
    | nominal row => rfl
    | seq element size =>
      simp only [closedOf.go, Option.map_eq_some_iff] at read
      obtain ⟨inner, readInner, _⟩ := read
      simp only [Ty.fill, fill_of_closed typeTable depth element inner readInner]
    | tuple components =>
      simp only [closedOf.go, Option.map_eq_some_iff] at read
      obtain ⟨inner, readAll, _⟩ := read
      simp only [Ty.fill, fillAll_of_read typeTable (closedOf.go types depth)
        (fill_of_closed typeTable depth) components readAll]
    | record declaration use fields => simp [closedOf.go] at read
    | variant declaration alternatives => simp [closedOf.go] at read

/-- A nominal type of a package stands for the units of a field or for a type of the
vocabulary. -/
private theorem closed_of_nominal {types : Array CatalogueRow} {depth row : Nat} {closed : Closed}
    (read : closedOf.go types depth (.nominal row) = some closed) :
    (∃ field, closed = .nonzero field) ∨ ∃ name, closed = .row name := by
  cases depth with
  | zero => simp [closedOf.go] at read
  | succ depth =>
    simp only [closedOf.go] at read
    cases found : types[row]? with
    | none => simp [found] at read
    | some entry =>
      simp only [found, Option.bind_eq_bind, Option.bind_some] at read
      split at read
      · obtain ⟨field, _, rfl⟩ := Option.map_eq_some_iff.mp read
        exact .inl ⟨field, rfl⟩
      · cases read
        exact .inr ⟨_, rfl⟩

/-- A type of a package that stands for an index is the index. -/
private theorem index_of_closed {types : Array CatalogueRow} {depth bound : Nat} {type : Ty}
    (read : closedOf.go types depth type = some (.index bound)) : type = .fin bound := by
  cases depth with
  | zero => simp [closedOf.go] at read
  | succ depth =>
    cases type with
    | fin other =>
      simp only [closedOf.go, Option.some.injEq, Closed.index.injEq] at read
      rw [read]
    | nominal row =>
      rcases closed_of_nominal read with ⟨_, isUnits⟩ | ⟨_, isRow⟩
      · cases isUnits
      · cases isRow
    | _ => simp [closedOf.go] at read

/-- The closed type of bytes: a collection of indices below 256, without a size. -/
abbrev bytesClosed : Closed := .seq (.index 256) none

/-- A type of a package that stands for the bytes of the vocabulary is the type of bytes. -/
theorem bytes_of_closed {types : Array CatalogueRow} {type : Ty}
    (read : closedOf types type = some bytesClosed) : type = bytesType := by
  unfold closedOf at read
  generalize types.size + typeParts type = depth at read
  cases depth with
  | zero => simp [closedOf.go] at read
  | succ depth =>
    cases type with
    | seq element size =>
      simp only [closedOf.go, Option.map_eq_some_iff, Closed.seq.injEq] at read
      obtain ⟨inner, readInner, rfl, rfl⟩ := read
      rw [index_of_closed readInner]
    | nominal row =>
      rcases closed_of_nominal read with ⟨_, isUnits⟩ | ⟨_, isRow⟩
      · cases isUnits
      · cases isRow
    | _ => simp [closedOf.go] at read

/-- A type of a package that stands for a closed type of the vocabulary is itself in every
type table: it has no record and no variant in it. -/
theorem fill_of_closedOf (typeTable : TypeTable) {types : Array CatalogueRow} {type : Ty}
    {closed : Closed} (read : closedOf types type = some closed) :
    Ty.fill typeTable type = some type :=
  fill_of_closed typeTable _ type closed read

/-- No type is the vocabulary's type of none. -/
theorem sameTypes_nil {types : Array CatalogueRow} {given : List Ty}
    (same : sameTypes types given [] = true) : given = [] := by
  cases given with
  | nil => rfl
  | cons type rest => simp [sameTypes] at same

/-- Types that are the vocabulary's closed types, the first of them: a type that stands for
the first closed type, and types that are the others. -/
theorem sameTypes_cons {types : Array CatalogueRow} {given : List Ty} {closed : Closed}
    {others : List Closed} (same : sameTypes types given (closed :: others) = true) :
    ∃ type rest, given = type :: rest ∧ closedOf types type = some closed ∧
      sameTypes types rest others = true := by
  cases given with
  | nil => simp [sameTypes] at same
  | cons type rest =>
    cases read : closedOf types type with
    | none => simp [sameTypes, read] at same
    | some found =>
      simp only [sameTypes, read, Bool.and_eq_true] at same
      exact ⟨type, rest, rfl, by rw [read, Closed.eq_of_beq found closed same.1], same.2⟩

/-- Types that are the vocabulary's closed types are themselves in every type table. -/
theorem sameTypes_filled (typeTable : TypeTable) {types : Array CatalogueRow} :
    ∀ {given : List Ty} {closed : List Closed}, sameTypes types given closed = true →
      Ty.fillAll typeTable given = some given
  | [], _, _ => rfl
  | type :: rest, [], same => by simp [sameTypes] at same
  | type :: rest, closed :: others, same => by
    obtain ⟨first, later, isCons, read, sameRest⟩ := sameTypes_cons same
    cases isCons
    simp only [Ty.fillAll, fill_of_closedOf typeTable read, sameTypes_filled typeTable sameRest]

/-! ## The rows of the layout in the vocabulary -/

/-- The rows of the vocabulary before the six rows of the canonical layout. -/
private def rowsBefore : List RowEntry :=
  Vocabulary.table.rows.take (Vocabulary.table.rows.length - 6)

/-- The six rows of the canonical layout, the last of the vocabulary. -/
private def layoutRows : List RowEntry := [
  { name := "layout.canonical.open", parameters := [], kind := .pure, inputs := [],
    outputs := [bytes] },
  { name := "layout.canonical.put", parameters := [.type none], kind := .pure
    inputs := [bytes, self], outputs := [bytes] },
  { name := "layout.canonical.close", parameters := [], kind := .pure, inputs := [bytes],
    outputs := [bytes] },
  { name := "layout.canonical.read", parameters := [], kind := .pure, inputs := [bytes],
    outputs := [bytes] },
  { name := "layout.canonical.take", parameters := [.type none], kind := .pure
    inputs := [bytes], outputs := [.bool, self, bytes] },
  { name := "layout.canonical.exhausted", parameters := [], kind := .pure, inputs := [bytes],
    outputs := [.bool] }]

private theorem rows_split : Vocabulary.table.rows = rowsBefore ++ layoutRows := by
  have last : Vocabulary.table.rows.drop (Vocabulary.table.rows.length - 6) = layoutRows := by rfl
  rw [← last]
  exact (List.take_append_drop _ Vocabulary.table.rows).symm

/-- The row of the vocabulary that a name and static arguments name, when its signature at
them is given: a row of the name whose parameters accept the arguments, with the inputs and
the outputs of the signature at them. -/
private theorem signature_entry {name : String} {arguments : List Value} {signature : Signature}
    (found : Vocabulary.table.signature? name arguments = some signature) :
    ∃ entry, entry ∈ Vocabulary.table.rows ∧ entry.name = name ∧
      entry.parameters.length = arguments.length ∧
      ((entry.parameters.zip arguments).all fun (parameter, argument) =>
        parameter.accepts Vocabulary.table argument) = true ∧
      entry.inputs.mapM (Term.at Vocabulary.table arguments) = some signature.inputs ∧
      entry.outputs.mapM (Term.at Vocabulary.table arguments) = some signature.outputs ∧
      signature.kind = entry.kind := by
  unfold Table.signature? at found
  cases row : Vocabulary.table.row? name arguments with
  | none => simp [row] at found
  | some entry =>
    have member : entry ∈ Vocabulary.table.rows := List.mem_of_find?_eq_some row
    have holds := List.find?_some row
    simp only [row, Option.bind_eq_bind, Option.bind_some] at found
    cases inputsAt : List.mapM (Term.at Vocabulary.table arguments) entry.inputs with
    | none => simp [inputsAt] at found
    | some inputs =>
      cases outputsAt : List.mapM (Term.at Vocabulary.table arguments) entry.outputs with
      | none => simp [inputsAt, outputsAt] at found
      | some outputs =>
        simp only [inputsAt, outputsAt, Option.bind_some, pure, Option.some.injEq] at found
        subst found
        simp only [Bool.and_eq_true, beq_iff_eq] at holds
        exact ⟨entry, member, holds.1.1, holds.1.2, holds.2, inputsAt, outputsAt, rfl⟩

/-- A row of the vocabulary with the name of a row of the canonical layout is one of the six
rows of the layout. -/
private theorem layout_entry {name : String} {entry : RowEntry}
    (member : entry ∈ Vocabulary.table.rows) (named : entry.name = name)
    (other : (rowsBefore.all fun earlier => earlier.name != name) = true) : entry ∈ layoutRows := by
  rw [rows_split] at member
  rcases List.mem_append.mp member with before | among
  · have differs := List.all_eq_true.mp other entry before
    simp [named] at differs
  · exact among

/-- A static argument that the parameter of a type accepts is a type. -/
private theorem accepts_type {argument : Value}
    (accepts : Parameter.accepts Vocabulary.table (.type none) argument = true) :
    ∃ closed, argument = .type closed := by
  cases argument with
  | type closed => exact ⟨closed, rfl⟩
  | natural value => simp [Parameter.accepts] at accepts

/-- The signature of the vocabulary's row that opens a writer: no static argument, no input
and one output of bytes. -/
theorem signature_open {arguments : List Value} {signature : Signature}
    (found : Vocabulary.table.signature? "layout.canonical.open" arguments = some signature) :
    arguments = [] ∧ signature.inputs = [] ∧ signature.outputs = [bytesClosed] := by
  obtain ⟨entry, member, named, counted, _, inputs, outputs, _⟩ := signature_entry found
  have among := layout_entry member named (by decide +kernel)
  simp only [layoutRows, List.mem_cons, List.not_mem_nil, or_false] at among
  rcases among with rfl | rfl | rfl | rfl | rfl | rfl <;> first
    | exact absurd named (by decide)
    | skip
  have none : arguments = [] := List.eq_nil_of_length_eq_zero counted.symm
  subst none
  exact ⟨rfl, (Option.some.inj inputs).symm, (Option.some.inj outputs).symm⟩

/-- The signature of the vocabulary's row that closes a writer: no static argument, one input
of bytes and one output of bytes. -/
theorem signature_close {arguments : List Value} {signature : Signature}
    (found : Vocabulary.table.signature? "layout.canonical.close" arguments = some signature) :
    arguments = [] ∧ signature.inputs = [bytesClosed] ∧ signature.outputs = [bytesClosed] := by
  obtain ⟨entry, member, named, counted, _, inputs, outputs, _⟩ := signature_entry found
  have among := layout_entry member named (by decide +kernel)
  simp only [layoutRows, List.mem_cons, List.not_mem_nil, or_false] at among
  rcases among with rfl | rfl | rfl | rfl | rfl | rfl <;> first
    | exact absurd named (by decide)
    | skip
  have none : arguments = [] := List.eq_nil_of_length_eq_zero counted.symm
  subst none
  exact ⟨rfl, (Option.some.inj inputs).symm, (Option.some.inj outputs).symm⟩

/-- The signature of the vocabulary's row that opens a reader: no static argument, one input
of bytes and one output of bytes. -/
theorem signature_read {arguments : List Value} {signature : Signature}
    (found : Vocabulary.table.signature? "layout.canonical.read" arguments = some signature) :
    arguments = [] ∧ signature.inputs = [bytesClosed] ∧ signature.outputs = [bytesClosed] := by
  obtain ⟨entry, member, named, counted, _, inputs, outputs, _⟩ := signature_entry found
  have among := layout_entry member named (by decide +kernel)
  simp only [layoutRows, List.mem_cons, List.not_mem_nil, or_false] at among
  rcases among with rfl | rfl | rfl | rfl | rfl | rfl <;> first
    | exact absurd named (by decide)
    | skip
  have none : arguments = [] := List.eq_nil_of_length_eq_zero counted.symm
  subst none
  exact ⟨rfl, (Option.some.inj inputs).symm, (Option.some.inj outputs).symm⟩

/-- The signature of the vocabulary's row that tests a reader: no static argument, one input
of bytes and one output, a `bool`. -/
theorem signature_exhausted {arguments : List Value} {signature : Signature}
    (found : Vocabulary.table.signature? "layout.canonical.exhausted" arguments = some signature) :
    arguments = [] ∧ signature.inputs = [bytesClosed] ∧ signature.outputs = [.bool] := by
  obtain ⟨entry, member, named, counted, _, inputs, outputs, _⟩ := signature_entry found
  have among := layout_entry member named (by decide +kernel)
  simp only [layoutRows, List.mem_cons, List.not_mem_nil, or_false] at among
  rcases among with rfl | rfl | rfl | rfl | rfl | rfl <;> first
    | exact absurd named (by decide)
    | skip
  have none : arguments = [] := List.eq_nil_of_length_eq_zero counted.symm
  subst none
  exact ⟨rfl, (Option.some.inj inputs).symm, (Option.some.inj outputs).symm⟩

/-- The static arguments of a row that takes one type: one closed type. -/
private theorem one_type {arguments : List Value}
    (counted : [Parameter.type none].length = arguments.length)
    (accepted : (([Parameter.type none].zip arguments).all fun (parameter, argument) =>
      parameter.accepts Vocabulary.table argument) = true) :
    ∃ closed, arguments = [.type closed] := by
  match arguments, counted, accepted with
  | [argument], _, accepted =>
    simp only [List.zip_cons_cons, List.zip_nil_right, List.all_cons, List.all_nil,
      Bool.and_true] at accepted
    obtain ⟨closed, rfl⟩ := accepts_type accepted
    exact ⟨closed, rfl⟩

/-- The signature of the vocabulary's row that puts a value: one static argument, a closed
type; the inputs are bytes and the type, and the output is bytes; the row is pure. -/
theorem signature_put {arguments : List Value} {signature : Signature}
    (found : Vocabulary.table.signature? "layout.canonical.put" arguments = some signature) :
    ∃ closed, arguments = [.type closed] ∧ signature.inputs = [bytesClosed, closed] ∧
      signature.outputs = [bytesClosed] ∧ signature.kind = .pure := by
  obtain ⟨entry, member, named, counted, accepted, inputs, outputs, kind⟩ :=
    signature_entry found
  have among := layout_entry member named (by decide +kernel)
  simp only [layoutRows, List.mem_cons, List.not_mem_nil, or_false] at among
  rcases among with rfl | rfl | rfl | rfl | rfl | rfl <;> first
    | exact absurd named (by decide)
    | skip
  obtain ⟨closed, rfl⟩ := one_type counted accepted
  exact ⟨closed, rfl, (Option.some.inj inputs).symm, (Option.some.inj outputs).symm, kind⟩

/-- The signature of the vocabulary's row that takes a value: one static argument, a closed
type; the input is bytes, and the outputs are a `bool`, the type and bytes; the row is pure. -/
theorem signature_take {arguments : List Value} {signature : Signature}
    (found : Vocabulary.table.signature? "layout.canonical.take" arguments = some signature) :
    ∃ closed, arguments = [.type closed] ∧ signature.inputs = [bytesClosed] ∧
      signature.outputs = [.bool, closed, bytesClosed] ∧ signature.kind = .pure := by
  obtain ⟨entry, member, named, counted, accepted, inputs, outputs, kind⟩ :=
    signature_entry found
  have among := layout_entry member named (by decide +kernel)
  simp only [layoutRows, List.mem_cons, List.not_mem_nil, or_false] at among
  rcases among with rfl | rfl | rfl | rfl | rfl | rfl <;> first
    | exact absurd named (by decide)
    | skip
  obtain ⟨closed, rfl⟩ := one_type counted accepted
  exact ⟨closed, rfl, (Option.some.inj inputs).symm, (Option.some.inj outputs).symm, kind⟩

/-! ## The rows of a package that the vocabulary reads -/

/-- The row of a package with a number is the row of a name at static arguments: the package
has the row, the row has the name, and the vocabulary reads its static arguments as these. -/
@[expose] def RowIs (package : Raw.Package) (row : Nat) (name : String) (arguments : List Value) :
    Prop :=
  ∃ operation, package.operations[row]? = some operation ∧
    operation.identity.name.toString = name ∧
    argumentsOf package.types.toArray operation.identity = some arguments

/-- Whether the row of a package with a number has a name. -/
@[expose] def rowNamed (package : Raw.Package) (row : Nat) (name : String) : Bool :=
  match package.operations[row]? with
  | some operation => operation.identity.name.toString == name
  | none => false

/-- A row of the typed table of a package that the core elaborates and whose rows are the
vocabulary's: the package has a row with that number, the vocabulary reads its static
arguments and has a row of its name at them, and the inputs and the outputs of the typed row
are the vocabulary's. -/
theorem typed_row_matched {package : Raw.Package} {typed : Typed}
    (elaborated : elaborate package = .ok typed)
    (matched : mismatches Vocabulary.table package = []) {row : Nat}
    {signature : OperationSignature}
    (valid : (typed.table.map (·.signature))[row]? = some signature) :
    ∃ operation arguments vocabulary,
      package.operations[row]? = some operation ∧
      argumentsOf package.types.toArray operation.identity = some arguments ∧
      Vocabulary.table.signature? operation.identity.name.toString arguments = some vocabulary ∧
      sameTypes package.types.toArray signature.inputs vocabulary.inputs = true ∧
      sameTypes package.types.toArray signature.outputs vocabulary.outputs = true := by
  rw [List.getElem?_map] at valid
  cases atFilled : typed.table[row]? with
  | none => rw [atFilled] at valid; cases valid
  | some filled =>
    rw [atFilled] at valid
    have signatureEq : filled.signature = signature := Option.some.inj valid
    obtain ⟨given, atGiven, fills⟩ := fillEach_getElem? (elaborate_table elaborated) atFilled
    obtain ⟨_, fillsInputs, fillsOutputs⟩ := fill_signature fills
    obtain ⟨arguments, vocabulary, read, found, _, sameInputs, sameOutputs⟩ :=
      mismatch_none (List.filterMap_eq_nil_iff.mp matched given (List.mem_of_getElem? atGiven))
    rw [sameTypes_filled _ sameInputs] at fillsInputs
    rw [sameTypes_filled _ sameOutputs] at fillsOutputs
    rw [← signatureEq, ← Option.some.inj fillsInputs, ← Option.some.inj fillsOutputs]
    exact ⟨given, arguments, vocabulary, atGiven, read, found, sameInputs, sameOutputs⟩

/-- A row of a package that has a name: the row and its name. -/
theorem rowNamed_some {package : Raw.Package} {row : Nat} {name : String}
    (named : rowNamed package row name = true) :
    ∃ operation, package.operations[row]? = some operation ∧
      operation.identity.name.toString = name := by
  unfold rowNamed at named
  cases found : package.operations[row]? with
  | none => simp [found] at named
  | some operation =>
    simp only [found, beq_iff_eq] at named
    exact ⟨operation, rfl, named⟩

end Vocabulary

open Vocabulary

/-! ## The canonical layout of a package -/

/-- Whether the rows that a declared layout names have the names of the rows of the canonical
layout: the four rows of the entry, every row that puts and every row that takes a value. It
reads the names alone, so it is decided on a package. -/
@[expose] def Raw.Layout.namesCanonical (package : Raw.Package) (raw : Raw.Layout) : Bool :=
  rowNamed package raw.start "layout.canonical.open" &&
    rowNamed package raw.close "layout.canonical.close" &&
    rowNamed package raw.read "layout.canonical.read" &&
    rowNamed package raw.exhausted "layout.canonical.exhausted" &&
    raw.putting.all (rowNamed package · "layout.canonical.put") &&
    raw.taking.all (rowNamed package · "layout.canonical.take")

/-- Whether a declaration has a layout whose rows have the names of the rows of the canonical
layout. -/
@[expose] def Raw.Declaration.namesCanonical (package : Raw.Package)
    (declaration : Raw.Declaration) : Bool :=
  match declaration.layout with
  | some raw => raw.namesCanonical package
  | none => false

/-- A layout over the rows of a package is the canonical one. Its writer, its reader and its
proof are bytes. Its rows of the entry are the package's rows `layout.canonical.open`,
`close`, `read` and `exhausted`, at no static argument. A row that puts or takes a value of a
type is the package's row `layout.canonical.put` or `take` at the closed type of the
vocabulary that the type stands for: the row that puts and the row that takes a value of one
type are at one closed type, the one of the type. -/
structure Layout.Canonical (package : Raw.Package) {operations : List OperationSignature}
    (layout : Layout operations) : Prop where
  writer : layout.writer = bytesType
  reader : layout.reader = bytesType
  proof : layout.proof = bytesType
  start : RowIs package layout.start.index "layout.canonical.open" []
  close : RowIs package layout.close.index "layout.canonical.close" []
  read : RowIs package layout.read.index "layout.canonical.read" []
  exhausted : RowIs package layout.exhausted.index "layout.canonical.exhausted" []
  put : ∀ {type : Ty} {put : Var operations ⟨[layout.writer, type], [layout.writer], .pure⟩},
    layout.put type = some put →
      ∃ closed, closedOf package.types.toArray type = some closed ∧
        RowIs package put.index "layout.canonical.put" [.type closed]
  take : ∀ {type : Ty}
    {take : Var operations ⟨[layout.reader], [.bool, type, layout.reader], .pure⟩},
    layout.take type = some take →
      ∃ closed, closedOf package.types.toArray type = some closed ∧
        RowIs package take.index "layout.canonical.take" [.type closed]

/-- The layout that a declared layout describes over the rows of a package is the canonical
one, when the core elaborates the package, the rows of the package are the vocabulary's, and
the rows that the declared layout names have the names of the rows of the canonical layout.

A row of the package with a name of the vocabulary has the vocabulary's signature at its
static arguments. So the rows of the entry have no static argument and are over bytes, which
makes the three types of the layout bytes; and a row that puts or takes a value of a type has
one static argument, the closed type that the type stands for. -/
theorem Layout.canonical_of_declared {package : Raw.Package} {typed : Typed}
    (elaborated : elaborate package = .ok typed)
    (matched : mismatches Vocabulary.table package = []) {raw : Raw.Layout}
    {layout : Layout (typed.table.map (·.signature))}
    (declared : Layout.ofRaw (tableScope (typed.table.map (·.signature))) raw = some layout)
    (named : raw.namesCanonical package = true) : layout.Canonical package := by
  have described := Layout.ofRaw_declaredBy declared
  simp only [Raw.Layout.namesCanonical, Bool.and_eq_true, List.all_eq_true] at named
  obtain ⟨⟨⟨⟨⟨namedStart, namedClose⟩, namedRead⟩, namedExhausted⟩, namedPut⟩, namedTake⟩ := named
  -- The row that opens a writer: its output, the writer, is bytes.
  obtain ⟨start, startArguments, startSignature, atStart, readStart, foundStart, _,
    startOutputs⟩ := typed_row_matched elaborated matched layout.start.valid
  obtain ⟨_, atStart', startName⟩ := rowNamed_some (described.start ▸ namedStart)
  obtain rfl := Option.some.inj (atStart.symm.trans atStart')
  rw [startName] at foundStart
  obtain ⟨rfl, _, startOut⟩ := signature_open foundStart
  rw [startOut] at startOutputs
  obtain ⟨_, _, isWriter, writerClosed, _⟩ := sameTypes_cons startOutputs
  obtain ⟨rfl, _⟩ := List.cons.inj isWriter
  have writerBytes := bytes_of_closed writerClosed
  -- The row that closes a writer: its output, the proof, is bytes.
  obtain ⟨close, closeArguments, closeSignature, atClose, readClose, foundClose, _,
    closeOutputs⟩ := typed_row_matched elaborated matched layout.close.valid
  obtain ⟨_, atClose', closeName⟩ := rowNamed_some (described.close ▸ namedClose)
  obtain rfl := Option.some.inj (atClose.symm.trans atClose')
  rw [closeName] at foundClose
  obtain ⟨rfl, _, closeOut⟩ := signature_close foundClose
  rw [closeOut] at closeOutputs
  obtain ⟨_, _, isProof, proofClosed, _⟩ := sameTypes_cons closeOutputs
  obtain ⟨rfl, _⟩ := List.cons.inj isProof
  have proofBytes := bytes_of_closed proofClosed
  -- The row that opens a reader: its output, the reader, is bytes.
  obtain ⟨read, readArguments, readSignature, atRead, readRead, foundRead, _,
    readOutputs⟩ := typed_row_matched elaborated matched layout.read.valid
  obtain ⟨_, atRead', readName⟩ := rowNamed_some (described.read ▸ namedRead)
  obtain rfl := Option.some.inj (atRead.symm.trans atRead')
  rw [readName] at foundRead
  obtain ⟨rfl, _, readOut⟩ := signature_read foundRead
  rw [readOut] at readOutputs
  obtain ⟨_, _, isReader, readerClosed, _⟩ := sameTypes_cons readOutputs
  obtain ⟨rfl, _⟩ := List.cons.inj isReader
  have readerBytes := bytes_of_closed readerClosed
  -- The row that tests a reader.
  obtain ⟨exhausted, exhaustedArguments, exhaustedSignature, atExhausted, readExhausted,
    foundExhausted, _, _⟩ := typed_row_matched elaborated matched layout.exhausted.valid
  obtain ⟨_, atExhausted', exhaustedName⟩ :=
    rowNamed_some (described.exhausted ▸ namedExhausted)
  obtain rfl := Option.some.inj (atExhausted.symm.trans atExhausted')
  rw [exhaustedName] at foundExhausted
  obtain ⟨rfl, _, _⟩ := signature_exhausted foundExhausted
  refine ⟨writerBytes, readerBytes, proofBytes, ⟨start, atStart, startName, readStart⟩,
    ⟨close, atClose, closeName, readClose⟩, ⟨read, atRead, readName, readRead⟩,
    ⟨exhausted, atExhausted, exhaustedName, readExhausted⟩, ?_, ?_⟩
  · -- A row that puts a value of a type: its second input, the type, stands for its static
    -- argument.
    intro type put row
    obtain ⟨operation, arguments, signature, found, read, vocabulary, inputs, _⟩ :=
      typed_row_matched elaborated matched put.valid
    obtain ⟨_, found', name⟩ := rowNamed_some (namedPut put.index (described.put row))
    obtain rfl := Option.some.inj (found.symm.trans found')
    rw [name] at vocabulary
    obtain ⟨closed, rfl, signatureInputs, _, _⟩ := signature_put vocabulary
    rw [signatureInputs] at inputs
    obtain ⟨_, _, isFirst, _, others⟩ := sameTypes_cons inputs
    obtain ⟨rfl, rfl⟩ := List.cons.inj isFirst
    obtain ⟨_, _, isSecond, typeClosed, _⟩ := sameTypes_cons others
    obtain ⟨rfl, _⟩ := List.cons.inj isSecond
    exact ⟨closed, typeClosed, operation, found, name, read⟩
  · -- A row that takes a value of a type: its second output, the type, stands for its static
    -- argument.
    intro type take row
    obtain ⟨operation, arguments, signature, found, read, vocabulary, _, outputs⟩ :=
      typed_row_matched elaborated matched take.valid
    obtain ⟨_, found', name⟩ := rowNamed_some (namedTake take.index (described.take row))
    obtain rfl := Option.some.inj (found.symm.trans found')
    rw [name] at vocabulary
    obtain ⟨closed, rfl, _, signatureOutputs, _⟩ := signature_take vocabulary
    rw [signatureOutputs] at outputs
    obtain ⟨_, _, isFirst, _, others⟩ := sameTypes_cons outputs
    obtain ⟨rfl, rfl⟩ := List.cons.inj isFirst
    obtain ⟨_, _, isSecond, typeClosed, _⟩ := sameTypes_cons others
    obtain ⟨rfl, _⟩ := List.cons.inj isSecond
    exact ⟨closed, typeClosed, operation, found, name, read⟩

/-! ## What the layout writes -/

namespace Vocabulary

/-- The format of the closed type that a type of a package stands for, when the type stands
for one and it has a format. -/
@[expose] def messageFormat (table : Table) (package : Raw.Package) (type : Ty) :
    Option (Format Datum) :=
  (closedOf package.types.toArray type).bind (formatOf table)

/-- The bytes that the canonical layout writes for a value of a type of a package: those that
the format of its closed type writes for its datum. A type without a format has no bytes. -/
@[expose] def encodeMessage (table : Table) (package : Raw.Package) (type : Ty)
    (value : Concrete.Value type) : Bytes :=
  match messageFormat table package type with
  | some format => format.write (Concrete.toDatum type value)
  | none => []

/-- Whether the canonical layout writes a value of a type of a package: the type has a
format, and the datum of the value is of the domain of the format. -/
@[expose] def writes (table : Table) (package : Raw.Package) (type : Ty)
    (value : Concrete.Value type) : Bool :=
  match messageFormat table package type with
  | some format => format.domain (Concrete.toDatum type value)
  | none => false

/-- A value that the layout writes, of a type that stands for a closed type: the closed type
has a format, the datum of the value is of its domain, and the bytes of the value are those
that the format writes for the datum. -/
theorem writes_format {table : Table} {package : Raw.Package} {type : Ty}
    {value : Concrete.Value type} (writable : writes table package type value = true)
    {closed : Closed} (closedIs : closedOf package.types.toArray type = some closed) :
    ∃ format, formatOf table closed = some format ∧
      format.domain (Concrete.toDatum type value) = true ∧
      encodeMessage table package type value = format.write (Concrete.toDatum type value) := by
  unfold writes at writable
  unfold encodeMessage
  simp only [messageFormat, closedIs, Option.bind_some] at writable ⊢
  cases built : formatOf table closed with
  | none => simp [built] at writable
  | some format =>
    simp only [built] at writable ⊢
    exact ⟨format, rfl, writable, rfl⟩

/-- The layout writes a value exactly when its type stands for a closed type with a format
and the datum of the value is of the domain of the format. -/
theorem writes_iff {table : Table} {package : Raw.Package} {type : Ty}
    {value : Concrete.Value type} :
    writes table package type value = true ↔
      ∃ closed format, closedOf package.types.toArray type = some closed ∧
        formatOf table closed = some format ∧
        format.domain (Concrete.toDatum type value) = true := by
  constructor
  · intro writable
    cases closedIs : closedOf package.types.toArray type with
    | none => simp [writes, messageFormat, closedIs] at writable
    | some closed =>
      obtain ⟨format, built, inDomain, _⟩ := writes_format writable closedIs
      exact ⟨closed, format, rfl, built, inDomain⟩
  · rintro ⟨closed, format, closedIs, built, inDomain⟩
    simp only [writes, messageFormat, closedIs, Option.bind_some, built]
    exact inDomain

/-! ## The rows of the layout on a writer and a reader that are bytes

The statements about the rows in the model of a package are for a writer, a reader and a
proof of the type of bytes. A layout that is the canonical one has these types up to an
equation, along which a writer and a reader are read as bytes. -/

/-- Bytes as a value of a type that is the type of bytes. -/
@[expose] def valueOfBytes {type : Ty} (isBytes : type = bytesType) (bytes : Bytes) :
    Concrete.Value type :=
  cast (congrArg Concrete.Value isBytes.symm) bytes

/-- A value of a type that is the type of bytes, as bytes. -/
@[expose] def bytesOfValue {type : Ty} (isBytes : type = bytesType)
    (value : Concrete.Value type) : Bytes :=
  cast (congrArg Concrete.Value isBytes) value

theorem bytesOfValue_valueOfBytes {type : Ty} (isBytes : type = bytesType) (bytes : Bytes) :
    bytesOfValue isBytes (valueOfBytes isBytes bytes) = bytes := by
  subst isBytes
  rfl

theorem valueOfBytes_bytesOfValue {type : Ty} (isBytes : type = bytesType)
    (value : Concrete.Value type) : valueOfBytes isBytes (bytesOfValue isBytes value) = value := by
  subst isBytes
  rfl

variable {package : Raw.Package}

/-- The writer that the row `layout.canonical.open` gives has no bytes. -/
theorem opened_bytes {row : Nat} {writer : Ty} (writerIs : writer = bytesType)
    (populated : Ty.allPopulated [writer] = true)
    (rowIs : RowIs package row "layout.canonical.open" []) :
    bytesOfValue writerIs (((model Vocabulary.table package).pure ⟨row, [], [writer]⟩ populated
      .nil).get .here) = [] := by
  subst writerIs
  obtain ⟨operation, found, named, read⟩ := rowIs
  rw [model_open found named read populated]
  rfl

/-- The row `layout.canonical.put` on a value of the domain of the format of its type appends
the bytes that the format writes for the value. -/
theorem put_bytes {row : Nat} {writer : Ty} (writerIs : writer = bytesType)
    (populated : Ty.allPopulated [writer] = true) {type : Ty} {closed : Closed}
    (rowIs : RowIs package row "layout.canonical.put" [.type closed]) {format : Format Datum}
    (built : formatOf Vocabulary.table closed = some format) (lawful : format.Lawful)
    (current : Concrete.Value writer) (value : Concrete.Value type)
    (inDomain : format.domain (Concrete.toDatum type value) = true) :
    bytesOfValue writerIs (((model Vocabulary.table package).pure ⟨row, [writer, type], [writer]⟩
      populated (.cons current (.cons value .nil))).get .here) =
        bytesOfValue writerIs current ++ format.write (Concrete.toDatum type value) := by
  subst writerIs
  obtain ⟨operation, found, named, read⟩ := rowIs
  rw [model_put found named read built lawful populated current value inDomain]
  rfl

/-- The row `layout.canonical.read` on what the row `layout.canonical.close` makes of a
writer gives the bytes of the writer. -/
theorem close_read_bytes {closeRow readRow : Nat} {writer reader proof : Ty}
    (writerIs : writer = bytesType) (readerIs : reader = bytesType) (proofIs : proof = bytesType)
    (proofPopulated : Ty.allPopulated [proof] = true)
    (readerPopulated : Ty.allPopulated [reader] = true)
    (closeIs : RowIs package closeRow "layout.canonical.close" [])
    (readIs : RowIs package readRow "layout.canonical.read" [])
    (current : Concrete.Value writer) :
    ((model Vocabulary.table package).pure ⟨readRow, [proof], [reader]⟩ readerPopulated
      (.cons (((model Vocabulary.table package).pure ⟨closeRow, [writer], [proof]⟩
        proofPopulated (.cons current .nil)).get .here) .nil)).get .here =
      valueOfBytes readerIs (bytesOfValue writerIs current) := by
  subst writerIs
  subst readerIs
  subst proofIs
  obtain ⟨closing, foundClose, namedClose, readClose⟩ := closeIs
  obtain ⟨reading, foundRead, namedRead, readRead⟩ := readIs
  rw [model_close foundClose namedClose readClose proofPopulated current, Values.get_here,
    model_read foundRead namedRead readRead readerPopulated current]
  rfl

/-- The row `layout.canonical.take`, on a reader that is the bytes which the format of its
type writes for a value of its domain, followed by anything, gives the flag `true`, the value
and what follows. -/
theorem take_bytes {row : Nat} {reader : Ty} (readerIs : reader = bytesType) {type : Ty}
    (populated : Ty.allPopulated [.bool, type, reader] = true) {closed : Closed}
    (rowIs : RowIs package row "layout.canonical.take" [.type closed]) {format : Format Datum}
    (built : formatOf Vocabulary.table closed = some format) (lawful : format.Lawful)
    (value : Concrete.Value type)
    (inDomain : format.domain (Concrete.toDatum type value) = true) (rest : Bytes) :
    (model Vocabulary.table package).pure ⟨row, [reader], [.bool, type, reader]⟩ populated
        (.cons (valueOfBytes readerIs (format.write (Concrete.toDatum type value) ++ rest))
          .nil) =
      .cons true (.cons value (.cons (valueOfBytes readerIs rest) .nil)) := by
  subst readerIs
  obtain ⟨operation, found, named, read⟩ := rowIs
  exact model_take found named read built lawful populated value inDomain rest

/-- The row `layout.canonical.exhausted` on a reader without bytes gives `true`. -/
theorem exhausted_bytes {row : Nat} {reader : Ty} (readerIs : reader = bytesType)
    (populated : Ty.allPopulated [.bool] = true)
    (rowIs : RowIs package row "layout.canonical.exhausted" []) :
    ((model Vocabulary.table package).pure ⟨row, [reader], [.bool]⟩ populated
      (.cons (valueOfBytes readerIs []) .nil)).get .here = true := by
  subst readerIs
  obtain ⟨operation, found, named, read⟩ := rowIs
  rw [model_exhausted found named read populated]
  rfl

end Vocabulary

/-! ## The laws -/

/-- A type that the layout puts or takes a value of has a point of G1 in it. -/
@[expose] def Layout.MovesPoint (package : Raw.Package) {operations : List OperationSignature}
    (layout : Layout operations) : Prop :=
  ∃ (type : Ty) (closed : Closed),
    ((layout.put type).isSome = true ∨ (layout.take type).isSome = true) ∧
      closedOf package.types.toArray type = some closed ∧
      containsPoint Vocabulary.table closed = true

/-- The laws of the canonical layout of a package, in the model of the vocabulary's rows of the
package.

The wire is bytes, the empty content no bytes and the append `++`. A value of a type is
written as the bytes that the format of its closed type writes for its datum
(`encodeMessage`), and it is writable when its type has a format and its datum is of the
domain of the format (`writes`). The content of a writer is its bytes, and the reader of a
content is those bytes.

The one hypothesis that is not a fact about the package is the compressed encoding of G1,
asked only when a type that the layout puts or takes has a point of G1 in it. -/
@[expose] def Layout.Canonical.laws {package : Raw.Package} {operations : List OperationSignature}
    {layout : Layout operations} (canonical : layout.Canonical package)
    (compression : layout.MovesPoint package → PointCompression) :
    layout.Lawful (model Vocabulary.table package) where
  Wire := Bytes
  empty := []
  append := fun first second => first ++ second
  append_assoc := List.append_assoc
  empty_append := List.nil_append
  append_empty := List.append_nil
  encode := encodeMessage Vocabulary.table package
  Writable := fun type value => writes Vocabulary.table package type value = true
  ofWriter := bytesOfValue canonical.writer
  toReader := valueOfBytes canonical.reader
  start_empty := opened_bytes canonical.writer layout.writerPopulated canonical.start
  put_appends := by
    intro type put row value writable writer
    obtain ⟨closed, closedIs, rowIs⟩ := canonical.put row
    obtain ⟨format, built, inDomain, written⟩ := writes_format writable closedIs
    have lawful : format.Lawful := formatOf_lawful Vocabulary.table closed built fun has =>
      compression ⟨type, closed, .inl (by rw [row]; rfl), closedIs, has⟩
    rw [written]
    exact put_bytes canonical.writer layout.writerPopulated rowIs built lawful writer value
      inDomain
  close_read := fun writer =>
    close_read_bytes canonical.writer canonical.reader canonical.proof layout.proofPopulated
      layout.readerPopulated canonical.close canonical.read writer
  take_reads := by
    intro type take populated row value writable rest
    obtain ⟨closed, closedIs, rowIs⟩ := canonical.take row
    obtain ⟨format, built, inDomain, written⟩ := writes_format writable closedIs
    have lawful : format.Lawful := formatOf_lawful Vocabulary.table closed built fun has =>
      compression ⟨type, closed, .inr (by rw [row]; rfl), closedIs, has⟩
    rw [written]
    exact take_bytes canonical.reader populated rowIs built lawful value inDomain rest
  exhausted_empty := exhausted_bytes canonical.reader rfl canonical.exhausted

/-! ## The types that the layout of an admitted package moves have formats -/

/-- A row of a package that the vocabulary admits, with the name of the row of the layout that
puts or takes a value, at a closed type: the type has a format. Admission of such a row is the
existence of the format. -/
private theorem row_format_of_admitted {package : Raw.Package}
    (admitted : missing Vocabulary.table package = []) {row : Nat} {name : String}
    {closed : Closed} (rowIs : RowIs package row name [.type closed])
    (uses : usesFormat Vocabulary.table name = true)
    (isPure : ∀ {arguments : List Value} {signature : Signature},
      Vocabulary.table.signature? name arguments = some signature → signature.kind = .pure) :
    (formatOf Vocabulary.table closed).isSome = true := by
  obtain ⟨operation, found, named, read⟩ := rowIs
  have none := List.filterMap_eq_nil_iff.mp admitted operation (List.mem_of_getElem? found)
  cases same : mismatch Vocabulary.table package operation with
  | some message => simp [same] at none
  | none =>
    simp only [same] at none
    obtain ⟨arguments, signature, _, vocabulary, sameKinds, _, _⟩ := mismatch_none same
    rw [named] at vocabulary
    rw [isPure vocabulary] at sameKinds
    have kind : operation.signature.kind = .pure := by
      cases shape : operation.signature.kind <;> simp [shape, sameKind] at sameKinds ⊢
    have computes : (OperationKind.pure == OperationKind.sampling) = false := by decide
    have argument : typeArgument [Value.type closed] 0 = some closed := by simp [typeArgument]
    unfold unimplemented at none
    simp only [kind, read, named, uses, computes, argument, Bool.false_eq_true, ↓reduceIte,
      Option.bind_some] at none
    cases built : formatOf Vocabulary.table closed with
    | none => simp [built] at none
    | some format => rfl

/-- In a package that the vocabulary admits, a type that the canonical layout puts or takes a
value of has a format: the layout writes the values of the type that are of the domain of the
format, and `writes` is not `false` on the whole type for want of a format. -/
theorem Layout.Canonical.format_of_admitted {package : Raw.Package}
    {operations : List OperationSignature} {layout : Layout operations}
    (canonical : layout.Canonical package) (admitted : missing Vocabulary.table package = [])
    {type : Ty} (moved : (layout.put type).isSome = true ∨ (layout.take type).isSome = true) :
    (messageFormat Vocabulary.table package type).isSome = true := by
  rcases moved with puts | takes
  · cases row : layout.put type with
    | none => simp [row] at puts
    | some put =>
      obtain ⟨closed, closedIs, rowIs⟩ := canonical.put row
      simp only [messageFormat, closedIs, Option.bind_some]
      exact row_format_of_admitted admitted rowIs (by decide +kernel)
        fun vocabulary => (signature_put vocabulary).choose_spec.2.2.2
  · cases row : layout.take type with
    | none => simp [row] at takes
    | some take =>
      obtain ⟨closed, closedIs, rowIs⟩ := canonical.take row
      simp only [messageFormat, closedIs, Option.bind_some]
      exact row_format_of_admitted admitted rowIs (by decide +kernel)
        fun vocabulary => (signature_take vocabulary).choose_spec.2.2.2

/-! ## The laws from what is checked of a package and its declaration -/

namespace Vocabulary

/-- Whether the row of a package with a number is at one static argument, a closed type with
a point of G1 in it. -/
@[expose] def rowMovesPoint (table : Table) (package : Raw.Package) (row : Nat) : Bool :=
  match package.operations[row]? with
  | some operation =>
    match argumentsOf package.types.toArray operation.identity with
    | some [.type closed] => containsPoint table closed
    | _ => false
  | none => false

end Vocabulary

/-- Whether a row that a declared layout names to put or to take a value is at a closed type
with a point of G1 in it. It is decided on a package. -/
@[expose] def Raw.Layout.movesPoint (table : Table) (package : Raw.Package) (raw : Raw.Layout) :
    Bool :=
  (raw.putting ++ raw.taking).any (rowMovesPoint table package)

/-- Whether the layout of a declaration puts or takes a value of a type with a point of G1 in
it. A declaration without a layout does not. -/
@[expose] def Raw.Declaration.movesPoint (table : Table) (package : Raw.Package)
    (declaration : Raw.Declaration) : Bool :=
  match declaration.layout with
  | some raw => raw.movesPoint table package
  | none => false

/-- When a type that the canonical layout of a package puts or takes has a point of G1 in
it, a row that the declared layout names to put or to take a value is at a closed type with a
point of G1 in it. -/
theorem Layout.Canonical.declared_movesPoint {package : Raw.Package}
    {operations : List OperationSignature} {layout : Layout operations}
    (canonical : layout.Canonical package) {raw : Raw.Layout} (described : layout.DeclaredBy raw)
    (moves : layout.MovesPoint package) :
    raw.movesPoint Vocabulary.table package = true := by
  obtain ⟨type, closed, moved, closedIs, has⟩ := moves
  unfold Raw.Layout.movesPoint
  rw [List.any_eq_true]
  rcases moved with puts | takes
  · cases row : layout.put type with
    | none => simp [row] at puts
    | some put =>
      obtain ⟨found, foundIs, operation, atRow, _, read⟩ := canonical.put row
      obtain rfl := Option.some.inj (foundIs.symm.trans closedIs)
      exact ⟨put.index, List.mem_append_left _ (described.put row), by
        simp only [rowMovesPoint, atRow, read, has]⟩
  · cases row : layout.take type with
    | none => simp [row] at takes
    | some take =>
      obtain ⟨found, foundIs, operation, atRow, _, read⟩ := canonical.take row
      obtain rfl := Option.some.inj (foundIs.symm.trans closedIs)
      exact ⟨take.index, List.mem_append_right _ (described.take row), by
        simp only [rowMovesPoint, atRow, read, has]⟩

/-- The layout that a declaration describes is the one that its declared layout describes. -/
theorem Layout.declared_of_declaration {declaration : Raw.Declaration}
    {operations : List OperationSignature} {rows : Scope operations} {layout : Layout operations}
    (declared : declaration.layout.bind (Layout.ofRaw rows) = some layout) :
    ∃ raw, declaration.layout = some raw ∧ Layout.ofRaw rows raw = some layout := by
  cases found : declaration.layout with
  | none => simp [found] at declared
  | some raw =>
    rw [found] at declared
    exact ⟨raw, rfl, declared⟩

/-- The layout of a declaration over the rows of a package is the canonical one, when the core
elaborates the package, the rows of the package are the vocabulary's, and the rows that the
declaration names for its layout have the names of the rows of the canonical layout. -/
theorem Layout.canonical_of_declaration {package : Raw.Package} {typed : Typed}
    {declaration : Raw.Declaration} {layout : Layout (typed.table.map (·.signature))}
    (elaborated : elaborate package = .ok typed)
    (matched : mismatches Vocabulary.table package = [])
    (declared : declaration.layout.bind
      (Layout.ofRaw (tableScope (typed.table.map (·.signature)))) = some layout)
    (named : declaration.namesCanonical package = true) : layout.Canonical package := by
  obtain ⟨raw, found, isLayout⟩ := Layout.declared_of_declaration declared
  simp only [Raw.Declaration.namesCanonical, found] at named
  exact Layout.canonical_of_declared elaborated matched isLayout named

/-- When a type that the layout of a declaration puts or takes has a point of G1 in it, the
declaration says so (`Raw.Declaration.movesPoint`). -/
theorem Layout.movesPoint_of_declaration {package : Raw.Package} {typed : Typed}
    {declaration : Raw.Declaration} {layout : Layout (typed.table.map (·.signature))}
    (elaborated : elaborate package = .ok typed)
    (matched : mismatches Vocabulary.table package = [])
    (declared : declaration.layout.bind
      (Layout.ofRaw (tableScope (typed.table.map (·.signature)))) = some layout)
    (named : declaration.namesCanonical package = true) (moves : layout.MovesPoint package) :
    declaration.movesPoint Vocabulary.table package = true := by
  obtain ⟨raw, found, isLayout⟩ := Layout.declared_of_declaration declared
  simp only [Raw.Declaration.namesCanonical, found] at named
  simp only [Raw.Declaration.movesPoint, found]
  exact (Layout.canonical_of_declared elaborated matched isLayout named).declared_movesPoint
    (Layout.ofRaw_declaredBy isLayout) moves

namespace Vocabulary

/-- The laws of the layout of a declaration, in the model of the vocabulary's rows of the
package (`Layout.Canonical.laws`).

What is checked of the package and the declaration: the core elaborates the package, the rows
of the package are the vocabulary's, the declaration has a layout over those rows, and the
rows that it names have the names of the rows of the canonical layout. The compressed
encoding of G1 is asked only when the declared layout puts or takes a value of a type with a
point of G1 in it. -/
@[expose] def canonicalLaws {package : Raw.Package} {typed : Typed} {declaration : Raw.Declaration}
    {layout : Layout (typed.table.map (·.signature))}
    (elaborated : elaborate package = .ok typed)
    (matched : mismatches Vocabulary.table package = [])
    (declared : declaration.layout.bind
      (Layout.ofRaw (tableScope (typed.table.map (·.signature)))) = some layout)
    (named : declaration.namesCanonical package = true)
    (compression : declaration.movesPoint Vocabulary.table package = true → PointCompression) :
    layout.Lawful (model Vocabulary.table package) :=
  (Layout.canonical_of_declaration elaborated matched declared named).laws fun moves =>
    compression (Layout.movesPoint_of_declaration elaborated matched declared named moves)

/-- The laws of the layout of a declaration that puts and takes no value of a type with a
point of G1 in it: every premise is checked of the package and the declaration. -/
@[expose] def canonicalLawsWithoutPoint {package : Raw.Package} {typed : Typed}
    {declaration : Raw.Declaration} {layout : Layout (typed.table.map (·.signature))}
    (elaborated : elaborate package = .ok typed)
    (matched : mismatches Vocabulary.table package = [])
    (declared : declaration.layout.bind
      (Layout.ofRaw (tableScope (typed.table.map (·.signature)))) = some layout)
    (named : declaration.namesCanonical package = true)
    (noPoint : declaration.movesPoint Vocabulary.table package = false) :
    layout.Lawful (model Vocabulary.table package) :=
  canonicalLaws elaborated matched declared named fun moves =>
    Bool.noConfusion (noPoint.symm.trans moves)

/-- A value is writable under the laws exactly when the layout writes it. -/
theorem laws_writable {package : Raw.Package} {operations : List OperationSignature}
    {layout : Layout operations} (canonical : layout.Canonical package)
    (compression : layout.MovesPoint package → PointCompression) (type : Ty)
    (value : Concrete.Value type) :
    (canonical.laws compression).Writable type value ↔
      writes Vocabulary.table package type value = true :=
  Iff.rfl

/-- The content that the laws give a value is the bytes that the layout writes for it. -/
theorem laws_encode {package : Raw.Package} {operations : List OperationSignature}
    {layout : Layout operations} (canonical : layout.Canonical package)
    (compression : layout.MovesPoint package → PointCompression) (type : Ty)
    (value : Concrete.Value type) :
    (canonical.laws compression).encode type value =
      encodeMessage Vocabulary.table package type value :=
  rfl

end Vocabulary

end Zkc.Core
