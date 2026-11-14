import Zkc.Tests.Core.Threading
import Zkc.Tests.Core.ThreadingSumcheck
import Zkc.Tests.Core.ConstructSchnorr
import Zkc.Core.CanonicalLayoutLaws
import Zkc.Core.CanonicalLayoutValues

/-! The laws of the canonical layout in the model of the vocabulary, at packages.

`Vocabulary.canonicalLaws` gives `Layout.Lawful` for the layout of a declaration in the model
of the vocabulary's rows of a package. Its premises are that the core elaborates the package,
that the rows of the package are the vocabulary's, that the declaration has a layout over them
and that the rows it names have the names of the rows of the canonical layout; and the
compressed encoding of G1 when a declared row is at a type with a point of G1 in it.

- `fixtures/construction/collecting.json` with its declaration: every premise is evaluated by
  the kernel and no hypothesis remains (`Collecting.laws`). The round trip of
  `Layout.Lawful.round_trip` at two elements of the field, with the 64 bytes that were written.
  The vocabulary admits the package, so the field has a format
  (`Layout.Canonical.format_of_admitted`). The order of the field is a value of the type that
  the layout does not write. The two values that the prover sends, the results of `field.add`
  and `field.mul`, are written whatever those rows were given.
- `fixtures/construction/sumcheck.json` and `schnorr.json` with their declarations: the
  premises fail. The packages name their rows by catalogue domains that the vocabulary does not
  read (`proof.open`, `proof.put`), so their rows are not the vocabulary's and the declared
  rows do not have the names of the canonical layout. Their layouts have no laws at all in the
  model of the vocabulary (`Sumcheck.no_laws`, `Schnorr.no_laws`): the model implements none
  of their rows, and the row that tests a reader gives `false` on every reader.
- The protocols of `schnorr.json` over tables that name the vocabulary's rows
  (`SchnorrVocabulary`; the package that the frontend prints with these rows is in
  `Tests/Core/VocabularyScheme.lean`): every premise but one is evaluated by the kernel, and
  the laws take the compressed encoding of G1 as their one hypothesis, because the prover
  sends a point. The round trip at every point of the group and every element of the field,
  and at the point at infinity and 5. The response that the prover sends is written; the
  commitment is written exactly when the multiple of the base is a point of the group.
- A package in which the row that takes a point has the name of the canonical layout and the
  field as its static argument (`Mismatched`): the core elaborates it and the declared rows
  have the names, but one row is not the vocabulary's. The layout is not the canonical one,
  and under no laws of it is the point at infinity writable: the reader gives the number of
  the first 32 of its 48 bytes.

The axioms of every theorem of `Zkc.Core.CanonicalLayoutLaws` and
`Zkc.Core.CanonicalLayoutValues` and of the statements here are printed at the end.
-/

set_option autoImplicit false

open Zkc.Source Zkc.Core
open Zkc.Core.Concrete (Datum)

namespace CanonicalLayoutLaws

/-- The layout that a declaration describes, when the kernel finds one, is the layout of the
declaration. -/
theorem declared_get {operations : List OperationSignature} (declaration : Raw.Declaration)
    (isSome : (declaration.layout.bind (Layout.ofRaw (tableScope operations))).isSome = true) :
    declaration.layout.bind (Layout.ofRaw (tableScope operations)) =
      some ((declaration.layout.bind (Layout.ofRaw (tableScope operations))).get isSome) :=
  (Option.some_get isSome).symm

/-! ## `collecting.json` -/

namespace Collecting

open Threading (raw declaration typed layout)

/-- The model of the vocabulary's rows of the package. -/
noncomputable abbrev model : Model := Vocabulary.model Vocabulary.table raw

kernel_refl matched : Vocabulary.mismatches Vocabulary.table raw equals []

kernel_refl named : declaration.namesCanonical raw equals true

kernel_refl no_point : declaration.movesPoint Vocabulary.table raw equals false

theorem declared :
    declaration.layout.bind (Layout.ofRaw (tableScope (typed.table.map (·.signature)))) =
      some layout :=
  declared_get declaration Threading.layout_declared

/-- The layout of the declaration is the canonical one of the package. -/
theorem canonical : layout.Canonical raw :=
  Layout.canonical_of_declaration Threading.typed_eq matched declared named

/-- The laws of the layout of the declaration, in the model of the vocabulary: every premise
is evaluated by the kernel, and there is no hypothesis. -/
noncomputable def laws : layout.Lawful model :=
  Vocabulary.canonicalLawsWithoutPoint Threading.typed_eq matched declared named no_point

/-! ### A round trip at two elements of the field

The one message type of the package is its field, the nominal type 0 (`bls12-381.fr`): an
element is written in 32 bytes, least significant first. -/

kernel_refl put_declared : (layout.put (.nominal 0)).isSome equals true

/-- The row that puts an element of the field. -/
noncomputable def put :
    Var Threading.operations ⟨[layout.writer, .nominal 0], [layout.writer], .pure⟩ :=
  (layout.put (.nominal 0)).get put_declared

theorem put_row : layout.put (.nominal 0) = some put := (Option.some_get put_declared).symm

-- The rows that put and take an element are the rows 12 and 13 of the package, and the layout
-- has no row for another type.
kernel_refl message_rows :
  ((layout.put (.nominal 0)).map (·.index), (layout.take (.nominal 0)).map (·.index),
    (layout.put .bool).isSome, (layout.take .nat).isSome)
  equals (some 12, some 13, false, false)

/-- The elements 5 and 258. -/
abbrev first : Datum := .number 5

abbrev second : Datum := .number 258

noncomputable abbrev messages : List (Message model) := [⟨.nominal 0, first⟩, ⟨.nominal 0, second⟩]

-- The layout writes both, and it does not write the order of the field, which is a value of
-- the carrier of the type and no element.
kernel_refl elements_written :
  (Vocabulary.writes Vocabulary.table raw (.nominal 0) first,
    Vocabulary.writes Vocabulary.table raw (.nominal 0) second,
    Vocabulary.writes Vocabulary.table raw (.nominal 0) (Datum.number Vocabulary.bls12381Order))
  equals (true, true, false)

-- The bytes of the two: 64 bytes, each element in 32, least significant first.
kernel_refl elements_encoded :
  ((Vocabulary.encodeMessage Vocabulary.table raw (.nominal 0) first ++
    Vocabulary.encodeMessage Vocabulary.table raw (.nominal 0) second).map (·.val))
  equals ([5] ++ List.replicate 31 0 ++ [2, 1] ++ List.replicate 30 0)

-- The vocabulary admits the package, so the type that the layout moves has a format.
kernel_refl admitted : Vocabulary.missing Vocabulary.table raw equals []

/-- The field has a format: the layout writes its elements. -/
theorem field_format :
    (Vocabulary.messageFormat Vocabulary.table raw (.nominal 0)).isSome = true :=
  canonical.format_of_admitted admitted (.inl put_declared)

/-- The layout carries the elements of the field. -/
theorem carries : layout.Carries (.nominal 0) :=
  ⟨kernel_rfl%, Option.isSome_iff_exists.mp put_declared,
    Option.isSome_iff_exists.mp
      (show (layout.take (.nominal 0)).isSome = true from kernel_rfl%)⟩

theorem first_written : Vocabulary.writes Vocabulary.table raw (.nominal 0) first = true :=
  congrArg (fun flags : Bool × Bool × Bool => flags.1) elements_written

theorem second_written : Vocabulary.writes Vocabulary.table raw (.nominal 0) second = true :=
  congrArg (fun flags : Bool × Bool × Bool => flags.2.1) elements_written

/-- Both elements can be sent under the laws. -/
theorem sendable : ∀ message ∈ messages, laws.Sendable message.1 message.2 := by
  intro message member
  rcases List.mem_cons.mp member with rfl | later
  · exact ⟨carries, first_written⟩
  · rw [List.mem_singleton.mp later]
    exact ⟨carries, second_written⟩

/-- Putting the two elements on the writer that the layout opens. -/
theorem written : layout.Written model (layout.opened model) messages
    (layout.putValue model put (layout.putValue model put (layout.opened model) first) second) :=
  .cons put put_row (.cons put put_row (.nil _))

/-- The round trip at the two elements: they are taken, in order, from the reader of the
closed writer, which is then exhausted. -/
theorem round_trip : ∃ reader,
    layout.Takes model
      (layout.reading model (layout.closed model
        (layout.putValue model put (layout.putValue model put (layout.opened model) first) second)))
      messages reader ∧
    layout.isExhausted model reader = true :=
  laws.round_trip sendable written

/-- What was written is the 64 bytes of the two elements. -/
theorem written_bytes :
    laws.ofWriter
        (layout.putValue model put (layout.putValue model put (layout.opened model) first) second) =
      Vocabulary.encodeMessage Vocabulary.table raw (.nominal 0) first ++
        (Vocabulary.encodeMessage Vocabulary.table raw (.nominal 0) second ++ []) := by
  have content := laws.written_content written fun message member => (sendable message member).2
  rw [laws.start_empty, laws.empty_append] at content
  exact content

/-! ### The values that the protocol sends

In `rounds` the prover sends the result of the row 1, `field.add`, and the result of the row
2, `field.mul`. Whatever values these rows are given, the layout writes what they return. -/

/-- The layout writes the sum that the row `field.add` of the package returns. -/
theorem sum_written (arguments : Values Concrete.Value [.nominal 0, .nominal 0]) :
    laws.Writable (.nominal 0)
      ((model.pure ⟨1, [.nominal 0, .nominal 0], [.nominal 0]⟩ rfl arguments).get .here) :=
  Vocabulary.model_arithmetic_writes
    (operation := ⟨⟨Name.ofString "field.add", [.type (.nominal 0)]⟩,
      ⟨[.nominal 0, .nominal 0], [.nominal 0], .pure⟩⟩)
    (name := "field.add") (field := "bls12-381.fr") (order := Vocabulary.bls12381Order)
    (width := 32) kernel_rfl% kernel_rfl% (by decide) kernel_rfl% kernel_rfl% kernel_rfl%
    (by decide) rfl arguments

/-- The layout writes the product that the row `field.mul` of the package returns. -/
theorem product_written (arguments : Values Concrete.Value [.nominal 0, .nominal 0]) :
    laws.Writable (.nominal 0)
      ((model.pure ⟨2, [.nominal 0, .nominal 0], [.nominal 0]⟩ rfl arguments).get .here) :=
  Vocabulary.model_arithmetic_writes
    (operation := ⟨⟨Name.ofString "field.mul", [.type (.nominal 0)]⟩,
      ⟨[.nominal 0, .nominal 0], [.nominal 0], .pure⟩⟩)
    (name := "field.mul") (field := "bls12-381.fr") (order := Vocabulary.bls12381Order)
    (width := 32) kernel_rfl% kernel_rfl% (by decide) kernel_rfl% kernel_rfl% kernel_rfl%
    (by decide) rfl arguments

end Collecting

/-! ## `sumcheck.json` and `schnorr.json`

The two packages name their rows by catalogue domains (`proof.open`, `proof.put`, a field as
`field` at the domain `scalar`), which the vocabulary does not read, and their writer, reader
and proof are nominal types. Their rows are not the vocabulary's, the rows that their
declarations name do not have the names of the rows of the canonical layout, and their layouts
have no laws in the model of the vocabulary: the model implements none of their rows, so the
row that tests a reader gives `false` on every reader. -/

namespace Sumcheck

open ThreadingSumcheck (raw declaration typed layout)

noncomputable abbrev model : Model := Vocabulary.model Vocabulary.table raw

kernel_refl not_matched : (Vocabulary.mismatches Vocabulary.table raw).isEmpty equals false

kernel_refl not_named : declaration.namesCanonical raw equals false

-- The name of the row that the declaration names to open a writer.
kernel_refl open_name :
  (declaration.layout.bind fun declared => raw.operations[declared.start]?).map
    (·.identity.name.toString)
  equals some "proof.open"

/-- The row that tests a reader gives `false` on every reader. -/
theorem never_exhausted (reader : model.Value layout.reader) :
    layout.isExhausted model reader = false :=
  kernel_rfl%

/-- The layout of the declaration has no laws in the model of the vocabulary. -/
theorem no_laws (laws : layout.Lawful model) : False := by
  have exhausted := laws.exhausted_empty
  rw [never_exhausted] at exhausted
  cases exhausted

end Sumcheck

namespace Schnorr

open ConstructSchnorr (raw declaration)

typed_literal typed := ConstructSchnorr.typed

kernel_refl typed_eq : elaborate raw equals Except.ok typed

noncomputable abbrev model : Model := Vocabulary.model Vocabulary.table raw

/-- The operations of the package. -/
noncomputable abbrev operations : List OperationSignature := typed.table.map (·.signature)

kernel_refl layout_declared :
  (declaration.layout.bind (Layout.ofRaw (tableScope operations))).isSome equals true

/-- The layout of the declaration, over the rows of the package. -/
noncomputable def layout : Layout operations :=
  (declaration.layout.bind (Layout.ofRaw (tableScope operations))).get layout_declared

kernel_refl not_matched : (Vocabulary.mismatches Vocabulary.table raw).isEmpty equals false

kernel_refl not_named : declaration.namesCanonical raw equals false

-- The name of the row that the declaration names to open a writer.
kernel_refl open_name :
  (declaration.layout.bind fun declared => raw.operations[declared.start]?).map
    (·.identity.name.toString)
  equals some "proof.open"

/-- The row that tests a reader gives `false` on every reader. -/
theorem never_exhausted (reader : model.Value layout.reader) :
    layout.isExhausted model reader = false :=
  kernel_rfl%

/-- The layout of the declaration has no laws in the model of the vocabulary. -/
theorem no_laws (laws : layout.Lawful model) : False := by
  have exhausted := laws.exhausted_empty
  rw [never_exhausted] at exhausted
  cases exhausted

end Schnorr

/-! ## The Schnorr protocol over the rows of the vocabulary

The protocols of `schnorr.json`, as the frontend printed them, over tables that name the
vocabulary's rows: the field `bls12-381.fr`, the group `bls12-381.g1`, the suite
`suite.merlin3.bls12-381.fr64be/0` and the canonical layout over bytes, with the rows in the
order of the fixture. The declaration is the fixture's, with bytes as the writer, the reader
and the proof. The prover sends a point of G1 and an element of the field, so the laws take
the hypothesis of the compressed encoding, and nothing else. -/

namespace SchnorrVocabulary

/-- A row of the vocabulary. -/
abbrev row (name : String) (statics : List Static) (inputs outputs : List Ty)
    (kind : OperationKind := .pure) : Operation :=
  ⟨⟨Name.ofString name, statics⟩, ⟨inputs, outputs, kind⟩⟩

abbrev scalar : Ty := .nominal 0

abbrev point : Ty := .nominal 1

abbrev state : Ty := .nominal 2

abbrev label : Ty := .nominal 3

abbrev bytes : Ty := Vocabulary.bytesType

abbrev types : List CatalogueRow :=
  [⟨Name.ofString "bls12-381.fr", []⟩, ⟨Name.ofString "bls12-381.g1", []⟩,
    ⟨Name.ofString "suite.merlin3.bls12-381.fr64be/0.state", []⟩,
    ⟨Name.ofString "suite.merlin3.bls12-381.fr64be/0.label", []⟩]

abbrev rows : List Operation := [
  row "law.uniform" [.type scalar] [] [scalar] .sampling,
  row "group.scale" [.type point] [point, scalar] [point],
  row "group.add" [.type point] [point, point] [point],
  row "group.equal" [.type point] [point, point] [.bool],
  row "field.mul" [.type scalar] [scalar, scalar] [scalar],
  row "field.add" [.type scalar] [scalar, scalar] [scalar],
  row "suite.merlin3.bls12-381.fr64be/0.start" [] [label] [state],
  row "suite.merlin3.bls12-381.fr64be/0.absorb" [.type scalar] [state, label, scalar] [state],
  row "suite.merlin3.bls12-381.fr64be/0.absorb" [.type point] [state, label, point] [state],
  row "suite.merlin3.bls12-381.fr64be/0.absorb" [.type .bool] [state, label, .bool] [state],
  row "suite.merlin3.bls12-381.fr64be/0.absorb" [.type .nat] [state, label, .nat] [state],
  row "suite.merlin3.bls12-381.fr64be/0.derive" [.type scalar] [state, label] [scalar, state],
  row "layout.canonical.open" [] [] [bytes],
  row "layout.canonical.close" [] [bytes] [bytes],
  row "layout.canonical.read" [] [bytes] [bytes],
  row "layout.canonical.exhausted" [] [bytes] [.bool],
  row "layout.canonical.put" [.type scalar] [bytes, scalar] [bytes],
  row "layout.canonical.put" [.type point] [bytes, point] [bytes],
  row "layout.canonical.put" [.type .bool] [bytes, .bool] [bytes],
  row "layout.canonical.put" [.type .nat] [bytes, .nat] [bytes],
  row "layout.canonical.take" [.type scalar] [bytes] [.bool, scalar, bytes],
  row "layout.canonical.take" [.type point] [bytes] [.bool, point, bytes],
  row "layout.canonical.take" [.type .bool] [bytes] [.bool, .bool, bytes],
  row "layout.canonical.take" [.type .nat] [bytes] [.bool, .nat, bytes]]

/-- The package: the tables of the vocabulary's rows and the protocols of the fixture. -/
noncomputable abbrev raw : Raw.Package :=
  ⟨types, [], [], rows, [], ConstructSchnorr.raw.protocols, ConstructSchnorr.raw.names⟩

/-- The declaration of the fixture, with bytes as the writer, the reader and the proof. -/
noncomputable abbrev declaration : Raw.Declaration :=
  { ConstructSchnorr.declaration with
    layout := some ⟨bytes, bytes, bytes, 12, 13, 14, 15, [16, 17, 18, 19], [20, 21, 22, 23]⟩ }

kernel_refl elaborates : (elaborate raw).isOk equals true

noncomputable def elaborated : Typed := Typed.ofRaw raw elaborates

typed_literal typed := elaborated

kernel_refl typed_eq : elaborate raw equals Except.ok typed

noncomputable abbrev model : Model := Vocabulary.model Vocabulary.table raw

-- The rows of the package are the vocabulary's, the rows that the declaration names have the
-- names of the rows of the canonical layout, and a row that it names is at a type with a
-- point of G1 in it.
kernel_refl matched : Vocabulary.mismatches Vocabulary.table raw equals []

kernel_refl named : declaration.namesCanonical raw equals true

kernel_refl moves_point : declaration.movesPoint Vocabulary.table raw equals true

-- The pipeline of the declaration has a result on the package: its serialize step uses this
-- layout.
kernel_refl constructs : (construct typed declaration).isOk equals true

/-- The operations of the package. -/
noncomputable abbrev operations : List OperationSignature := typed.table.map (·.signature)

kernel_refl layout_declared :
  (declaration.layout.bind (Layout.ofRaw (tableScope operations))).isSome equals true

/-- The layout of the declaration, over the rows of the package. -/
noncomputable def layout : Layout operations :=
  (declaration.layout.bind (Layout.ofRaw (tableScope operations))).get layout_declared

theorem declared :
    declaration.layout.bind (Layout.ofRaw (tableScope (typed.table.map (·.signature)))) =
      some layout :=
  declared_get declaration layout_declared

/-- The layout of the declaration is the canonical one of the package. -/
theorem canonical : layout.Canonical raw :=
  Layout.canonical_of_declaration typed_eq matched declared named

/-- The laws of the layout of the declaration, in the model of the vocabulary. Every other
premise is evaluated by the kernel; the compressed encoding of G1 is a hypothesis, because the
prover sends a point. -/
noncomputable def laws (compression : Vocabulary.PointCompression) : layout.Lawful model :=
  Vocabulary.canonicalLaws typed_eq matched declared named fun _ => compression

/-! ### A round trip at a point of the group and an element of the field -/

kernel_refl point_declared : (layout.put point).isSome equals true

kernel_refl scalar_declared : (layout.put scalar).isSome equals true

/-- The rows that put a point and an element of the field. -/
noncomputable def putPoint : Var operations ⟨[layout.writer, point], [layout.writer], .pure⟩ :=
  (layout.put point).get point_declared

noncomputable def putScalar : Var operations ⟨[layout.writer, scalar], [layout.writer], .pure⟩ :=
  (layout.put scalar).get scalar_declared

theorem point_row : layout.put point = some putPoint := (Option.some_get point_declared).symm

theorem scalar_row : layout.put scalar = some putScalar := (Option.some_get scalar_declared).symm

-- The rows that put and take a point are the rows 17 and 21 of the package, both at the
-- group; those that put and take an element are the rows 16 and 20, both at the field.
kernel_refl message_rows :
  ((layout.put point).map (·.index), (layout.take point).map (·.index),
    (layout.put scalar).map (·.index), (layout.take scalar).map (·.index))
  equals (some 17, some 21, some 16, some 20)

-- The vocabulary admits the package, so the types that the layout moves have formats.
kernel_refl admitted : Vocabulary.missing Vocabulary.table raw equals []

/-- The group and the field have formats: the layout writes their points and elements. -/
theorem message_formats :
    (Vocabulary.messageFormat Vocabulary.table raw point).isSome = true ∧
      (Vocabulary.messageFormat Vocabulary.table raw scalar).isSome = true :=
  ⟨canonical.format_of_admitted admitted (.inl point_declared),
    canonical.format_of_admitted admitted (.inl scalar_declared)⟩

/-- The layout carries the points and the elements of the field. -/
theorem carries_point : layout.Carries point :=
  ⟨kernel_rfl%, Option.isSome_iff_exists.mp point_declared,
    Option.isSome_iff_exists.mp (show (layout.take point).isSome = true from kernel_rfl%)⟩

theorem carries_scalar : layout.Carries scalar :=
  ⟨kernel_rfl%, Option.isSome_iff_exists.mp scalar_declared,
    Option.isSome_iff_exists.mp (show (layout.take scalar).isSome = true from kernel_rfl%)⟩

/-- A point of the group is written. -/
theorem point_written (commitment : Concrete.Point)
    (ofGroup : Vocabulary.inGroup commitment = true) :
    Vocabulary.writes Vocabulary.table raw point (Datum.ofPoint commitment) = true :=
  (Vocabulary.writes_point (name := "bls12-381.g1") kernel_rfl% kernel_rfl% _).trans (by
    rw [Vocabulary.views_point.view_image]
    exact ofGroup)

/-- A number below the order of the field is written. -/
theorem scalar_written (response : Nat) (below : response < Vocabulary.bls12381Order) :
    Vocabulary.writes Vocabulary.table raw scalar (Datum.number response) = true :=
  (Vocabulary.writes_prime (name := "bls12-381.fr") (order := Vocabulary.bls12381Order)
    (width := 32) kernel_rfl% kernel_rfl% _).trans (by simp [Vocabulary.Element.valid, below])

/-- The round trip at a point of the group and an element of the field, the messages of the
prover: they are taken, in order, from the reader of the closed writer, which is then
exhausted. -/
theorem round_trip (compression : Vocabulary.PointCompression) (commitment : Concrete.Point)
    (ofGroup : Vocabulary.inGroup commitment = true) (response : Nat)
    (below : response < Vocabulary.bls12381Order) :
    ∃ reader,
      layout.Takes model
        (layout.reading model (layout.closed model
          (layout.putValue model putScalar
            (layout.putValue model putPoint (layout.opened model) (Datum.ofPoint commitment))
            (Datum.number response))))
        [⟨point, Datum.ofPoint commitment⟩, ⟨scalar, Datum.number response⟩] reader ∧
      layout.isExhausted model reader = true :=
  (laws compression).round_trip
    (fun message member => by
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨carries_point, point_written commitment ofGroup⟩
      · rw [List.mem_singleton.mp later]
        exact ⟨carries_scalar, scalar_written response below⟩)
    (.cons putPoint point_row (.cons putScalar scalar_row (.nil _)))

/-! ### The values that the protocol sends

The prover sends the commitment, the result of the row 1, `group.scale`, and the response,
the result of the row 5, `field.add`. The layout writes the response whatever the row was
given. It writes the commitment exactly when the multiple is a point of the group: that a
multiple of a point of the group is one is not proved in this package. -/

/-- The layout writes the response that the row `field.add` of the package returns. -/
theorem response_written (arguments : Values Concrete.Value [scalar, scalar]) :
    Vocabulary.writes Vocabulary.table raw scalar
      ((model.pure ⟨5, [scalar, scalar], [scalar]⟩ rfl arguments).get .here) = true :=
  Vocabulary.model_arithmetic_writes
    (operation := row "field.add" [.type scalar] [scalar, scalar] [scalar])
    (name := "field.add") (field := "bls12-381.fr") (order := Vocabulary.bls12381Order)
    (width := 32) kernel_rfl% kernel_rfl% (by decide) kernel_rfl% kernel_rfl% kernel_rfl%
    (by decide) rfl arguments

/-- The layout writes the commitment that the row `group.scale` of the package returns exactly
when the multiple of the base by the nonce is a point of the group. -/
theorem commitment_written (arguments : Values Concrete.Value [point, scalar]) :
    Vocabulary.writes Vocabulary.table raw point
        ((model.pure ⟨1, [point, scalar], [point]⟩ rfl arguments).get .here) =
      Vocabulary.inGroup (Concrete.scalePoint (Concrete.toDatum point (arguments.get .here)).toPoint
        ((Concrete.toDatum scalar (arguments.tail.get .here)).toNat % Concrete.scalarModulus)) :=
  Vocabulary.model_scale_writes
    (operation := row "group.scale" [.type point] [point, scalar] [point])
    (group := "bls12-381.g1") kernel_rfl% kernel_rfl% kernel_rfl% kernel_rfl% kernel_rfl% rfl
    arguments

-- The point at infinity is of the group, so the statement has an instance.
kernel_refl infinity_of_group : Vocabulary.inGroup none equals true

/-- The round trip at the point at infinity and the element 5. -/
theorem round_trip_infinity (compression : Vocabulary.PointCompression) :
    ∃ reader,
      layout.Takes model
        (layout.reading model (layout.closed model
          (layout.putValue model putScalar
            (layout.putValue model putPoint (layout.opened model) (Datum.ofPoint none))
            (Datum.number 5))))
        [⟨point, Datum.ofPoint none⟩, ⟨scalar, Datum.number 5⟩] reader ∧
      layout.isExhausted model reader = true :=
  round_trip compression none infinity_of_group 5 (by decide)

end SchnorrVocabulary

/-! ## A layout whose row that takes a point is at the field

A package of the field and the group with the rows of the canonical layout by name, in which
the row that takes a value of the group has the field as its static argument: its name is the
vocabulary's and its signature is not. The core elaborates the package and the rows that the
declared layout names have the names of the rows of the canonical layout, but the rows of the
package are not the vocabulary's, and the layout is not the canonical one: the row that puts a
point is at the group and the row that takes one at the field. Under no laws is the point at
infinity writable: the reader of its 48 bytes gives the number of the first 32. -/

namespace Mismatched

open SchnorrVocabulary (row scalar point bytes)

abbrev raw : Raw.Package :=
  ⟨[⟨Name.ofString "bls12-381.fr", []⟩, ⟨Name.ofString "bls12-381.g1", []⟩], [], [],
    [row "layout.canonical.open" [] [] [bytes],
      row "layout.canonical.close" [] [bytes] [bytes],
      row "layout.canonical.read" [] [bytes] [bytes],
      row "layout.canonical.exhausted" [] [bytes] [.bool],
      row "layout.canonical.put" [.type scalar] [bytes, scalar] [bytes],
      row "layout.canonical.put" [.type point] [bytes, point] [bytes],
      row "layout.canonical.take" [.type scalar] [bytes] [.bool, point, bytes]],
    [], [], none⟩

/-- The declared layout: the rows by their numbers. -/
abbrev declared : Raw.Layout := ⟨bytes, bytes, bytes, 0, 1, 2, 3, [4, 5], [6]⟩

kernel_refl elaborates : (elaborate raw).isOk equals true

noncomputable def elaborated : Typed := Typed.ofRaw raw elaborates

typed_literal typed := elaborated

kernel_refl typed_eq : elaborate raw equals Except.ok typed

noncomputable abbrev operations : List OperationSignature := typed.table.map (·.signature)

noncomputable abbrev model : Model := Vocabulary.model Vocabulary.table raw

-- The rows that the declared layout names have the names of the rows of the canonical layout,
-- and one row of the package is not the vocabulary's.
kernel_refl named : declared.namesCanonical raw equals true

kernel_refl not_matched : (Vocabulary.mismatches Vocabulary.table raw).length equals 1

kernel_refl layout_declared : (Layout.ofRaw (tableScope operations) declared).isSome equals true

/-- The layout that the declared layout describes, over the rows of the package. -/
noncomputable def layout : Layout operations :=
  (Layout.ofRaw (tableScope operations) declared).get layout_declared

kernel_refl put_declared : (layout.put point).isSome equals true

kernel_refl take_declared : (layout.take point).isSome equals true

/-- The rows that put and take a point. -/
noncomputable def put : Var operations ⟨[layout.writer, point], [layout.writer], .pure⟩ :=
  (layout.put point).get put_declared

noncomputable def take :
    Var operations ⟨[layout.reader], [.bool, point, layout.reader], .pure⟩ :=
  (layout.take point).get take_declared

theorem put_row : layout.put point = some put := (Option.some_get put_declared).symm

theorem take_row : layout.take point = some take := (Option.some_get take_declared).symm

-- The row that takes a point is the row 6 of the package, whose static argument is the field,
-- and the type of points stands for the group.
kernel_refl take_index : take.index equals 6

kernel_refl take_static :
  (raw.operations[6]?.bind fun operation =>
    Vocabulary.argumentsOf raw.types.toArray operation.identity)
  equals some [.type (.row "bls12-381.fr")]

kernel_refl point_closed :
  Vocabulary.closedOf raw.types.toArray point equals some (.row "bls12-381.g1")

/-- The layout is not the canonical one of the package. -/
theorem not_canonical : ¬layout.Canonical raw := by
  intro canonical
  obtain ⟨closed, closedIs, operation, found, _, read⟩ := canonical.take take_row
  rw [take_index] at found
  have static := take_static
  rw [found, Option.bind_some, read] at static
  rw [point_closed] at closedIs
  cases closedIs
  simp at static

/-- The point at infinity. -/
abbrev infinity : Datum := Datum.ofPoint none

/-- The reader of what the layout wrote for the point at infinity. -/
noncomputable abbrev written : model.Value layout.reader :=
  layout.reading model
    (layout.closed model (layout.putValue model put (layout.opened model) infinity))

theorem populated : Ty.allPopulated [.bool, point, layout.reader] = true := kernel_rfl%

-- The row that takes a point, on that reader, gives the number 192: the 32 bytes that it
-- reads as an element of the field start with the byte of the flags of the point.
kernel_refl taken :
  ((model.pure (.of take) populated (.cons written .nil)).tail.get .here : Datum)
  equals Datum.number 192

/-- Under no laws of the layout is the point at infinity writable: the reader gives another
value than the writer was given. -/
theorem infinity_not_writable (laws : layout.Lawful model) : ¬laws.Writable point infinity := by
  intro writable
  have put := laws.put_appends put put_row infinity writable (layout.opened model)
  rw [laws.start_empty, laws.empty_append] at put
  have takes := laws.take_reads take populated take_row infinity writable laws.empty
  rw [laws.append_empty, ← put, ← laws.close_read] at takes
  have same : Datum.number 192 = infinity :=
    taken.symm.trans (congrArg (fun values => values.tail.get .here) takes)
  cases same

end Mismatched

end CanonicalLayoutLaws

/-! ## Axioms -/

#print axioms CanonicalLayoutLaws.Collecting.canonical
#print axioms CanonicalLayoutLaws.Collecting.laws
#print axioms CanonicalLayoutLaws.Collecting.field_format
#print axioms CanonicalLayoutLaws.Collecting.sendable
#print axioms CanonicalLayoutLaws.Collecting.written
#print axioms CanonicalLayoutLaws.Collecting.round_trip
#print axioms CanonicalLayoutLaws.Collecting.written_bytes
#print axioms CanonicalLayoutLaws.Collecting.sum_written
#print axioms CanonicalLayoutLaws.Collecting.product_written
#print axioms CanonicalLayoutLaws.Sumcheck.never_exhausted
#print axioms CanonicalLayoutLaws.Sumcheck.no_laws
#print axioms CanonicalLayoutLaws.Schnorr.never_exhausted
#print axioms CanonicalLayoutLaws.Schnorr.no_laws
#print axioms CanonicalLayoutLaws.SchnorrVocabulary.canonical
#print axioms CanonicalLayoutLaws.SchnorrVocabulary.laws
#print axioms CanonicalLayoutLaws.SchnorrVocabulary.message_formats
#print axioms CanonicalLayoutLaws.SchnorrVocabulary.point_written
#print axioms CanonicalLayoutLaws.SchnorrVocabulary.scalar_written
#print axioms CanonicalLayoutLaws.SchnorrVocabulary.round_trip
#print axioms CanonicalLayoutLaws.SchnorrVocabulary.round_trip_infinity
#print axioms CanonicalLayoutLaws.SchnorrVocabulary.response_written
#print axioms CanonicalLayoutLaws.SchnorrVocabulary.commitment_written
#print axioms CanonicalLayoutLaws.Mismatched.not_canonical
#print axioms CanonicalLayoutLaws.Mismatched.infinity_not_writable

#print axioms rowWith_index
#print axioms firstRowWith_mem
#print axioms Layout.ofRaw_declaredBy
#print axioms Vocabulary.Closed.eq_of_beq
#print axioms Vocabulary.Closed.eq_of_beqList
#print axioms Vocabulary.bytes_of_closed
#print axioms Vocabulary.fill_of_closedOf
#print axioms Vocabulary.sameTypes_nil
#print axioms Vocabulary.sameTypes_cons
#print axioms Vocabulary.sameTypes_filled
#print axioms Vocabulary.signature_open
#print axioms Vocabulary.signature_close
#print axioms Vocabulary.signature_read
#print axioms Vocabulary.signature_exhausted
#print axioms Vocabulary.signature_put
#print axioms Vocabulary.signature_take
#print axioms Vocabulary.typed_row_matched
#print axioms Vocabulary.rowNamed_some
#print axioms Layout.canonical_of_declared
#print axioms Vocabulary.writes_format
#print axioms Vocabulary.writes_iff
#print axioms Vocabulary.bytesOfValue_valueOfBytes
#print axioms Vocabulary.valueOfBytes_bytesOfValue
#print axioms Vocabulary.opened_bytes
#print axioms Vocabulary.put_bytes
#print axioms Vocabulary.close_read_bytes
#print axioms Vocabulary.take_bytes
#print axioms Vocabulary.exhausted_bytes
#print axioms Layout.Canonical.laws
#print axioms Layout.Canonical.format_of_admitted
#print axioms Layout.Canonical.declared_movesPoint
#print axioms Layout.declared_of_declaration
#print axioms Layout.canonical_of_declaration
#print axioms Layout.movesPoint_of_declaration
#print axioms Vocabulary.canonicalLaws
#print axioms Vocabulary.canonicalLawsWithoutPoint
#print axioms Vocabulary.laws_writable
#print axioms Vocabulary.laws_encode

#print axioms Vocabulary.closedOf_bool
#print axioms Vocabulary.closedOf_nat
#print axioms Vocabulary.closedOf_fin
#print axioms Vocabulary.writes_bool
#print axioms Vocabulary.writes_nat
#print axioms Vocabulary.writes_index
#print axioms Vocabulary.leafOf_prime
#print axioms Vocabulary.prime_valid_iff
#print axioms Vocabulary.writes_prime
#print axioms Vocabulary.writes_prime_order
#print axioms Vocabulary.writes_point
#print axioms Vocabulary.powerModulo_lt
#print axioms Vocabulary.apply_arithmetic_valid
#print axioms Vocabulary.model_arithmetic_valid
#print axioms Vocabulary.model_arithmetic_writes
#print axioms Vocabulary.literal_writes
#print axioms Vocabulary.leafOf_curve
#print axioms Vocabulary.apply_scale_point
#print axioms Vocabulary.model_scale_point
#print axioms Vocabulary.model_scale_writes
