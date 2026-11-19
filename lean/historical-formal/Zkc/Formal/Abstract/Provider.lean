module

public import Zkc.Core.Meaning
public import Zkc.Formal.Algebra
public import Zkc.Formal.Abstract.Binding

@[expose] public section

/-! The model of a package's rows in an arithmetic.

`provider A binding` is a model in the core's sense: the carrier of a nominal type is the
scalars or the points of the arithmetic `A`, as the binding says, and a row is the operation of
the arithmetic that the binding names, read at the row's typed signature: an operation of the
field on scalars, of the group on points, and of a sized collection of scalars element by
element. A row that the binding does not name, or whose signature is not the operation's,
gives the inhabitants of its outputs; nothing is proved about such a row.

A statement about a protocol in this model is a statement of mathematics: it holds for every
arithmetic. The model that runs is related to it (`Zkc.Formal.Bls12381`).
-/

set_option autoImplicit false

namespace Zkc.Formal

open Zkc.Source Zkc.Core

namespace Kind

variable (A : Arithmetic)

/-- The values of a nominal type of a kind. -/
def Carrier : Kind → Type
  | .scalar => A.Scalar
  | .point => A.Point
  | .other => PUnit

def inhabitant : (kind : Kind) → kind.Carrier A
  | .scalar => (0 : A.Scalar)
  | .point => A.identity
  | .other => PUnit.unit

/-- A value as a scalar: itself at the scalars. -/
def asScalar : (kind : Kind) → kind.Carrier A → A.Scalar
  | .scalar, value => value
  | .point, _ => 0
  | .other, _ => 0

/-- A scalar as a value: itself at the scalars. -/
def ofScalar : (kind : Kind) → A.Scalar → kind.Carrier A
  | .scalar, value => value
  | .point, _ => A.identity
  | .other, _ => PUnit.unit

/-- A value as a point: itself at the points. -/
def asPoint : (kind : Kind) → kind.Carrier A → A.Point
  | .point, value => value
  | .scalar, _ => A.identity
  | .other, _ => A.identity

/-- A point as a value: itself at the points. -/
def ofPoint : (kind : Kind) → A.Point → kind.Carrier A
  | .point, value => value
  | .scalar, _ => (0 : A.Scalar)
  | .other, _ => PUnit.unit

/-- Values as scalars: themselves at the scalars. -/
def asScalars : (kind : Kind) → List (kind.Carrier A) → List A.Scalar
  | .scalar, values => values
  | .point, values => values.map fun _ => 0
  | .other, values => values.map fun _ => 0

/-- Scalars as values: themselves at the scalars. -/
def ofScalars : (kind : Kind) → List A.Scalar → List (kind.Carrier A)
  | .scalar, values => values
  | .point, values => values.map fun _ => A.identity
  | .other, values => values.map fun _ => PUnit.unit

theorem length_asScalars (kind : Kind) (values : List (kind.Carrier A)) :
    (kind.asScalars A values).length = values.length := by
  cases kind <;> first | rfl | exact List.length_map _

theorem length_ofScalars (kind : Kind) (values : List A.Scalar) :
    (kind.ofScalars A values).length = values.length := by
  cases kind <;> first | rfl | exact List.length_map _

end Kind

/-- A list at a size: itself when it has the size. -/
def sized {X : Type} (fallback : X) (size : Nat) (values : List X) :
    { items : List X // items.length = size } :=
  if same : values.length = size then ⟨values, same⟩
  else ⟨List.replicate size fallback, List.length_replicate⟩

theorem sized_val {X : Type} (fallback : X) {size : Nat} {values : List X}
    (same : values.length = size) : (sized fallback size values).val = values := by
  simp [sized, same]

section Provider

variable (A : Arithmetic) (binding : Binding)

/-- The values of a nominal type of a package. -/
abbrev Carrier (type : Nat) : Type := (binding.kind type).Carrier A

/-- The inhabitants of outputs that no operation gives. -/
def inhabitants (outputs : List Ty) (populated : Ty.allPopulated outputs = true) :
    Values (Ty.Value (Carrier A binding)) outputs :=
  Ty.inhabitants (fun type => (binding.kind type).inhabitant A) outputs populated

/-- An operation of two scalars that gives a scalar. -/
def scalarBinary (compute : A.Scalar → A.Scalar → A.Scalar) :
    (inputs outputs : List Ty) → Ty.allPopulated outputs = true →
      Values (Ty.Value (Carrier A binding)) inputs → Values (Ty.Value (Carrier A binding)) outputs
  | [.nominal first, .nominal second], [.nominal output], _ => fun arguments =>
      .cons (ty := Ty.nominal output)
        ((binding.kind output).ofScalar A
          (compute ((binding.kind first).asScalar A (arguments.get .here))
            ((binding.kind second).asScalar A (arguments.tail.get .here)))) .nil
  | _, outputs, populated => fun _ => inhabitants A binding outputs populated

/-- Equality of two scalars. -/
def scalarEqual :
    (inputs outputs : List Ty) → Ty.allPopulated outputs = true →
      Values (Ty.Value (Carrier A binding)) inputs → Values (Ty.Value (Carrier A binding)) outputs
  | [.nominal first, .nominal second], [.bool], _ => fun arguments =>
      .cons (ty := Ty.bool)
        (decide ((binding.kind first).asScalar A (arguments.get .here) =
          (binding.kind second).asScalar A (arguments.tail.get .here))) .nil
  | _, outputs, populated => fun _ => inhabitants A binding outputs populated

/-- The sum of two points. -/
def pointBinary :
    (inputs outputs : List Ty) → Ty.allPopulated outputs = true →
      Values (Ty.Value (Carrier A binding)) inputs → Values (Ty.Value (Carrier A binding)) outputs
  | [.nominal first, .nominal second], [.nominal output], _ => fun arguments =>
      .cons (ty := Ty.nominal output)
        ((binding.kind output).ofPoint A
          (A.combine ((binding.kind first).asPoint A (arguments.get .here))
            ((binding.kind second).asPoint A (arguments.tail.get .here)))) .nil
  | _, outputs, populated => fun _ => inhabitants A binding outputs populated

/-- The multiple of a point by a scalar. -/
def pointScale :
    (inputs outputs : List Ty) → Ty.allPopulated outputs = true →
      Values (Ty.Value (Carrier A binding)) inputs → Values (Ty.Value (Carrier A binding)) outputs
  | [.nominal base, .nominal multiplier], [.nominal output], _ => fun arguments =>
      .cons (ty := Ty.nominal output)
        ((binding.kind output).ofPoint A
          (A.scale ((binding.kind base).asPoint A (arguments.get .here))
            ((binding.kind multiplier).asScalar A (arguments.tail.get .here)))) .nil
  | _, outputs, populated => fun _ => inhabitants A binding outputs populated

/-- Equality of two points. -/
def pointEqual :
    (inputs outputs : List Ty) → Ty.allPopulated outputs = true →
      Values (Ty.Value (Carrier A binding)) inputs → Values (Ty.Value (Carrier A binding)) outputs
  | [.nominal first, .nominal second], [.bool], _ => fun arguments =>
      .cons (ty := Ty.bool)
        (A.same ((binding.kind first).asPoint A (arguments.get .here))
          ((binding.kind second).asPoint A (arguments.tail.get .here))) .nil
  | _, outputs, populated => fun _ => inhabitants A binding outputs populated

/-- The sum of a sized collection of scalars. -/
def sequenceSum :
    (inputs outputs : List Ty) → Ty.allPopulated outputs = true →
      Values (Ty.Value (Carrier A binding)) inputs → Values (Ty.Value (Carrier A binding)) outputs
  | [.seq (.nominal entry) (some _)], [.nominal output], _ => fun arguments =>
      .cons (ty := Ty.nominal output)
        ((binding.kind output).ofScalar A
          (A.sum ((binding.kind entry).asScalars A (arguments.get .here).val))) .nil
  | _, outputs, populated => fun _ => inhabitants A binding outputs populated

/-- An operation of two sized collections of scalars, element by element. -/
def sequenceBinary (compute : A.Scalar → A.Scalar → A.Scalar) :
    (inputs outputs : List Ty) → Ty.allPopulated outputs = true →
      Values (Ty.Value (Carrier A binding)) inputs → Values (Ty.Value (Carrier A binding)) outputs
  | [.seq (.nominal left) (some _), .seq (.nominal right) (some _)],
      [.seq (.nominal output) (some size)], _ => fun arguments =>
      .cons (ty := Ty.seq (.nominal output) (some size))
        (sized ((binding.kind output).inhabitant A) size
          ((binding.kind output).ofScalars A
            (List.zipWith compute ((binding.kind left).asScalars A (arguments.get .here).val)
              ((binding.kind right).asScalars A (arguments.tail.get .here).val)))) .nil
  | _, outputs, populated => fun _ => inhabitants A binding outputs populated

/-- A sized collection of scalars, each times a scalar. -/
def sequenceScale :
    (inputs outputs : List Ty) → Ty.allPopulated outputs = true →
      Values (Ty.Value (Carrier A binding)) inputs → Values (Ty.Value (Carrier A binding)) outputs
  | [.seq (.nominal entry) (some _), .nominal multiplier],
      [.seq (.nominal output) (some size)], _ => fun arguments =>
      .cons (ty := Ty.seq (.nominal output) (some size))
        (sized ((binding.kind output).inhabitant A) size
          ((binding.kind output).ofScalars A
            (((binding.kind entry).asScalars A (arguments.get .here).val).map fun value =>
              value * (binding.kind multiplier).asScalar A (arguments.tail.get .here)))) .nil
  | _, outputs, populated => fun _ => inhabitants A binding outputs populated

/-- The model of a package's rows in an arithmetic. -/
def provider : Model where
  Carrier := Carrier A binding
  pure row populated :=
    match binding.row row.row with
    | .fieldAdd => scalarBinary A binding (· + ·) row.inputs row.outputs populated
    | .fieldSub => scalarBinary A binding (· - ·) row.inputs row.outputs populated
    | .fieldMul => scalarBinary A binding (· * ·) row.inputs row.outputs populated
    | .fieldEqual => scalarEqual A binding row.inputs row.outputs populated
    | .groupAdd => pointBinary A binding row.inputs row.outputs populated
    | .groupScale => pointScale A binding row.inputs row.outputs populated
    | .groupEqual => pointEqual A binding row.inputs row.outputs populated
    | .seqSum => sequenceSum A binding row.inputs row.outputs populated
    | .seqAdd => sequenceBinary A binding (· + ·) row.inputs row.outputs populated
    | .seqSub => sequenceBinary A binding (· - ·) row.inputs row.outputs populated
    | .seqScale => sequenceScale A binding row.inputs row.outputs populated
    | .other => fun _ => inhabitants A binding row.outputs populated
  restricted _ _ := none
  «opaque» _ _ := .error .abort
  literal row data := (binding.kind row).ofScalar A (OfNat.ofNat (data.headD 0))

/-! The rows of the model, at what the binding says of them. -/

section Rows

variable {A binding} {index : Nat} (inputs outputs : List Ty)
  (populated : Ty.allPopulated outputs = true)

theorem provider_fieldAdd (bound : binding.row index = .fieldAdd) :
    (provider A binding).pure ⟨index, inputs, outputs⟩ populated =
      scalarBinary A binding (· + ·) inputs outputs populated := by
  simp only [provider, bound]

theorem provider_fieldSub (bound : binding.row index = .fieldSub) :
    (provider A binding).pure ⟨index, inputs, outputs⟩ populated =
      scalarBinary A binding (· - ·) inputs outputs populated := by
  simp only [provider, bound]

theorem provider_fieldMul (bound : binding.row index = .fieldMul) :
    (provider A binding).pure ⟨index, inputs, outputs⟩ populated =
      scalarBinary A binding (· * ·) inputs outputs populated := by
  simp only [provider, bound]

theorem provider_fieldEqual (bound : binding.row index = .fieldEqual) :
    (provider A binding).pure ⟨index, inputs, outputs⟩ populated =
      scalarEqual A binding inputs outputs populated := by
  simp only [provider, bound]

theorem provider_groupAdd (bound : binding.row index = .groupAdd) :
    (provider A binding).pure ⟨index, inputs, outputs⟩ populated =
      pointBinary A binding inputs outputs populated := by
  simp only [provider, bound]

theorem provider_groupScale (bound : binding.row index = .groupScale) :
    (provider A binding).pure ⟨index, inputs, outputs⟩ populated =
      pointScale A binding inputs outputs populated := by
  simp only [provider, bound]

theorem provider_groupEqual (bound : binding.row index = .groupEqual) :
    (provider A binding).pure ⟨index, inputs, outputs⟩ populated =
      pointEqual A binding inputs outputs populated := by
  simp only [provider, bound]

theorem provider_seqSum (bound : binding.row index = .seqSum) :
    (provider A binding).pure ⟨index, inputs, outputs⟩ populated =
      sequenceSum A binding inputs outputs populated := by
  simp only [provider, bound]

theorem provider_seqAdd (bound : binding.row index = .seqAdd) :
    (provider A binding).pure ⟨index, inputs, outputs⟩ populated =
      sequenceBinary A binding (· + ·) inputs outputs populated := by
  simp only [provider, bound]

theorem provider_seqSub (bound : binding.row index = .seqSub) :
    (provider A binding).pure ⟨index, inputs, outputs⟩ populated =
      sequenceBinary A binding (· - ·) inputs outputs populated := by
  simp only [provider, bound]

theorem provider_seqScale (bound : binding.row index = .seqScale) :
    (provider A binding).pure ⟨index, inputs, outputs⟩ populated =
      sequenceScale A binding inputs outputs populated := by
  simp only [provider, bound]

end Rows

end Provider

end Zkc.Formal
