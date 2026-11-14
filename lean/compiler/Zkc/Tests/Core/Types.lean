import Zkc.Tests.Core.Check
import Zkc.Core.RoundTrip
import Zkc.Core.Laws

/-! Kernel checks for the types, the rows and the literals of the core.

- `fixtures/types.json` has a protocol with inputs of the types `fin 0`, `seq (fin 0) (some 0)`,
  a sized and an unsized sequence, a declared variant without alternative and one with two; a
  function
  that applies a restricted row and returns a `fin` literal and a `bytes` literal; and a function
  that returns a value of the empty variant from a restricted row. The package elaborates, its
  typed package unelaborates to it, and its printed JSON reads back to it.
- Elaboration refuses a table whose pure row returns `fin 0`, a `fin` literal not below its
  bound, a byte not below 256, and a `stop` with the reserved reason `undefined`.
- A restricted row in a function: for an arbitrary model, the function's meaning is the model's
  value where the model defines the row, and the stop `undefined` where it does not.
- A model exists: the one-point model.
-/

set_option autoImplicit false

open Zkc.Source Zkc.Core

namespace Types

/-! ## The JSON package -/

raw_package raw from file "fixtures/types.json"

kernel_refl tables : tablesViolation raw.types raw.records raw.variants raw.operations equals none
kernel_refl accepted : (elaborateWritten raw).isOk equals true
kernel_refl elaborates : (elaborate raw).isOk equals true

noncomputable def elaborated : Typed := Typed.ofRaw raw elaborates

kernel_refl elaborated_unelaborate : unelaborate elaborated equals raw

/-- The equation of elaboration, from the round-trip theorem. -/
theorem elaborate_eq : elaborate raw = .ok elaborated :=
  elaborated_unelaborate ▸ elaborate_unelaborate elaborated

reprinted_package reprinted from file "fixtures/types.json"

kernel_refl reprinted_eq : reprinted equals raw

/-! ## Refusals -/

/-- The catalogue name `test.none`. -/
abbrev testName : Name := [116, 101, 115, 116, 46, 110, 111, 110, 101]

/-- A pure row that returns a value of `fin 0`: no total function does. -/
abbrev unpopulatedRow : Operation := ⟨⟨testName, []⟩, ⟨[], [.fin 0], .pure⟩⟩

kernel_refl unpopulated_table :
    tablesViolation [] [] [] [unpopulatedRow] equals some .unpopulatedOutput
kernel_refl unpopulated_refused :
    elaborate ⟨[], [], [], [unpopulatedRow], [], [], none⟩ equals
      .error ⟨.residual .unpopulatedOutput, none, []⟩

-- The same row restricted: the table is accepted.
kernel_refl restricted_table :
    tablesViolation [] [] [] [⟨⟨testName, []⟩, ⟨[], [.fin 0], .restricted none⟩⟩] equals none

/-- A function that returns a literal. -/
abbrev literalPackage (type : Ty) (literal : Raw.Literal) : Raw.Package :=
  ⟨[], [], [], [], [⟨false, [], [type], some (.step (.literal literal) (.ret [0]))⟩], [], none⟩

kernel_refl fin_in_range : (elaborate (literalPackage (.fin 3) (.fin 3 2))).isOk equals true
kernel_refl fin_out_of_range :
    (elaborate (literalPackage (.fin 3) (.fin 3 3))).isOk equals false
kernel_refl fin_out_of_range_refusal :
    (match elaborate (literalPackage (.fin 3) (.fin 3 3)) with
      | .error refusal => some refusal
      | .ok _ => none) equals some ⟨.literal, some (.function 0), [0]⟩
kernel_refl bytes_in_range :
    (elaborate (literalPackage (.seq (.fin 256) (some 2)) (.bytes [0, 255]))).isOk equals true
kernel_refl bytes_out_of_range :
    (match elaborate (literalPackage (.seq (.fin 256) (some 2)) (.bytes [0, 256])) with
      | .error refusal => some refusal
      | .ok _ => none) equals some ⟨.literal, some (.function 0), [0]⟩

-- A function that stops with the reserved reason `undefined`.
kernel_refl undefined_stop_refused :
    (match elaborate ⟨[], [], [], [], [⟨false, [], [.nat], some (.stop .undefined)⟩], [], none⟩ with
      | .error refusal => some refusal
      | .ok _ => none) equals some ⟨.residual .reservedReason, some (.function 0), []⟩

#print axioms elaborate_eq
#print axioms reprinted_eq
#print axioms unpopulated_refused

end Types

/-! ## A restricted row in a function -/

namespace RestrictedRow

/-- One restricted row, from the count type to `fin 4`. -/
abbrev table : List OperationSignature := [⟨[.nat], [.fin 4], .restricted none⟩]

abbrev header : FunctionHeader := ⟨[.nat], [.fin 4], false⟩

/-- The row. -/
abbrev row : Var table ⟨[.nat], [.fin 4], .restricted none⟩ := ⟨0, rfl⟩

/-- A function that applies the row to its input and returns the result. -/
def decode : FunctionDefinition table [] header :=
  ⟨.letOp (.op row rfl) (.cons ⟨0, rfl⟩ .nil) .nil (.ret (.cons ⟨0, rfl⟩ .nil))⟩

/-- The row as a model reads it. -/
abbrev key : OperationRow := ⟨0, [.nat], [.fin 4]⟩

/-- Where the model defines the row, the function returns the model's value. -/
theorem decode_defined (model : Model) (count : Nat) (value : Fin 4)
    (defined : model.restricted key (.cons count .nil) = some (.cons value .nil)) :
    decode.meaning model .nil (.cons count .nil) = .done (.cons value .nil) := by
  show (definedProcess model (model.restricted key (.cons count .nil))).bind _ = _
  rw [defined]
  rfl

/-- Where the model does not define the row, the function stops `undefined`. -/
theorem decode_undefined (model : Model) (count : Nat)
    (undefined : model.restricted key (.cons count .nil) = none) :
    decode.meaning model .nil (.cons count .nil) = .halt .undefined := by
  show (definedProcess model (model.restricted key (.cons count .nil))).bind _ = _
  rw [undefined]
  rfl

/-- The row's process, for any arguments: `undefined` exactly where the model gives
nothing. -/
theorem rowProcess_restricted (model : Model) (operation : OperationRow)
    (applies : OperationSignature.applies ⟨operation.inputs, operation.outputs, .restricted none⟩ = true)
    (arguments : Values model.Value operation.inputs) :
    rowProcess model operation (.restricted none) applies arguments =
      match model.restricted operation arguments with
      | some values => .done values
      | none => .halt .undefined := by
  show definedProcess model (model.restricted operation arguments) = _
  cases model.restricted operation arguments <;> rfl

/-- Models exist: the one-point model, in which this row is undefined everywhere. -/
def unitModel : Model := Model.unit

theorem unit_undefined (count : Nat) :
    decode.meaning Model.unit .nil (.cons count .nil) = .halt .undefined :=
  decode_undefined Model.unit count rfl

#print axioms decode_defined
#print axioms decode_undefined
#print axioms rowProcess_restricted

end RestrictedRow
