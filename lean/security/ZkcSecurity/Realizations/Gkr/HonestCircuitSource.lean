module

public import ZkcSecurity.Realizations.Gkr.HonestCircuitValues
public import ZkcSecurity.Realizations.Gkr.HonestHelpersSource

@[expose] public section

/-! Transport the circuit-value laws to the source participant's actual helper
table. The associations and ordered collection callbacks are checked against
the current imported unit, including their complete typed bodies. -/

namespace ZkcSecurity.Realizations.Gkr.HonestCircuit
open Zkc Source Structured
open ZkcExamples.Structured GkrSourceLaws SumcheckVerifierHelpers
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open ZkcSecurity.Examples.Components

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- The actual participant helper33 computes the independent circuit layer. -/
theorem layer_plain {width : Nat} (add mul below : List F)
    (a m : Zkc.Protocols.Gkr.Wiring F width) (v : Table F width)
    (da : ofList? (width + width + width) add = some a)
    (dm : ofList? (width + width + width) mul = some m)
    (dv : ofList? width below = some v) (small : width + width + width < 64) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
      GkrSourceBodies.helper33Helper (.cons add (.cons mul (.cons below (.cons width .nil)))) =
      .done (.cons (GkrRoundsLayout.encode (Zkc.Protocols.Gkr.layer a m v)) .nil) := by
  rw [closed_invoke_plain]
  change (invoke (helpers (G := G)) GkrSourceBodies.helper33Helper _).interpret _ = _
  rw [layer_encodes add mul below a m v da dm dv small]
  rfl

/-- The source ABI is `(add, mul, inputs, layers, selector, width, layer)`.
The output is the entire wire vector, with no challenge or transcript effects. -/
theorem values_below_plain {width : Nat} (add mul inputs : List F) (layers selector layerIndex : Nat)
    (circuit : Families.Gkr.Circuit F width)
    (da : StackedEncoding add layers selector circuit.add)
    (dm : StackedEncoding mul layers selector circuit.mul)
    (di : ofList? width inputs = some circuit.inputs)
    (capacity : layers ≤ 2 ^ selector)
    (small : width + width + width + selector < 64)
    (layersBound : layers < indexLimit) (inside : layerIndex < layers) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
      GkrSourceBodies.helper34Helper
      (.cons add (.cons mul (.cons inputs (.cons layers
        (.cons selector (.cons width (.cons layerIndex .nil))))))) =
      .done (.cons (GkrRoundsLayout.encode
        (circuit.wires (layers - layerIndex - 1) (layerIndex + 1))) .nil) := by
  rw [closed_invoke_plain]
  change (invoke (helpers (G := G)) GkrSourceBodies.helper34Helper _).interpret _ = _
  rw [values_below add mul inputs layers selector layerIndex circuit da dm di capacity small layersBound inside]
  rfl

/-- Pure helper execution preserves every handler state, including all unread
input and transcript suffixes, and emits no events. -/
theorem values_below_run {width : Nat} {H E : Type} (add mul inputs : List F)
    (layers selector layerIndex : Nat) (circuit : Families.Gkr.Circuit F width)
    (da : StackedEncoding add layers selector circuit.add)
    (dm : StackedEncoding mul layers selector circuit.mul)
    (di : ofList? width inputs = some circuit.inputs)
    (capacity : layers ≤ 2 ^ selector)
    (small : width + width + width + selector < 64)
    (layersBound : layers < indexLimit) (inside : layerIndex < layers)
    (handler : PIR.Handler (participantInterface F G) H E) (initial : H) :
    (invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
      GkrSourceBodies.helper34Helper
      (.cons add (.cons mul (.cons inputs (.cons layers
        (.cons selector (.cons width (.cons layerIndex .nil)))))))).run handler initial =
      ⟨.returned (.cons (GkrRoundsLayout.encode
        (circuit.wires (layers - layerIndex - 1) (layerIndex + 1))) .nil), initial, []⟩ := by
  rw [values_below_plain add mul inputs layers selector layerIndex circuit da dm di capacity small layersBound inside]
  rfl

/-- The source component ABI retains `some` on the entire computed layer. -/
theorem layer_component {width : Nat} (add mul below : List F)
    (a m : Zkc.Protocols.Gkr.Wiring F width) (v : Table F width)
    (da : ofList? (width + width + width) add = some a)
    (dm : ofList? (width + width + width) mul = some m)
    (dv : ofList? width below = some v) (small : width + width + width < 64) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).components
      GkrSourceBodies.helper33Helper
      (.cons (some add) (.cons (some mul) (.cons (some below) (.cons (some width) .nil)))) =
      .done (.cons (some (GkrRoundsLayout.encode (Zkc.Protocols.Gkr.layer a m v))) .nil) := by
  change invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).components
    GkrSourceBodies.helper33Helper
    (Values.cons add (.cons mul (.cons below (.cons width .nil)))).present = _
  rw [HonestHelpers.component_present GkrSourceBodies.helper33Helper
    (.cons add (.cons mul (.cons below (.cons width .nil)))),
    layer_plain add mul below a m v da dm dv small]
  rfl

/-- Exact present wire-vector observation at the current source ABI. -/
theorem values_below_component {width : Nat} (add mul inputs : List F) (layers selector layerIndex : Nat)
    (circuit : Families.Gkr.Circuit F width)
    (da : StackedEncoding add layers selector circuit.add)
    (dm : StackedEncoding mul layers selector circuit.mul)
    (di : ofList? width inputs = some circuit.inputs)
    (capacity : layers ≤ 2 ^ selector) (small : width + width + width + selector < 64)
    (layersBound : layers < indexLimit) (inside : layerIndex < layers) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).components
      GkrSourceBodies.helper34Helper
      (.cons (some add) (.cons (some mul) (.cons (some inputs) (.cons (some layers)
        (.cons (some selector) (.cons (some width) (.cons (some layerIndex) .nil))))))) =
      .done (.cons (some (GkrRoundsLayout.encode
        (circuit.wires (layers - layerIndex - 1) (layerIndex + 1)))) .nil) := by
  change invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).components
    GkrSourceBodies.helper34Helper
    (Values.cons add (.cons mul (.cons inputs (.cons layers
      (.cons selector (.cons width (.cons layerIndex .nil))))))).present = _
  rw [HonestHelpers.component_present GkrSourceBodies.helper34Helper
    (.cons add (.cons mul (.cons inputs (.cons layers
      (.cons selector (.cons width (.cons layerIndex .nil))))))),
    values_below_plain add mul inputs layers selector layerIndex circuit da dm di capacity small
      layersBound inside]
  rfl

end ZkcSecurity.Realizations.Gkr.HonestCircuit
