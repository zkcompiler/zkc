module

public import ZkcSecurityExamples.Gkr.HonestCircuitValues
public import ZkcSecurityExamples.Gkr.HonestHelpersSource

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
      GkrSourceBodies.helper33Helper
      (Goals.LayerArguments.pack (Value := assignment F G)
        { addWeights := add, mulWeights := mul, below, width }) =
      .done (Goals.Layer.encode (ringModel F G)
        ⟨GkrRoundsLayout.encode (Zkc.Protocols.Gkr.layer a m v)⟩) := by
  exact closed_invoke_returned GkrSourceViews.unit _ _ _
    (layer_encodes add mul below a m v da dm dv small)

/-- The source ABI is `(add, mul, inputValues, layers, selector, width, layer)`.
The output is the entire wire vector, with no challenge or transcript effects. -/
theorem values_below_plain {width : Nat} (add mul inputValues : List F) (layers selector layerIndex : Nat)
    (circuit : Families.Gkr.Circuit F width)
    (da : StackedEncoding add layers selector circuit.add)
    (dm : StackedEncoding mul layers selector circuit.mul)
    (di : ofList? width inputValues = some circuit.inputs)
    (capacity : layers ≤ 2 ^ selector)
    (small : width + width + width + selector < 64)
    (layersBound : layers < indexLimit) (inside : layerIndex < layers) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
      GkrSourceBodies.helper34Helper
      (Goals.ValuesArguments.pack (Value := assignment F G)
        { addWeights := add, mulWeights := mul, inputValues := inputValues,
          layers, selector, width, layerIndex }) =
      .done (Goals.Traversal.encode (ringModel F G)
        ⟨GkrRoundsLayout.encode (circuit.wires (layers - layerIndex - 1) (layerIndex + 1))⟩) := by
  exact closed_invoke_returned GkrSourceViews.unit _ _ _
    (values_below add mul inputValues layers selector layerIndex circuit da dm di capacity small layersBound inside)

/-- Pure helper execution preserves every handler state, including all unread
input and transcript suffixes, and emits no events. -/
theorem values_below_run {width : Nat} {H E : Type} (add mul inputValues : List F)
    (layers selector layerIndex : Nat) (circuit : Families.Gkr.Circuit F width)
    (da : StackedEncoding add layers selector circuit.add)
    (dm : StackedEncoding mul layers selector circuit.mul)
    (di : ofList? width inputValues = some circuit.inputs)
    (capacity : layers ≤ 2 ^ selector)
    (small : width + width + width + selector < 64)
    (layersBound : layers < indexLimit) (inside : layerIndex < layers)
    (handler : PIR.Handler (participantInterface F G) H E) (initial : H) :
    (invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
      GkrSourceBodies.helper34Helper
      (Goals.ValuesArguments.pack (Value := assignment F G)
        { addWeights := add, mulWeights := mul, inputValues := inputValues,
          layers, selector, width, layerIndex })).run handler initial =
      ⟨.returned (Goals.Traversal.encode (ringModel F G)
        ⟨GkrRoundsLayout.encode (circuit.wires (layers - layerIndex - 1) (layerIndex + 1))⟩), initial, []⟩ := by
  rw [values_below_plain add mul inputValues layers selector layerIndex circuit da dm di capacity small layersBound inside]
  rfl

/-- The source component ABI retains `some` on the entire computed layer. -/
theorem layer_component {width : Nat} (add mul below : List F)
    (a m : Zkc.Protocols.Gkr.Wiring F width) (v : Table F width)
    (da : ofList? (width + width + width) add = some a)
    (dm : ofList? (width + width + width) mul = some m)
    (dv : ofList? width below = some v) (small : width + width + width < 64) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).components
      GkrSourceBodies.helper33Helper
      (Goals.LayerArguments.pack (Value := Component (assignment F G))
        { addWeights := some add, mulWeights := some mul, below := some below, width := some width }) =
      .done (Goals.Layer.encode (ringModel F G)
        ⟨GkrRoundsLayout.encode (Zkc.Protocols.Gkr.layer a m v)⟩).present := by
  exact component_invoke_returned GkrSourceViews.unit _ _ _
    (layer_encodes add mul below a m v da dm dv small)

/-- Exact present wire-vector observation at the current source ABI. -/
theorem values_below_component {width : Nat} (add mul inputValues : List F) (layers selector layerIndex : Nat)
    (circuit : Families.Gkr.Circuit F width)
    (da : StackedEncoding add layers selector circuit.add)
    (dm : StackedEncoding mul layers selector circuit.mul)
    (di : ofList? width inputValues = some circuit.inputs)
    (capacity : layers ≤ 2 ^ selector) (small : width + width + width + selector < 64)
    (layersBound : layers < indexLimit) (inside : layerIndex < layers) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).components
      GkrSourceBodies.helper34Helper
      (Goals.ValuesArguments.pack (Value := Component (assignment F G))
        { addWeights := some add, mulWeights := some mul, inputValues := some inputValues,
          layers := some layers, selector := some selector, width := some width,
          layerIndex := some layerIndex }) =
      .done (Goals.Traversal.encode (ringModel F G)
        ⟨GkrRoundsLayout.encode (circuit.wires (layers - layerIndex - 1) (layerIndex + 1))⟩).present := by
  exact component_invoke_returned GkrSourceViews.unit _ _ _
    (values_below add mul inputValues layers selector layerIndex circuit da dm di capacity small layersBound inside)

end ZkcSecurity.Realizations.Gkr.HonestCircuit
