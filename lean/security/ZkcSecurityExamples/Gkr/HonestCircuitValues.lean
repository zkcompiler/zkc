module

public import ZkcSecurityExamples.Gkr.HonestCircuit
public import ZkcSecurityExamples.Gkr.HonestTraversalGoals

@[expose] public section

/-! Correspondence of the actual backward layer traversal with the independent
recursive circuit evaluator. Exact stack shape, active blocks, padding and all
index bounds are separate data conditions, never helper correctness premises. -/

namespace ZkcSecurity.Realizations.Gkr.HonestCircuit
open Zkc Source Structured
open ZkcExamples.Structured GkrSourceViews GkrSourceLaws
open ZkcExamples.Structured.PrimitiveLibrary
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open ZkcSecurity.Examples.Components

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
attribute [local implicit_reducible] Op.arguments Op.results Op.regions

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- A raw power-of-two stack contains the specified active wiring blocks.
Blocks from `layers` onwards are unrestricted padding. -/
def StackedEncoding {width : Nat} (raw : List F) (layers selector : Nat)
    (wiring : Nat → Zkc.Protocols.Gkr.Wiring F width) : Prop :=
  raw.length = 2 ^ selector * 2 ^ (width + width + width) ∧
    ∀ position < layers,
      ofList? (width + width + width)
        (block raw position (2 ^ (width + width + width))) = some (wiring position)

omit [Field F] [DecidableEq F] in
/-- A fully decoded stack supplies the exact MSB-first suffix block. -/
theorem block_decodes {prefixBits suffix : Nat} (raw : List F)
    (table : Table F (suffix + prefixBits)) (decoded : ofList? (suffix + prefixBits) raw = some table)
    (position : Fin (2 ^ prefixBits)) :
    ofList? suffix (block raw position.val (2 ^ suffix)) =
      some (fun tail => table (Quadratic.point prefixBits (vertex prefixBits position) tail)) := by
  rw [← HonestHelpers.encode_of_decodes raw table decoded, block_encode,
    GkrRoundsLayout.decode_encode]

omit [Field F] [DecidableEq F] in
/-- A decoded stack and mathematical prefix slices establish the raw encoding
condition. No specification of unused padding slices is needed. -/
theorem stacked_of_decodes {width selector : Nat} (raw : List F) (layers : Nat)
    (table : Table F (width + width + width + selector))
    (wiring : Nat → Zkc.Protocols.Gkr.Wiring F width)
    (decoded : ofList? (width + width + width + selector) raw = some table)
    (capacity : layers ≤ 2 ^ selector)
    (active : ∀ position : Fin (2 ^ selector), position.val < layers →
      wiring position.val = fun tail => table (Quadratic.point selector (vertex selector position) tail)) :
    StackedEncoding raw layers selector wiring := by
  constructor
  · rw [ofList?_length raw table decoded, Nat.pow_add, Nat.mul_comm]
  · intro position inside
    have bound : position < 2 ^ selector := by omega
    rw [block_decodes raw table decoded ⟨position, bound⟩, active ⟨position, bound⟩ inside]

omit [Field F] [DecidableEq F] in
/-- A suffix outside a complete active block cannot change that block. -/
theorem block_append_tail (xs tail : List F) (position size : Nat)
    (inside : (position + 1) * size ≤ xs.length) :
    block (xs ++ tail) position size = block xs position size := by
  rw [Nat.add_mul, Nat.one_mul] at inside
  have before : position * size ≤ xs.length := by omega
  have remaining : size ≤ (xs.drop (position * size)).length := by
    simp only [List.length_drop]
    omega
  simp only [block, List.drop_append_of_le_length before,
    List.take_append_of_le_length remaining]

/-- One reached traversal step maintains the mathematical evaluator and the
backward layer index. This covers arbitrary raw stacks and active wiring. -/
theorem values_step {width : Nat} (add mul : List F) (layers selector : Nat)
    (circuit : Families.Gkr.Circuit F width)
    (da : StackedEncoding add layers selector circuit.add)
    (dm : StackedEncoding mul layers selector circuit.mul)
    (capacity : layers ≤ 2 ^ selector)
    (small : width + width + width + selector < 64)
    (layersBound : layers < indexLimit) (iteration : Nat) (inside : iteration < layers) :
    Goals.TraversalStep.body.denote (meaning F G (helpers (G := G)))
      (Goals.TraversalStepArguments.pack (Value := assignment F G)
        { iteration, values := GkrRoundsLayout.encode (circuit.wires iteration (layers - iteration)),
          current := layers - iteration, addWeights := add, mulWeights := mul, selector, width }).get =
      .done (Goals.TraversalStep.encode (ringModel F G)
        { values := GkrRoundsLayout.encode (circuit.wires (iteration + 1) (layers - (iteration + 1))),
          current := layers - (iteration + 1), addWeights := add, mulWeights := mul, selector, width }) := by
  have currentBound : layers - iteration < indexLimit := by omega
  have positive : 1 ≤ layers - iteration := by omega
  have nextBound : layers - iteration - 1 < indexLimit := by omega
  have next : layers - iteration - 1 = layers - (iteration + 1) := by omega
  have position : layers - iteration - 1 < 2 ^ selector := by omega
  have powerSmall : 2 ^ (width + width + width + selector) < indexLimit :=
    Nat.pow_lt_pow_right (by decide) small
  have addBound : add.length < indexLimit := by
    rw [da.1, ← Nat.pow_add]
    simpa [Nat.add_comm] using powerSmall
  have mulBound : mul.length < indexLimit := by
    rw [dm.1, ← Nat.pow_add]
    simpa [Nat.add_comm] using powerSmall
  dsimp only [Goals.TraversalStepArguments.pack]
  simp only [meaning]
  rw [Evaluation.denote_meaning_eq_meaningOn, Goals.traversalStepProcess_equation]
  dsimp only [Goals.traversalStepProcess, Goals.traversalStepProcess_certificate,
    Op.arguments, Op.results, Op.regions]
  simp only [Primitive.evaluateOn, primitiveOutcome, checkedIndices, currentBound,
    show 1 < indexLimit by decide +kernel, positive, nextBound, and_self, ite_true,
    PIR.Process.bind, Values.get, Op.arguments, Op.results, Op.regions,
    SumcheckHelperLaws.prepend_empty, SumcheckHelperLaws.prepend_one,
    Environment.prepend, Environment.push, Values.get_head, Values.get_tail]
  rw [selectBlock_equation add _ selector _ da.1 (by positivity) position addBound]
  simp only [PIR.Process.bind, Values.get, Op.arguments, Op.results, Op.regions,
    SumcheckHelperLaws.prepend_empty, SumcheckHelperLaws.prepend_one,
    Environment.prepend, Environment.push, Values.get_head, Values.get_tail]
  rw [selectBlock_equation mul _ selector _ dm.1 (by positivity) position mulBound]
  simp only [PIR.Process.bind, Values.get, Op.arguments, Op.results, Op.regions,
    SumcheckHelperLaws.prepend_empty, SumcheckHelperLaws.prepend_one,
    Environment.prepend, Environment.push, Values.get_head, Values.get_tail]
  rw [layer_encodes _ _ _ (circuit.add _) (circuit.mul _)
    (circuit.wires iteration (layers - iteration))
    (da.2 _ (by omega)) (dm.2 _ (by omega)) (GkrRoundsLayout.decode_encode _) (by omega)]
  simp only [PIR.Process.bind, Values.get, next, Goals.TraversalStep.encode,
    Op.arguments, Op.results, Op.regions,
    SumcheckHelperLaws.prepend_empty, SumcheckHelperLaws.prepend_one,
    Environment.prepend, Environment.push, Values.get_head, Values.get_tail]
  have belowIndex : layers - (iteration + 1) + 1 = layers - iteration := by omega
  simp only [Families.Gkr.Circuit.wires, Zkc.Protocols.Gkr.values_succ, belowIndex]

/-- Actual helper34 equals the independent recursive circuit evaluator. Its
requested layer is strictly below `layers`; the result is the layer below that
request, at index `layerIndex + 1`, after `layers - layerIndex - 1` steps. -/
theorem values_below {width : Nat} (add mul inputValues : List F) (layers selector layerIndex : Nat)
    (circuit : Families.Gkr.Circuit F width)
    (da : StackedEncoding add layers selector circuit.add)
    (dm : StackedEncoding mul layers selector circuit.mul)
    (di : ofList? width inputValues = some circuit.inputs)
    (capacity : layers ≤ 2 ^ selector)
    (small : width + width + width + selector < 64)
    (layersBound : layers < indexLimit) (inside : layerIndex < layers) :
    invoke (helpers (G := G)) GkrSourceBodies.helper34Helper
      (Goals.Traversal.Inputs.pack (Value := assignment F G)
        { addWeights := add, mulWeights := mul, inputValues, layers, selector, width, layerIndex }) =
      .done (Goals.Traversal.encode (ringModel F G)
        ⟨GkrRoundsLayout.encode (circuit.wires (layers - layerIndex - 1) (layerIndex + 1))⟩) := by
  have indexBound : layerIndex < indexLimit := by omega
  have remainingBound : layers - layerIndex < indexLimit := by omega
  have countBound : layers - layerIndex - 1 < indexLimit := by omega
  dsimp only [Goals.Traversal.Inputs.pack]
  rw [circuit_bodies.values.invoke unit.linked]
  simp only [meaning]
  rw [Evaluation.denote_meaning_eq_meaningOn, Goals.valuesProcess_equation]
  dsimp only [Goals.valuesProcess, Goals.valuesProcess_certificate, Op.arguments, Op.results, Op.regions]
  simp only [Primitive.evaluateOn, primitiveOutcome, checkedIndices, layersBound, indexBound,
    remainingBound, countBound, show 0 < indexLimit by decide +kernel,
    show 1 < indexLimit by decide +kernel,
    show layerIndex ≤ layers by omega, show 1 ≤ layers - layerIndex by omega,
    and_self, ite_true, PIR.Process.bind, Values.get,
    Op.arguments, Op.results, Op.regions,
    SumcheckHelperLaws.prepend_empty, SumcheckHelperLaws.prepend_one,
    Environment.prepend, Environment.push, Values.get_head, Values.get_tail, Values.split]
  rw [← Evaluation.denoteLoop_eq_denoteLoopOn]
  erw [denoteLoop_states (F := F) (G := G) Goals.TraversalState.types Goals.TraversalCaptures.types
    _ (layers - layerIndex - 1) _
    (Goals.TraversalCaptures.pack (Value := assignment F G)
      { addWeights := add, mulWeights := mul, selector, width })
    (fun i => Goals.TraversalState.pack (Value := assignment F G)
      { values := GkrRoundsLayout.encode (circuit.wires i (layers - i)), current := layers - i }) ?_ ?_]
  · simp only [PIR.Process.bind, Values.get, Op.arguments, Op.results, Op.regions,
      SumcheckHelperLaws.prepend_empty, SumcheckHelperLaws.prepend_one,
      Environment.prepend, Environment.push, Values.get_head, Values.get_tail]
    rw [show layers - (layers - layerIndex - 1) = layerIndex + 1 by omega]
  · rw [← HonestHelpers.encode_of_decodes inputValues circuit.inputs di]
    rfl
  · intro i bound
    have iteration := values_step (G := G) add mul layers selector circuit da dm capacity small layersBound i (by omega)
    simp only [Goals.TraversalStepArguments.pack, meaning] at iteration
    rw [Evaluation.denote_meaning_eq_meaningOn, Goals.traversalStepProcess_equation] at iteration
    dsimp only [Goals.traversalStepProcess, Goals.traversalStepProcess_certificate] at iteration
    simp only [Evaluation.invokeCallback, Goals.TraversalState.pack, Goals.TraversalCaptures.pack,
      Values.append, PIR.Process.bind_assoc, Goals.TraversalStep.encode,
      Op.arguments, Op.results, Op.regions,
      SumcheckHelperLaws.prepend_empty, SumcheckHelperLaws.prepend_one,
      Environment.prepend, Environment.push, Values.get_head, Values.get_tail, Values.get,
      Primitive.evaluateOn, primitiveOutcome, checkedIndices, PIR.Process.bind, Goals.TraversalStep.decode,
      show 1 < indexLimit by decide +kernel, ite_true] at iteration ⊢
    exact iteration
end ZkcSecurity.Realizations.Gkr.HonestCircuit
