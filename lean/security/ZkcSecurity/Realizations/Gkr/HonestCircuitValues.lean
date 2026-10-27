module

public import ZkcSecurity.Realizations.Gkr.HonestCircuit

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

/-- The literal loop callback of helper34. -/
def valuesLoopBody : Region dialect
    [.index, .vector "bls12-381.fr", .index, .vector "bls12-381.fr",
      .vector "bls12-381.fr", .index, .index]
    [.vector "bls12-381.fr", .index, .vector "bls12-381.fr",
      .vector "bls12-381.fr", .index, .index] :=
    .letOp (.mark "s11") .nil .nil <|
    .letOp (.exec (.indexConstant 1)) .nil .nil <|
    .letOp (.mark "s12") .nil .nil <|
    .letOp (.exec (.indexSub)) (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil <|
    .letOp (.mark "s14") .nil .nil <|
    .letOp (.invoke ⟨"zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr"]⟩) (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil))) .nil <|
    .letOp (.mark "s15") .nil .nil <|
    .letOp (.invoke ⟨"zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr"]⟩) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there .here) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil))) .nil <|
    .letOp (.mark "s16") .nil .nil <|
    .letOp (.invoke ⟨"zkl_3a99bc0fa1dab7cb27c9ec80754c3782b0a32e76ddc961a50e12c24c6cbff683", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .index], [.vector "bls12-381.fr"]⟩) (.cons (.there .here) (.cons .here (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) .nil)))) .nil <|
    .ret (.cons .here (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) .nil))))))

/-- Structural callback expansion, with its checked decrement still visible. -/
theorem values_step_body (table : Meanings F G) (iteration current width selector : Nat)
    (below add mul : List F) :
    valuesLoopBody.denote (meaning F G table)
      (Values.cons iteration (.cons below (.cons current (.cons add (.cons mul
        (.cons selector (.cons width .nil))))))).get =
      (primitiveOutcome (Primitive.evaluate (F := F) (G := G) .indexSub
        (.cons current (.cons 1 .nil)))).bind fun next =>
      (invoke table GkrSourceBodies.selectBlockHelper
        (.cons add (.cons (next.get .here) (.cons selector .nil)))).bind fun a =>
      (invoke table GkrSourceBodies.selectBlockHelper
        (.cons mul (.cons (next.get .here) (.cons selector .nil)))).bind fun m =>
      (invoke table GkrSourceBodies.helper33Helper
        (.cons (a.get .here) (.cons (m.get .here) (.cons below (.cons width .nil))))).bind fun result =>
      .done (.cons (result.get .here) (.cons (next.get .here)
        (.cons add (.cons mul (.cons selector (.cons width .nil)))))) := by
  derive_process

/-- One reached traversal step maintains the mathematical evaluator and the
backward layer index. This covers arbitrary raw stacks and active wiring. -/
theorem values_step {width : Nat} (add mul : List F) (layers selector : Nat)
    (circuit : Families.Gkr.Circuit F width)
    (da : StackedEncoding add layers selector circuit.add)
    (dm : StackedEncoding mul layers selector circuit.mul)
    (capacity : layers ≤ 2 ^ selector)
    (small : width + width + width + selector < 64)
    (layersBound : layers < indexLimit) (iteration : Nat) (inside : iteration < layers) :
    valuesLoopBody.denote (meaning F G (helpers (G := G)))
      (Values.cons iteration
        (.cons (GkrRoundsLayout.encode (circuit.wires iteration (layers - iteration)))
          (.cons (layers - iteration) (.cons add (.cons mul (.cons selector (.cons width .nil))))))).get =
      .done (.cons (GkrRoundsLayout.encode (circuit.wires (iteration + 1) (layers - (iteration + 1))))
        (.cons (layers - (iteration + 1)) (.cons add (.cons mul (.cons selector (.cons width .nil)))))) := by
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
  rw [values_step_body]
  simp only [Primitive.evaluate, primitiveOutcome, checkedIndices, currentBound,
    show 1 < indexLimit by decide +kernel, positive, nextBound, and_self, ite_true,
    PIR.Process.bind, Values.get]
  rw [selectBlock_equation add _ selector _ da.1 (by positivity) position addBound]
  simp only [PIR.Process.bind, Values.get]
  rw [selectBlock_equation mul _ selector _ dm.1 (by positivity) position mulBound]
  simp only [PIR.Process.bind, Values.get]
  rw [layer_encodes _ _ _ (circuit.add _) (circuit.mul _)
    (circuit.wires iteration (layers - iteration))
    (da.2 _ (by omega)) (dm.2 _ (by omega)) (GkrRoundsLayout.decode_encode _) (by omega)]
  simp only [PIR.Process.bind, Values.get, next]
  have belowIndex : layers - (iteration + 1) + 1 = layers - iteration := by omega
  simp only [Families.Gkr.Circuit.wires, Zkc.Protocols.Gkr.values_succ, belowIndex]

/-- Helper34's structural expansion, including both guarded subtractions. -/
theorem values_body (table : Meanings F G) (add mul inputs : List F)
    (layers selector width layerIndex : Nat) :
    GkrSourceBodies.helper34Body.denote (meaning F G table)
      (Values.cons add (.cons mul (.cons inputs (.cons layers
        (.cons selector (.cons width (.cons layerIndex .nil))))))).get =
      (primitiveOutcome (Primitive.evaluate (F := F) (G := G) .indexSub
        (.cons layers (.cons layerIndex .nil)))).bind fun remaining =>
      (primitiveOutcome (Primitive.evaluate (F := F) (G := G) .indexSub
        (.cons (remaining.get .here) (.cons 1 .nil)))).bind fun count =>
      (Evaluation.denoteLoop [.vector "bls12-381.fr", .index]
        [.vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index]
        (fun args => valuesLoopBody.denote (meaning F G table) args.get) 0 (count.get .here)
        (.cons inputs (.cons layers .nil))
        (.cons add (.cons mul (.cons selector (.cons width .nil))))).bind fun result =>
        .done (.cons (result.get .here) .nil) := by
  simp only [GkrSourceBodies.helper34Body, valuesLoopBody, Region.denote, meaning, Evaluation.meaning,
    Evaluation.operation, Operands.eval, Regions.denote, Values.get_cons, Values.get,
    SumcheckHelperLaws.prepend_empty, SumcheckHelperLaws.prepend_one,
    SumcheckHelperLaws.prepend_two,
    Environment.push, SiteObservations.closed, SiteObservations.silent,
    PIR.Process.bind, Primitive.evaluate, primitiveOutcome,
    show 0 < indexLimit by decide +kernel, show 1 < indexLimit by decide +kernel,
    ite_true, Values.split]
  rfl

/-- Actual helper34 equals the independent recursive circuit evaluator. Its
requested layer is strictly below `layers`; the result is the layer below that
request, at index `layerIndex + 1`, after `layers - layerIndex - 1` steps. -/
theorem values_below {width : Nat} (add mul inputs : List F) (layers selector layerIndex : Nat)
    (circuit : Families.Gkr.Circuit F width)
    (da : StackedEncoding add layers selector circuit.add)
    (dm : StackedEncoding mul layers selector circuit.mul)
    (di : ofList? width inputs = some circuit.inputs)
    (capacity : layers ≤ 2 ^ selector)
    (small : width + width + width + selector < 64)
    (layersBound : layers < indexLimit) (inside : layerIndex < layers) :
    invoke (helpers (G := G)) GkrSourceBodies.helper34Helper
      (.cons add (.cons mul (.cons inputs (.cons layers
        (.cons selector (.cons width (.cons layerIndex .nil))))))) =
      .done (.cons (GkrRoundsLayout.encode
        (circuit.wires (layers - layerIndex - 1) (layerIndex + 1))) .nil) := by
  have indexBound : layerIndex < indexLimit := by omega
  have remainingBound : layers - layerIndex < indexLimit := by omega
  have countBound : layers - layerIndex - 1 < indexLimit := by omega
  rw [helper34_association.invoke unit.linked, values_body]
  simp only [Primitive.evaluate, primitiveOutcome, checkedIndices, layersBound, indexBound,
    remainingBound, countBound, show 1 < indexLimit by decide +kernel,
    show layerIndex ≤ layers by omega, show 1 ≤ layers - layerIndex by omega,
    and_self, ite_true, PIR.Process.bind, Values.get]
  rw [denoteLoop_states (F := F) (G := G) [.vector "bls12-381.fr", .index]
    [.vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index] _ (layers - layerIndex - 1) _
    (.cons add (.cons mul (.cons selector (.cons width .nil))))
    (fun i => .cons (GkrRoundsLayout.encode (circuit.wires i (layers - i)))
      (.cons (layers - i) .nil)) ?_ ?_]
  · simp only [PIR.Process.bind, Values.get]
    rw [show layers - (layers - layerIndex - 1) = layerIndex + 1 by omega]
  · rw [← HonestHelpers.encode_of_decodes inputs circuit.inputs di]
    rfl
  · intro i bound
    simp only [Evaluation.invokeCallback, Values.append]
    exact values_step add mul layers selector circuit da dm capacity small layersBound i (by omega)

end ZkcSecurity.Realizations.Gkr.HonestCircuit
