import ZkcSecurityExamples.Gkr.HonestCircuitSource
import ZkcSecurityExamples.Components.GkrFiniteCircuit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

noncomputable section
namespace TestsSecurity.GkrHonestCircuit
open Zkc Source Structured
open ZkcExamples.Structured GkrSourceLaws SumcheckVerifierHelpers
open ZkcExamples.Structured.PrimitiveLibrary
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open ZkcSecurity.Examples.Components
open ZkcSecurity.Realizations.Gkr

/-- Independent mixed circuit: (3,5) -> (8,15) -> (120,30). -/
def circuit : ZkcSecurity.Families.Gkr.Circuit ℚ 1 :=
  ⟨GkrFiniteCircuit.inputTable, GkrFiniteCircuit.addWiring, GkrFiniteCircuit.mulWiring⟩

def upperAdd : List ℚ := [0, 0, 0, 0, 0, 0, 0, 1]
def upperMul : List ℚ := [0, 1, 0, 0, 0, 0, 0, 0]
def lowerAdd : List ℚ := [0, 1, 0, 0, 0, 0, 0, 0]
def lowerMul : List ℚ := [0, 0, 0, 0, 0, 1, 0, 0]
def rawAdd : List ℚ := upperAdd ++ lowerAdd
def rawMul : List ℚ := upperMul ++ lowerMul

theorem upper_add_encoding : GkrRoundsLayout.encode (circuit.add 0) = upperAdd := by
  norm_num [GkrRoundsLayout.encode, circuit, GkrFiniteCircuit.addWiring, vertex, upperAdd,
    Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]

theorem upper_mul_encoding : GkrRoundsLayout.encode (circuit.mul 0) = upperMul := by
  norm_num [GkrRoundsLayout.encode, circuit, GkrFiniteCircuit.mulWiring, vertex, upperMul,
    Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]

theorem lower_add_encoding : GkrRoundsLayout.encode (circuit.add 1) = lowerAdd := by
  norm_num [GkrRoundsLayout.encode, circuit, GkrFiniteCircuit.addWiring, vertex, lowerAdd,
    Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]

theorem lower_mul_encoding : GkrRoundsLayout.encode (circuit.mul 1) = lowerMul := by
  norm_num [GkrRoundsLayout.encode, circuit, GkrFiniteCircuit.mulWiring, vertex, lowerMul,
    Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]

theorem input_encoding : ofList? 1 ([3, 5] : List ℚ) = some circuit.inputs := by
  have encoded : GkrRoundsLayout.encode circuit.inputs = ([3, 5] : List ℚ) := by
    norm_num [GkrRoundsLayout.encode, circuit, GkrFiniteCircuit.inputTable, vertex]
  rw [← encoded, GkrRoundsLayout.decode_encode]

theorem add_encoding : HonestCircuit.StackedEncoding rawAdd 2 1 circuit.add := by
  constructor
  · norm_num [rawAdd, upperAdd, lowerAdd]
  · intro i bound
    have alternatives : i = 0 ∨ i = 1 := by omega
    rcases alternatives with rfl | rfl
    · rw [show block rawAdd 0 (2 ^ (1 + 1 + 1)) = upperAdd by rfl,
        ← upper_add_encoding, GkrRoundsLayout.decode_encode]
    · rw [show block rawAdd 1 (2 ^ (1 + 1 + 1)) = lowerAdd by rfl,
        ← lower_add_encoding, GkrRoundsLayout.decode_encode]

theorem mul_encoding : HonestCircuit.StackedEncoding rawMul 2 1 circuit.mul := by
  constructor
  · norm_num [rawMul, upperMul, lowerMul]
  · intro i bound
    have alternatives : i = 0 ∨ i = 1 := by omega
    rcases alternatives with rfl | rfl
    · rw [show block rawMul 0 (2 ^ (1 + 1 + 1)) = upperMul by rfl,
        ← upper_mul_encoding, GkrRoundsLayout.decode_encode]
    · rw [show block rawMul 1 (2 ^ (1 + 1 + 1)) = lowerMul by rfl,
        ← lower_mul_encoding, GkrRoundsLayout.decode_encode]

/-- The actual helper34 supplies the intermediate wires; they are not test
inputs to the upper layer helper. -/
theorem intermediate_values :
    invoke (helpers (G := ℚ)) GkrSourceBodies.helper34Helper
      (.cons rawAdd (.cons rawMul (.cons ([3, 5] : List ℚ)
        (.cons 2 (.cons 1 (.cons 1 (.cons 0 .nil))))))) = .done (.cons [8, 15] .nil) := by
  rw [HonestCircuit.values_below rawAdd rawMul [3, 5] 2 1 0 circuit add_encoding mul_encoding
    input_encoding (by decide) (by decide) (by norm_num [indexLimit]) (by decide)]
  rw [show circuit.wires (2 - 0 - 1) (0 + 1) = GkrCallerRealization.below from
    GkrFiniteCircuit.lower_layer]
  norm_num [GkrRoundsLayout.encode, GkrCallerRealization.below, vertex]

/-- Actual helper34 followed by actual helper33 computes the independent
circuit's outputs, exercising both mixed add/multiply layers. -/
theorem mixed_two_layers :
    (invoke (helpers (G := ℚ)) GkrSourceBodies.helper34Helper
      (.cons rawAdd (.cons rawMul (.cons ([3, 5] : List ℚ)
        (.cons 2 (.cons 1 (.cons 1 (.cons 0 .nil)))))))).bind (fun below =>
      invoke (helpers (G := ℚ)) GkrSourceBodies.helper33Helper
        (.cons upperAdd (.cons upperMul (.cons (below.get .here) (.cons 1 .nil))))) =
      .done (.cons [120, 30] .nil) := by
  rw [HonestCircuit.values_below rawAdd rawMul [3, 5] 2 1 0 circuit add_encoding mul_encoding
    input_encoding (by decide) (by decide) (by norm_num [indexLimit]) (by decide)]
  simp only [PIR.Process.bind, Values.get]
  rw [HonestCircuit.layer_encodes _ _ _ (circuit.add 0) (circuit.mul 0) (circuit.wires 1 1)
    (by rw [← upper_add_encoding, GkrRoundsLayout.decode_encode])
    (by rw [← upper_mul_encoding, GkrRoundsLayout.decode_encode])
    (GkrRoundsLayout.decode_encode _) (by decide)]
  rw [show Zkc.Protocols.Gkr.layer (circuit.add 0) (circuit.mul 0) (circuit.wires 1 1) =
      (fun bits => if bits 0 then (30 : ℚ) else 120) from GkrFiniteCircuit.outputs]
  norm_num [GkrRoundsLayout.encode, vertex]

/-- The zero-iteration boundary returns the exact inputs. -/
theorem last_layer_below :
    invoke (helpers (G := ℚ)) GkrSourceBodies.helper34Helper
      (.cons rawAdd (.cons rawMul (.cons ([3, 5] : List ℚ)
        (.cons 2 (.cons 1 (.cons 1 (.cons 1 .nil))))))) = .done (.cons [3, 5] .nil) := by
  rw [HonestCircuit.values_below rawAdd rawMul [3, 5] 2 1 1 circuit add_encoding mul_encoding
    input_encoding (by decide) (by decide) (by norm_num [indexLimit]) (by decide)]
  change (PIR.Process.done (.cons (GkrRoundsLayout.encode circuit.inputs) .nil) :
    Closed (Values (assignment ℚ ℚ) [.vector "bls12-381.fr"])) = _
  rw [HonestHelpers.encode_of_decodes [3, 5] circuit.inputs input_encoding]

/-- A larger selector separates the selector/width ABI slots. Arbitrary
field-valued padding remains outside the active layer blocks. -/
theorem padded_add_encoding (tail : List ℚ) (tailSize : tail.length = 16) :
    HonestCircuit.StackedEncoding (rawAdd ++ tail) 2 2 circuit.add := by
  constructor
  · simp [rawAdd, upperAdd, lowerAdd, tailSize]
  · intro i bound
    rw [HonestCircuit.block_append_tail rawAdd tail i _ (by
      have length : rawAdd.length = 16 := by rfl
      norm_num [length]
      omega)]
    exact add_encoding.2 i bound

theorem padded_mul_encoding (tail : List ℚ) (tailSize : tail.length = 16) :
    HonestCircuit.StackedEncoding (rawMul ++ tail) 2 2 circuit.mul := by
  constructor
  · simp [rawMul, upperMul, lowerMul, tailSize]
  · intro i bound
    rw [HonestCircuit.block_append_tail rawMul tail i _ (by
      have length : rawMul.length = 16 := by rfl
      norm_num [length]
      omega)]
    exact mul_encoding.2 i bound

theorem padded_values (addTail mulTail : List ℚ)
    (addSize : addTail.length = 16) (mulSize : mulTail.length = 16) :
    invoke (plainHelpers (F := ℚ) (G := ℚ) GkrSourceViews.unit).closed GkrSourceBodies.helper34Helper
      (.cons (rawAdd ++ addTail) (.cons (rawMul ++ mulTail) (.cons ([3, 5] : List ℚ)
        (.cons 2 (.cons 2 (.cons 1 (.cons 0 .nil))))))) = .done (.cons [8, 15] .nil) := by
  rw [HonestCircuit.values_below_plain _ _ [3, 5] 2 2 0 circuit
    (padded_add_encoding addTail addSize) (padded_mul_encoding mulTail mulSize)
    input_encoding (by decide) (by decide) (by norm_num [indexLimit]) (by decide)]
  rw [show circuit.wires (2 - 0 - 1) (0 + 1) = GkrCallerRealization.below from
    GkrFiniteCircuit.lower_layer]
  norm_num [GkrRoundsLayout.encode, GkrCallerRealization.below, vertex]

/-- Even a handler that refuses every call sees no calls from this helper;
all unread values and prior history carried by its state remain unchanged. -/
def refusingHandler : PIR.Handler (participantInterface ℚ ℚ) (List ℚ) Unit :=
  fun _ initial => ⟨.stopped .refused, initial, []⟩

theorem unchanged_suffix (suffix : List ℚ) :
    (invoke (plainHelpers (F := ℚ) (G := ℚ) GkrSourceViews.unit).closed GkrSourceBodies.helper34Helper
      (.cons rawAdd (.cons rawMul (.cons ([3, 5] : List ℚ)
        (.cons 2 (.cons 1 (.cons 1 (.cons 0 .nil)))))))).run refusingHandler suffix =
      ⟨.returned (.cons [8, 15] .nil), suffix, []⟩ := by
  rw [HonestCircuit.values_below_run rawAdd rawMul [3, 5] 2 1 0 circuit add_encoding mul_encoding
    input_encoding (by decide) (by decide) (by norm_num [indexLimit]) (by decide) refusingHandler suffix]
  rw [show circuit.wires (2 - 0 - 1) (0 + 1) = GkrCallerRealization.below from
    GkrFiniteCircuit.lower_layer]
  norm_num [GkrRoundsLayout.encode, GkrCallerRealization.below, vertex]

/-- Shape mismatch is refused before any scalar map callback. -/
theorem malformed_gate_map :
    invoke (helpers (G := ℚ)) GkrSourceBodies.scopedHelper44Helper
      (.cons ([0] : List ℚ) (.cons [] (.cons [3] (.cons [5] .nil)))) = .halt .refused := by
  rw [HonestCircuit.scopedHelper44_association.invoke GkrSourceViews.unit.linked]
  change (Evaluation.denoteCollect (helpers (G := ℚ)) HonestCircuit.gateCollection
    (.cons ([0] : List ℚ) (.cons [] (.cons [3] (.cons [5] .nil))))).bind _ = _
  have stopped : Evaluation.denoteCollect (helpers (G := ℚ)) HonestCircuit.gateCollection
      (.cons ([0] : List ℚ) (.cons [] (.cons [3] (.cons [5] .nil)))) = .halt .refused :=
    Evaluation.denoteCollect_admission_stop (helpers (G := ℚ)) HonestCircuit.gateCollection
      (.cons ([0] : List ℚ) (.cons [] (.cons [3] (.cons [5] .nil)))) .nil .refused
      (by rfl)
  rw [stopped]
  rfl

/-- Requesting a layer at the input boundary would subtract one from zero;
the actual helper refuses before touching even these malformed empty tables. -/
theorem refused_layer_index :
    invoke (helpers (G := ℚ)) GkrSourceBodies.helper34Helper
      (.cons ([] : List ℚ) (.cons [] (.cons []
        (.cons 2 (.cons 1 (.cons 1 (.cons 2 .nil))))))) = .halt .refused := by
  rw [HonestCircuit.helper34_association.invoke GkrSourceViews.unit.linked, HonestCircuit.values_body]
  simp [Primitive.evaluate, primitiveOutcome, checkedIndices, indexLimit, PIR.Process.bind, Values.get]

#print axioms HonestCircuit.index_point
#print axioms HonestCircuit.block_encode
#print axioms HonestCircuit.gate_equation
#print axioms HonestCircuit.gate_map_encodes
#print axioms HonestCircuit.layer_encodes
#print axioms HonestCircuit.block_decodes
#print axioms HonestCircuit.stacked_of_decodes
#print axioms HonestCircuit.block_append_tail
#print axioms HonestCircuit.values_step
#print axioms HonestCircuit.values_below
#print axioms HonestCircuit.layer_plain
#print axioms HonestCircuit.values_below_plain
#print axioms HonestCircuit.values_below_run
#print axioms mixed_two_layers
#print axioms padded_values
#print axioms unchanged_suffix
#print axioms malformed_gate_map
#print axioms refused_layer_index

end TestsSecurity.GkrHonestCircuit
