import ZkcSecurity.Realizations.Gkr.HonestCircuitSource
import ZkcSecurity.Realizations.Gkr.HonestLineSource
import TestsSecurity.GkrHonestLineMath
import ZkcSecurity.Examples.Components.GkrFiniteCircuit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

noncomputable section
namespace TestsSecurity.GkrCurrentHelpers
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

/-- All equations below are about the regenerated current-source import. -/
theorem current_digest : GkrSourceData.snapshot.source =
    "sha256:0c1696d084f39ac0870c06bda4e8e92c2d372cc651491caee546c77671eec9d5" := rfl

/-- Malformed rows stop during the ordered domain admission. -/
theorem malformed_gate_map :
    invoke (helpers (G := ℚ)) GkrSourceBodies.scopedHelper44Helper
      (.cons ([0] : List ℚ) (.cons [] (.cons [3] (.cons [5] .nil)))) = .halt .refused := by
  rw [HonestCircuit.scopedHelper44_association.invoke GkrSourceViews.unit.linked]
  change (Evaluation.denoteCollect (helpers (G := ℚ)) HonestCircuit.gateCollection
    (.cons ([0] : List ℚ) (.cons [] (.cons [3] (.cons [5] .nil))))).bind _ = _
  have stopped := Evaluation.denoteCollect_admission_stop (helpers (F := ℚ) (G := ℚ)) HonestCircuit.gateCollection
    (.cons ([0] : List ℚ) (.cons [] (.cons [3] (.cons [5] .nil)))) .nil .refused (by rfl)
  simp only [Values.append] at stopped
  rw [stopped]
  rfl

/-- The actual traversal refuses a decrement past its input boundary. -/
theorem refused_layer_index :
    invoke (helpers (G := ℚ)) GkrSourceBodies.helper34Helper
      (.cons ([] : List ℚ) (.cons [] (.cons []
        (.cons 2 (.cons 1 (.cons 1 (.cons 2 .nil))))))) = .halt .refused := by
  rw [HonestCircuit.helper34_association.invoke GkrSourceViews.unit.linked, HonestCircuit.values_body]
  simp [Primitive.evaluate, primitiveOutcome, checkedIndices, indexLimit, PIR.Process.bind, Values.get]

/-- The complete present value is returned by the actual component table. -/
theorem read_output :
    invoke (plainHelpers (F := ℚ) (G := ℚ) GkrSourceViews.unit).components
      GkrSourceBodies.helper57Helper
      (.cons (some ([120, 30] : List ℚ)) (.cons (some 1) .nil)) =
      .done (.cons (some 30) .nil) := by
  simpa using HonestHelpers.element_component (G := ℚ) ([120, 30] : List ℚ) 1
    (by norm_num [indexLimit]) (by norm_num [indexLimit])

theorem changed_readback :
    invoke (plainHelpers (F := ℚ) (G := ℚ) GkrSourceViews.unit).components
      GkrSourceBodies.helper57Helper
      (.cons (some ([120, 30] : List ℚ)) (.cons (some 1) .nil)) ≠
      .done (.cons (some 31) .nil) := by
  rw [read_output]
  intro wrong
  have value := congrArg (fun xs => xs.get .here) (PIR.Process.done.inj wrong)
  norm_num [Values.get] at value

theorem read_after :
    invoke (plainHelpers (F := ℚ) (G := ℚ) GkrSourceViews.unit).components
      GkrSourceBodies.helper70Helper
      (.cons (some ([120, 30] : List ℚ)) (.cons (some 0) .nil)) =
      .done (.cons (some 30) .nil) := by
  simpa using HonestHelpers.element_after_component (G := ℚ) ([120, 30] : List ℚ) 0
    (by norm_num [indexLimit]) (by norm_num [indexLimit])

theorem read_past_end :
    invoke (helpers (G := ℚ)) GkrSourceBodies.helper57Helper
      (.cons ([120, 30] : List ℚ) (.cons 2 .nil)) = .done (.cons 0 .nil) := by
  simpa using HonestHelpers.element_equation (G := ℚ) ([120, 30] : List ℚ) 2
    (by norm_num [indexLimit]) (by norm_num [indexLimit])

theorem successor_overflow :
    invoke (helpers (G := ℚ)) GkrSourceBodies.helper70Helper
      (.cons ([120, 30] : List ℚ) (.cons (indexLimit - 1) .nil)) = .halt .refused := by
  exact HonestHelpers.element_after_overflow _ _ (by unfold indexLimit; omega)

theorem upper_layout (rho : ℚ) :
    invoke (helpers (G := ℚ)) GkrSourceBodies.helper36Helper
      (.cons upperAdd (.cons upperMul (.cons [rho] (.cons [8, 15] (.cons 1 .nil))))) =
      .done (GkrCallerRealization.raw rho).values := by
  rw [HonestHelpers.layout_equation upperAdd upperMul [8, 15] [rho] 1 (by decide)
    (by norm_num [HasShape, upperAdd]) (by norm_num [HasShape, upperMul])
    (by norm_num [upperAdd, indexLimit]) (by norm_num [upperMul, indexLimit])
    (by norm_num [indexLimit]) (by norm_num [indexLimit])]
  simp [upperAdd, upperMul, restrictPrefixValues, restrictValues,
    GkrCallerRealization.raw, GkrRoundsRealization.RawState.values, sub_eq_add_neg]

open TestsSecurity.GkrHonestLine
open CoefficientRows LineCoefficients _root_.Polynomial

theorem actual_quadratic :
    invoke (helpers (F := ℚ) (G := ℚ)) GkrSourceBodies.helper69Helper
      (.cons cubeValues (.cons [0, 0] (.cons [1, 1] (.cons 2 .nil)))) =
        .done (.cons [1, 3, 4] .nil) := by
  rw [HonestLine.coefficients_correspond 2 cubeValues [0, 0] [1, 1] cubeTable decoded
    rfl rfl (by norm_num [indexLimit]), quadratic_line]
  norm_num [row, List.range_succ, coeff_add, coeff_mul_X, coeff_X_pow, coeff_one]

theorem changed_highest :
    invoke (helpers (F := ℚ) (G := ℚ)) GkrSourceBodies.helper69Helper
      (.cons cubeValues (.cons [0, 0] (.cons [1, 1] (.cons 2 .nil)))) ≠
        .done (.cons [1, 3, 5] .nil) := by
  rw [actual_quadratic]
  intro wrong
  have coefficients := congrArg (fun xs => xs.get .here) (PIR.Process.done.inj wrong)
  norm_num [Values.get] at coefficients

theorem actual_translated :
    invoke (plainHelpers (F := ℚ) (G := ℚ) GkrSourceViews.unit).components
      GkrSourceBodies.helper69Helper
      (.cons (some cubeValues) (.cons (some [2, 3]) (.cons (some [5, 7]) (.cons (some 2) .nil)))) =
        .done (.cons (some [32, 78, 48]) .nil) := by
  rw [HonestLine.coefficients_component 2 cubeValues [2, 3] [5, 7] cubeTable decoded
    rfl rfl (by norm_num [indexLimit]), translated_line]
  norm_num [row, List.range_succ, coeff_add, coeff_mul_X, coeff_X_pow]

theorem actual_scalar :
    invoke (helpers (F := ℚ) (G := ℚ)) GkrSourceBodies.helper69Helper
      (.cons [7] (.cons [] (.cons [] (.cons 0 .nil)))) = .done (.cons [7] .nil) := by
  rw [HonestLine.line_coefficients (F := ℚ) [7] [] [] 0 rfl
    (by norm_num [indexLimit]) (by norm_num [indexLimit]) (by norm_num [indexLimit])]
  simp [row_constant]

theorem unequal_slope_rows :
    invoke (helpers (F := ℚ) (G := ℚ)) GkrSourceBodies.scopedHelper70Helper
      (.cons [1, 2] (.cons [3] (.cons 4 .nil))) = .halt .refused := by
  rw [HonestLine.scopedHelper70_association.invoke GkrSourceViews.unit.linked, HonestLine.slope_map_body]
  have stopped := Evaluation.denoteCollect_admission_stop (helpers (F := ℚ) (G := ℚ)) HonestLine.slopeCollection
    (.cons ([1, 2] : List ℚ) (.cons [3] .nil)) (.cons 4 .nil) .refused (by rfl)
  simp only [Values.append] at stopped
  rw [stopped]
  rfl

open Zkc.Protocols.AlgebraicRounds

theorem first_message : GkrRoundsReference.message (GkrCallerRealization.reference (0 : ℚ)) =
    ⟨120, -15, -105⟩ := by
  norm_num [GkrRoundsReference.message, GkrRoundsReference.pointMessage,
    GkrCallerRealization.reference, GkrCallerRealization.addTable, GkrCallerRealization.mulTable,
    GkrCallerRealization.below, GkrRoundsLayout.state, GkrRoundsLayout.replicate,
    GkrRoundsLayout.tile, GkrRoundsLayout.leading, GkrRoundsLayout.trailing,
    booleanSum, half, Gate.message, Gate.value, Gate.quadratic]

theorem actual_round :
    invoke (plainHelpers (F := ℚ) (G := ℚ) GkrSourceViews.unit).components
      GkrSourceBodies.helper41Helper (GkrCallerRealization.raw 0).values.present =
      .done (.cons (some 120) (.cons (some (-15)) (.cons (some (-105)) .nil))) := by
  rw [HonestHelpers.round_coefficients_component _ (GkrCallerRealization.reference 0)
    (GkrCallerRealization.represented 0).1 (by norm_num [indexLimit]), first_message]

theorem changed_round :
    invoke (plainHelpers (F := ℚ) (G := ℚ) GkrSourceViews.unit).components
      GkrSourceBodies.helper41Helper (GkrCallerRealization.raw 0).values.present ≠
      .done (.cons (some 121) (.cons (some (-15)) (.cons (some (-105)) .nil))) := by
  rw [actual_round]
  intro wrong
  have value := congrArg (fun xs => xs.get .here) (PIR.Process.done.inj wrong)
  norm_num [Values.get] at value

theorem actual_restriction (challenge : ℚ) :
    invoke (plainHelpers (F := ℚ) (G := ℚ) GkrSourceViews.unit).components
      GkrSourceBodies.helper45Helper
      ((GkrCallerRealization.raw 0).values.append (.cons challenge .nil)).present =
      .done ((GkrCallerRealization.raw 0).restrict challenge).values.present := by
  exact HonestHelpers.round_restriction_component _ (GkrCallerRealization.reference 0)
    (GkrCallerRealization.represented 0).1 (by norm_num [indexLimit]) challenge

theorem malformed_round :
    invoke (plainHelpers (F := ℚ) (G := ℚ) GkrSourceViews.unit).closed
      GkrSourceBodies.helper41Helper
      (.cons [] (.cons [0, 1] (.cons [1, 1] (.cons [1, 1] .nil)))) = .halt .refused := by
  rw [HonestHelpers.round_message_table, GkrRoundsProcesses.round_equation]
  rfl

/-- Restriction also retains the source split refusal before any update. -/
theorem refused_restriction (challenge : ℚ) :
    invoke (plainHelpers (F := ℚ) (G := ℚ) GkrSourceViews.unit).closed
      GkrSourceBodies.helper45Helper
      (.cons [] (.cons [0, 1] (.cons [1, 1] (.cons [1, 1] (.cons challenge .nil))))) =
      .halt .refused := by
  rw [HonestHelpers.round_restriction_table, GkrRoundsProcesses.fixGates_equation]
  change (GkrRoundsProcesses.fix (G := ℚ) [] challenge).bind _ = _
  rw [GkrRoundsProcesses.fix_all]
  rfl

#print axioms GkrSourceLaws.evaluate_extension
#print axioms GkrSourceLaws.evaluateWiring_extension
#print axioms GkrSourceLaws.evaluateCoefficients_equation
#print axioms GkrSourceLaws.linePoint_equation
#print axioms HonestCircuit.layer_component
#print axioms HonestCircuit.values_below_component
#print axioms HonestHelpers.layout_component
#print axioms HonestHelpers.round_coefficients_component
#print axioms HonestHelpers.round_restriction_component
#print axioms HonestHelpers.element_after_overflow
#print axioms HonestHelpers.round_coefficients
#print axioms HonestHelpers.round_restriction
#print axioms HonestHelpers.element_component
#print axioms HonestHelpers.element_after_component
#print axioms HonestLine.coefficients_component
#print axioms HonestLine.actual_line_polynomial
#print axioms mixed_two_layers
#print axioms malformed_round

end TestsSecurity.GkrCurrentHelpers
