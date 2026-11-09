module

public import ProtocolProof.Components.ServiceInstallation

/-! The same service installation handles stochastic malformed input and nested callers. -/

public section
noncomputable section
open PIR ProtocolProof MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProtocolProofExamples.ServiceDecoding
abbrev Bits : Signature := ⟨Unit, fun _ ↦ Bool⟩
abbrev Words : Signature := ⟨Unit, fun _ ↦ Nat⟩
def half : ℝ≥0∞ := 1 / 2
private theorem halves : half + half = 1 := ENNReal.add_halves 1

noncomputable def words : System Unit Words Unit Nat where
  operations _ _ := Kernel.const Unit
    (half • Measure.dirac (⟨.returned 0, (), [0]⟩ : Execution Unit Nat Nat) +
      half • Measure.dirac (⟨.returned 2, (), [2]⟩ : Execution Unit Nat Nat))
  initial _ := Measure.dirac ()
  operation_mass _ _ _ := by simpa using halves
  initial_probability _ := inferInstance

noncomputable def bits : System Unit Bits Unit Nat where
  operations _ _ := Kernel.const Unit
    (half • Measure.dirac (⟨.returned false, (), [0]⟩ : Execution Unit Nat Bool) +
      half • Measure.dirac (⟨.stopped .refused, (), [2]⟩ : Execution Unit Nat Bool))
  initial _ := Measure.dirac ()
  operation_mass _ _ _ := by simpa using halves
  initial_probability _ := inferInstance

def decoder : OperationInterpretation Bits Words := fun _ ↦
  .call () fun word ↦ if word < 2 then .done (word == 1) else .halt .refused

private theorem decoder_law (current : Unit × List Nat) :
    bits.accumulatedOperations () () current =
      words.implementedOperations decoder () () current := by
  unfold System.implementedOperations
  rw [ProbabilityTheory.Kernel.map_apply _
    Execution.measurableEquiv.measurable]
  simp (disch := first | exact measurable_of_countable _ |
    exact (measurable_of_countable _).aemeasurable)
    [decoder, System.runFrom_call, System.accumulatedOperations_apply,
    words, bits, Measure.map_add, Measure.map_smul, Measure.bind_add_left, Measure.bind_smul,
    Execution.measurableEquiv, Execution.equiv]

/-- A single primitive representation establishes full probabilistic contextual installation. -/
noncomputable def installed : ServiceInstallation bits words decoder (fun _ ↦ True)
    (fun _ ↦ Eq) :=
  ServiceInstallation.ofMap bits words decoder (fun _ ↦ True) id measurable_id
    (fun e _ op current ↦ by cases e; cases op; simpa using decoder_law current)
    (fun _ _ ↦ by simp [bits, words, System.initialWithEvents])

/-- Reused body at two distinct sites; the second is skipped if the first decoding stops. -/
def pair : Process Bits Bool := do
  let first ← Process.call () .done
  let second ← Process.call () .done
  pure (first == second)

def nested (outer inner : Nat) : Process Bits Bool :=
  (List.range outer).foldlM (fun accepted _ ↦
    (List.range inner).foldlM (fun accepted _ ↦ do
      let value ← pair
      pure (accepted && value)) accepted) true

/-- One installation transports every full-record event for every finite nested caller. -/
theorem nested_event (outer inner : Nat) (event : Set (Execution Unit Nat Bool))
    (measurable : MeasurableSet event) :
    (bits.experiment (fun _ ↦ nested outer inner)).run () event =
      (words.experiment (fun _ ↦ (nested outer inner).interpret decoder)).run () event :=
  installed.event_eq _ event event measurable measurable
    (fun _ _ _ _ _ same ↦ by subst same; exact Iff.rfl) () trivial

end ProtocolProofExamples.ServiceDecoding
