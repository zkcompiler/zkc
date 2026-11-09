module

public import Zkc.Protocol.Semantics.System
import Zkc.Protocol.Internal.Process

/-!
# Complete execution regression controls

The public tests use one fixed System and retain Outcome, final state, and the entire ordered
event log. The final internal control explains why ordinary FreeM bind cannot replace Process
bind. No success projection or conditioning is used to define any experiment.
-/

public section

open PIR MeasureTheory ProbabilityTheory ProtocolProof
open scoped ENNReal

namespace ProtocolProofExamples.ExecutionControls

inductive Operation where
  | first | second | stop (reason : Stop) | later | gate

abbrev signature : Signature where
  Op := Operation
  Reply _ := Unit

/-- Distinct event blocks expose reordering, rollback, and execution after a failure. -/
@[expose] def handler : Handler signature Nat Nat
  | .first, state => ⟨.returned (), state + 1, [10, 11]⟩
  | .second, state => ⟨.returned (), state * 2, [20, 21]⟩
  | .stop reason, state => ⟨.stopped reason, state + 7, [30, 31]⟩
  | .later, state => ⟨.returned (), state + 100, [90, 91]⟩
  | .gate, state => if state = 0 then ⟨.stopped .refused, state + 5, [40, 41]⟩
      else ⟨.returned (), state + 5, [50, 51]⟩

/-- Randomness is in the whole initial law, not in a choice of system after seeing an outcome. -/
@[expose] noncomputable def initialLaw : Measure Nat :=
  (2 : ℝ≥0∞)⁻¹ • Measure.dirac 0 + (2 : ℝ≥0∞)⁻¹ • Measure.dirac 1

theorem initialLaw_normalized : initialLaw Set.univ = 1 := by
  simp [initialLaw, ENNReal.inv_two_add_inv_two]

@[expose] noncomputable def system : System Unit signature Nat Nat where
  operations _ operation := Kernel.deterministic (handler operation) (measurable_of_countable _)
  initial _ := initialLaw
  operation_mass _ _ _ := by simp
  initial_probability _ := ⟨initialLaw_normalized⟩

theorem primitive_eq_dirac (operation : signature.Op) (state : Nat) :
    system.operations () operation state = Measure.dirac (handler operation state) := rfl

@[expose] def processHalt (reason : Stop) : Process signature Nat :=
  .call .first fun _ ↦ .call .second fun _ ↦ .halt reason

@[expose] def handlerStop (reason : Stop) : Process signature Nat :=
  .call .first fun _ ↦ .call .second fun _ ↦ .call (.stop reason) fun _ ↦
    .call .later fun _ ↦ .done 42

@[expose] def haltRecord (reason : Stop) (state : Nat) (prior : List Nat) : Execution Nat Nat Nat :=
  ⟨.stopped reason, (state + 1) * 2, prior ++ [10, 11, 20, 21]⟩

@[expose] def stopRecord (reason : Stop) (state : Nat) (prior : List Nat) : Execution Nat Nat Nat :=
  ⟨.stopped reason, (state + 1) * 2 + 7, prior ++ [10, 11, 20, 21, 30, 31]⟩

/-- Universal in Stop: reject, abort, exhausted, incomplete, and refused retain their identity. -/
theorem process_halt_complete (reason : Stop) (state : Nat) (prior : List Nat) :
    system.runFrom () (processHalt reason) (state, prior) =
      Measure.dirac (haltRecord reason state prior) := by
  rw [system.runFrom_eq_dirac () handler primitive_eq_dirac]
  rfl

/-- The stopping operation contributes both its reached state and its entire event block. -/
theorem handler_stop_complete (reason : Stop) (state : Nat) (prior : List Nat) :
    system.runFrom () (handlerStop reason) (state, prior) =
      Measure.dirac (stopRecord reason state prior) := by
  rw [system.runFrom_eq_dirac () handler primitive_eq_dirac]
  rfl

/-- Both stop mechanisms preserve unit mass on the exact record with a nonempty prefix. -/
theorem all_stop_reasons_full_mass (reason : Stop) :
    system.runFrom () (processHalt reason) (3, [7, 8])
        {haltRecord reason 3 [7, 8]} = 1 ∧
    system.runFrom () (handlerStop reason) (3, [7, 8])
        {stopRecord reason 3 [7, 8]} = 1 := by
  simp [process_halt_complete, handler_stop_complete]

/-- A failed call does not reach the later return, even with the correct stopped state and log. -/
theorem failed_call_no_return (reason : Stop) :
    system.runFrom () (handlerStop reason) (3, [7, 8])
      {⟨.returned 42, 15, [7, 8, 10, 11, 20, 21, 30, 31]⟩} = 0 := by
  simp [handler_stop_complete, stopRecord]

/-- The complete record that would result from running the forbidden successor has mass zero. -/
theorem failed_call_no_successor (reason : Stop) :
    system.runFrom () (handlerStop reason) (3, [7, 8])
      {⟨.returned 42, 115, [7, 8, 10, 11, 20, 21, 30, 31, 90, 91]⟩} = 0 := by
  simp [handler_stop_complete, stopRecord]

/-- Stop reasons cannot be merged or relabelled, even if state and every event agree. -/
theorem failed_call_no_wrong_reason (reason other : Stop) (different : reason ≠ other) :
    system.runFrom () (handlerStop reason) (3, [7, 8])
      {stopRecord other 3 [7, 8]} = 0 := by
  simp [handler_stop_complete, stopRecord, different]

/-- Neither rolling back the failed call nor executing the next call yields a possible state. -/
theorem failed_call_no_wrong_state (reason : Stop) :
    system.runFrom () (handlerStop reason) (3, [7, 8])
        {⟨.stopped reason, 8, [7, 8, 10, 11, 20, 21, 30, 31]⟩} = 0 ∧
    system.runFrom () (handlerStop reason) (3, [7, 8])
        {⟨.stopped reason, 115, [7, 8, 10, 11, 20, 21, 30, 31]⟩} = 0 := by
  simp [handler_stop_complete, stopRecord]

/-- Dropping, reversing, or extending the reached log changes the complete execution. -/
theorem failed_call_no_wrong_events (reason : Stop) :
    system.runFrom () (handlerStop reason) (3, [7, 8])
        {⟨.stopped reason, 15, [7, 8, 10, 11, 20, 21]⟩} = 0 ∧
    system.runFrom () (handlerStop reason) (3, [7, 8])
        {⟨.stopped reason, 15, [7, 8, 20, 21, 10, 11, 30, 31]⟩} = 0 ∧
    system.runFrom () (handlerStop reason) (3, [7, 8])
        {⟨.stopped reason, 15, [7, 8, 10, 11, 20, 21, 30, 31, 90, 91]⟩} = 0 := by
  simp [handler_stop_complete, stopRecord]

@[expose] def mixedClient : Process signature Nat :=
  .call .gate fun _ ↦ .call .first fun _ ↦ .done 42

@[expose] def stoppedRecord : Execution Nat Nat Nat := ⟨.stopped .refused, 5, [40, 41]⟩
@[expose] def returnedRecord : Execution Nat Nat Nat := ⟨.returned 42, 7, [50, 51, 10, 11]⟩

theorem mixed_run_zero : system.run () mixedClient 0 = Measure.dirac stoppedRecord := by
  rw [system.run_eq_dirac () handler primitive_eq_dirac]
  rfl

theorem mixed_run_one : system.run () mixedClient 1 = Measure.dirac returnedRecord := by
  rw [system.run_eq_dirac () handler primitive_eq_dirac]
  rfl

@[expose] noncomputable def mixedExperiment : Experiment Unit (Execution Nat Nat Nat) :=
  system.experiment (fun _ ↦ mixedClient)

/-- Equality of whole measures preserves the original mass of both complete execution records. -/
theorem mixed_experiment_complete :
    mixedExperiment.run () =
      (2 : ℝ≥0∞)⁻¹ • Measure.dirac stoppedRecord +
      (2 : ℝ≥0∞)⁻¹ • Measure.dirac returnedRecord := by
  rw [mixedExperiment, system.experiment_run]
  change initialLaw.bind (system.run () mixedClient) = _
  ext event hevent
  rw [Measure.bind_apply hevent (system.run () mixedClient).measurable.aemeasurable]
  simp [initialLaw, mixed_run_zero, mixed_run_one]

/-- Each input atom has its original, positive probability. -/
theorem initialLaw_atom_masses :
    initialLaw {0} = (2 : ℝ≥0∞)⁻¹ ∧ initialLaw {1} = (2 : ℝ≥0∞)⁻¹ := by
  simp [initialLaw]

theorem mixed_stopped_record_mass :
    mixedExperiment.run () {stoppedRecord} = (2 : ℝ≥0∞)⁻¹ := by
  simp [mixed_experiment_complete, stoppedRecord, returnedRecord]

theorem mixed_returned_record_mass :
    mixedExperiment.run () {returnedRecord} = (2 : ℝ≥0∞)⁻¹ := by
  simp [mixed_experiment_complete, stoppedRecord, returnedRecord]

/-- Events are sets of full records; these predicates do not change the experiment carrier. -/
@[expose] def stoppedEvent : Set (Execution Nat Nat Nat) :=
  {result | ∃ reason, result.outcome = .stopped reason}
@[expose] def returnedEvent : Set (Execution Nat Nat Nat) :=
  {result | ∃ value, result.outcome = .returned value}

theorem mixed_outcome_event_masses :
    mixedExperiment.run () stoppedEvent = (2 : ℝ≥0∞)⁻¹ ∧
    mixedExperiment.run () returnedEvent = (2 : ℝ≥0∞)⁻¹ := by
  simp [mixed_experiment_complete, stoppedEvent, returnedEvent, stoppedRecord, returnedRecord]

theorem mixed_normalized : mixedExperiment.run () Set.univ = 1 := by
  simp [mixed_experiment_complete, ENNReal.inv_two_add_inv_two]

/-- This event simultaneously checks terminal status, reached state, and exact ordered log. -/
theorem mixed_stopped_record_retains_initial_mass :
    mixedExperiment.run () {stoppedRecord} = initialLaw {0} ∧
    mixedExperiment.run () {returnedRecord} = initialLaw {1} := by
  rw [mixed_stopped_record_mass, mixed_returned_record_mass,
    initialLaw_atom_masses.1, initialLaw_atom_masses.2]
  exact ⟨rfl, rfl⟩

/-- Removing the stopped atom produces only half the required total mass. -/
theorem dropping_stopped_mass_refuted :
    mixedExperiment.run () ≠ (2 : ℝ≥0∞)⁻¹ • Measure.dirac returnedRecord := by
  intro h
  have lost := congrArg (fun law : Measure (Execution Nat Nat Nat) ↦ law {stoppedRecord}) h
  rw [mixed_stopped_record_mass] at lost
  simp [stoppedRecord, returnedRecord] at lost

/-- Renormalizing the successful branch to probability one is a different complete law. -/
theorem successful_conditioning_refuted :
    mixedExperiment.run () ≠ Measure.dirac returnedRecord := by
  intro h
  have lost := congrArg (fun law : Measure (Execution Nat Nat Nat) ↦ law {stoppedRecord}) h
  rw [mixed_stopped_record_mass] at lost
  simp [stoppedRecord, returnedRecord] at lost

/-- No mass remains for any other complete execution, including altered state or events. -/
theorem mixed_no_other_record (result : Execution Nat Nat Nat)
    (hstopped : result ≠ stoppedRecord) (hreturned : result ≠ returnedRecord) :
    mixedExperiment.run () {result} = 0 := by
  simp [mixed_experiment_complete, Ne.symm hstopped, Ne.symm hreturned]

namespace InternalBindControl

open PFunctor

@[expose] def laterClient : Process signature Nat := .call .later fun _ ↦ .done 42

/-- Deliberately ordinary FreeM bind ignores the stopped Outcome supplied to its continuation. -/
@[expose] def ordinaryBind (reason : Stop) : FreeM (Internal.effects signature) (Outcome Nat) :=
  Internal.encode (.halt reason : Process signature Nat) >>= fun _ ↦ Internal.encode laterClient

/-- The wrong bind really runs the successor, changing outcome, state, and the prefixed log. -/
theorem ordinary_bind_runs_successor (reason : Stop) :
    ((ordinaryBind reason).liftM (Internal.monadHandler (m := Id) handler)) (3, [7, 8]) =
      (.returned 42, (103, [7, 8, 90, 91])) := by
  change ((Internal.encode laterClient).liftM
    (Internal.monadHandler (m := Id) handler)) (3, [7, 8]) = _
  rw [Internal.complete_execution]
  rfl

/-- Encoding the public bind retains the original stopped execution and never calls laterClient. -/
theorem encoded_process_bind_stops (reason : Stop) :
    ((Internal.encode ((.halt reason : Process signature Nat).bind (fun _ ↦ laterClient))).liftM
      (Internal.monadHandler (m := Id) handler)) (3, [7, 8]) =
      (.stopped reason, (3, [7, 8])) := rfl

/-- A certified counterexample to replacing failure-aware Process bind by ordinary FreeM bind. -/
theorem ordinary_bind_not_process_bind (reason : Stop) :
    ordinaryBind reason ≠
      Internal.encode ((.halt reason : Process signature Nat).bind (fun _ ↦ laterClient)) := by
  intro h
  have impossible := congrArg (fun program : FreeM (Internal.effects signature) (Outcome Nat) ↦
    ((program.liftM (Internal.monadHandler (m := Id) handler)) (3, [7, 8])).1) h
  rw [ordinary_bind_runs_successor, encoded_process_bind_stops] at impossible
  cases impossible

end InternalBindControl

end ProtocolProofExamples.ExecutionControls
