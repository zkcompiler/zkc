module

public import Zkc.Protocol.Claims.Receipt
public import Zkc.Protocol.Claims.Diagnostics

/-!
# Closed property profiles and refused mutations

These complete finite experiments exercise fixed statements, access, extraction guarantees,
resource budgets and simulation. They test the framework's meanings, not a production protocol.
The service preserves a persistent call counter and returns the context's public bit. A real
simulation view either returns that bit or leaks a separate private witness.
-/

public section

open ProtocolProof PIR MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProtocolProofExamples.PropertyProfiles

local instance : MeasurableSpace (Option Bool) := ⊤

@[expose, reducible] def Interface : Signature := ⟨Unit, fun _ ↦ Bool⟩

@[expose] noncomputable def service : System Bool Interface Nat Bool where
  operations context _ := Kernel.deterministic
    (fun counter ↦ ⟨.returned context, counter + 1, [context]⟩)
    (measurable_of_countable _)
  initial _ := Measure.dirac 0
  operation_mass _ _ _ := by simp [Kernel.deterministic_apply]
  initial_probability _ := inferInstance

@[expose] def extractProgram (correct : Bool) (_ : Bool) : Process Interface (Option Bool) := do
  let answer ← Process.call () .done
  pure (some (if correct then answer else !answer))

@[expose] noncomputable def extractor (correct : Bool) :
    AccessExecution Bool Bool Interface Nat Bool (Option Bool) where
  system := service
  publicInput := id
  algorithm := extractProgram correct

theorem extractor_law (correct context : Bool) :
    (extractor correct).experiment.run context =
      Measure.dirac ⟨.returned (some (if correct then context else !context)), 1, [context]⟩ := by
  change (service.experiment (extractProgram correct)).run context = _
  rw [service.experiment_run]
  change (Measure.dirac 0).bind
    (service.run context (extractProgram correct context)) = _
  rw [Measure.dirac_bind (service.run context _).measurable]
  exact service.run_eq_dirac context
    (fun _ counter ↦ ⟨.returned context, counter + 1, [context]⟩)
    (fun _ _ ↦ rfl) _ 0

theorem extractor_calls (correct context : Bool) :
    (OperationCost.calls Interface).bound ((extractor correct).algorithm context) = 1 := by
  change (OperationCost.calls Interface).bound
    (.call () (fun answer ↦ .done (some (if correct then answer else !answer)))) = 1
  simp [OperationCost.bound, OperationCost.calls]

@[expose] noncomputable def extraction (correct : Bool) (budget : ℝ≥0∞) :
    ExtractionRequest Bool Bool Interface Nat Bool Bool Bool where
  acceptance := { run := fun _ ↦ Measure.dirac true, normalized := fun _ ↦ inferInstance }
  admissible _ := True
  execution := extractor correct
  statement := id
  problem := PromiseProblem.ofPredicate (fun _ ↦ True)
  witnesses := {
    relates := fun statement witness ↦ statement = witness
    implies_yes := fun _ _ _ ↦ trivial }
  measurable_success _ := MeasurableSet.of_discrete
  guarantee _ := ExtractionGuarantee.direct
  cost := OperationCost.calls Interface
  budget _ := budget

/-- The common success-request interface closes a genuine execution, including its call budget. -/
theorem extraction_established : (extraction true 1).Holds := by
  refine (extraction true 1).establish ?_ ?_
  · intro context _ _ _
    change _ ≤ (extractor true).experiment.run context _
    rw [extractor_law]
    simp [extraction, ExtractionRequest.successRequest, ExtractionGuarantee.direct,
      extractor, Measure.dirac_apply' _ MeasurableSet.of_discrete]
  · intro context _
    change (OperationCost.calls Interface).bound ((extractor true).algorithm context) ≤ 1
    rw [extractor_calls]

/-- Existence of a valid witness cannot rescue the request's wrong extraction algorithm. -/
theorem wrong_extractor_refused : ¬ (extraction false 1).Holds := by
  intro h
  have wrong := h.1 true trivial () trivial
  change _ ≤ (extractor false).experiment.run true _ at wrong
  rw [extractor_law] at wrong
  simp [extraction, ExtractionRequest.successRequest, ExtractionGuarantee.direct, extractor,
    Measure.dirac_apply' _ MeasurableSet.of_discrete] at wrong

/-- A successful extractor still fails a zero-call request if it performs one call. -/
theorem insufficient_budget_refused : ¬ (extraction true 0).Holds := by
  intro h
  have calls := h.2 true trivial
  change (OperationCost.calls Interface).bound ((extractor true).algorithm true) ≤ 0 at calls
  rw [extractor_calls] at calls
  exact (not_le_of_gt (by simp : (0 : ℝ≥0∞) < 1)) calls

/-- Changing the public target does not silently change the extractor's returned witness. -/
@[expose] noncomputable def wrongStatement :
    ExtractionRequest Bool Bool Interface Nat Bool Bool Bool :=
  { extraction true 1 with
    statement := fun context ↦ !context
    measurable_success := fun _ ↦ MeasurableSet.of_discrete }

theorem wrong_statement_refused : ¬ wrongStatement.Holds := by
  intro h
  have wrong := h.1 true trivial () trivial
  change _ ≤ (extractor true).experiment.run true _ at wrong
  rw [extractor_law] at wrong
  simp [wrongStatement, extraction, ExtractionRequest.successRequest,
    ExtractionGuarantee.direct, extractor,
    Measure.dirac_apply' _ MeasurableSet.of_discrete] at wrong

/-- The reply chooses whether the next call occurs. Cost covers both possible replies. -/
@[expose] def adaptiveCalls : Process Interface Unit :=
  (Process.call (I := Interface) () .done).bind fun answer ↦
    if answer then (Process.call (I := Interface) () .done).bind (fun _ ↦ pure ()) else pure ()

theorem adaptive_call_bound : (OperationCost.calls Interface).bound adaptiveCalls = 2 := by
  change 1 + (⨆ answer : Bool, (OperationCost.calls Interface).bound
    (if answer then Process.call () (fun _ ↦ .done ()) else .done ())) = 2
  rw [iSup_bool_eq]
  norm_num [OperationCost.bound, OperationCost.calls]

/-- A zero success function cannot have a useful extraction threshold. -/
theorem zero_guarantee_refused (guarantee : ExtractionGuarantee)
    (informative : guarantee.Informative) (zero : guarantee.lower 1 = 0) : False := by
  have positive := guarantee.positive 1 le_rfl informative
  rw [zero] at positive
  exact (lt_irrefl 0) positive

@[expose] def simulateProgram (_ : Bool) : Process Interface Bool := Process.call () .done

@[expose] noncomputable def simulator : AccessExecution Bool Bool Interface Nat Bool Bool where
  system := service
  publicInput := id
  algorithm := simulateProgram

theorem simulator_law (context : Bool) :
    simulator.experiment.run context = Measure.dirac ⟨.returned context, 1, [context]⟩ := by
  change (service.experiment simulateProgram).run context = _
  rw [service.experiment_run]
  change (Measure.dirac 0).bind
    (service.run context (Process.call () .done)) = _
  rw [Measure.dirac_bind (service.run context _).measurable]
  exact service.run_eq_dirac context
    (fun _ counter ↦ ⟨.returned context, counter + 1, [context]⟩)
    (fun _ _ ↦ rfl) _ 0

@[expose] noncomputable def profile (leaks : Bool) :
    SimulationProfile Bool Bool Bool Bool Interface Nat Bool where
  real := {
    run := fun input ↦ Measure.dirac (Outcome.returned (if leaks then input.2 else input.1))
    normalized := fun _ ↦ inferInstance }
  simulation := simulator
  valid _ _ := True

theorem simulated_law (leaks context : Bool) :
    (profile leaks).simulated.run context = Measure.dirac (Outcome.returned context) := by
  change (simulator.experiment.run context).map Execution.outcome = _
  rw [simulator_law]
  simp

theorem simulation_calls (leaks : Bool) :
    (profile leaks).CallsBounded (OperationCost.calls Interface) (fun _ ↦ 1) := by
  intro context _ _
  simp [profile, simulator, simulateProgram, OperationCost.bound, OperationCost.calls]

@[expose] noncomputable def statistical (leaks : Bool) :
    StatisticalSimulationRequest Bool Bool Bool Bool Interface Nat Bool where
  profile := profile leaks
  error _ := 0
  cost := OperationCost.calls Interface
  budget _ := 1

/-- One simulator is fixed before every private witness is quantified. -/
theorem statistical_established : (statistical false).Holds := by
  apply (statistical false).establish_exact
  · intro context witness _
    change Measure.dirac (Outcome.returned context) = (profile false).simulated.run context
    exact (simulated_law false context).symm
  · exact simulation_calls false

theorem leaking_statistical_refused : ¬ (statistical true).Holds := by
  intro h
  have wrong := (h.1 false true trivial {.returned true} MeasurableSet.of_discrete).1
  change Measure.dirac (Outcome.returned true) {.returned true} ≤
    (profile true).simulated.run false {.returned true} + 0 at wrong
  rw [simulated_law] at wrong
  simp at wrong

/-- An observer that returns exactly the observed bit. -/
@[expose] noncomputable def observers : ObserverFamily Bool (Outcome Bool) Unit where
  admitted _ _ := True
  kernel _ _ := Kernel.deterministic (fun outcome ↦ outcome = .returned true)
    (measurable_of_countable _)
  normalized _ _ _ := by simp only [Kernel.deterministic_apply, measure_univ]

@[expose] noncomputable def distinguishing (leaks : Bool) :
    DistinguisherSimulationRequest Bool Bool Bool Bool Interface Nat Bool Unit where
  profile := profile leaks
  observers := observers
  error _ := 0
  cost := OperationCost.calls Interface
  budget _ := 1

theorem distinguishing_established : (distinguishing false).Holds := by
  apply (distinguishing false).establish_exact
  · intro context witness _
    change Measure.dirac (Outcome.returned context) = (profile false).simulated.run context
    exact (simulated_law false context).symm
  · exact simulation_calls false

theorem leaking_distinguishing_refused : ¬ (distinguishing true).Holds := by
  intro h
  have wrong := (h.1 false true trivial () trivial).1
  change (Measure.dirac (Outcome.returned true)).bind (observers.kernel false ()) {true} ≤
    ((profile true).simulated.run false).bind (observers.kernel false ()) {true} + 0 at wrong
  rw [simulated_law] at wrong
  rw [Measure.dirac_bind (observers.kernel false ()).measurable,
    Measure.dirac_bind (observers.kernel false ()).measurable] at wrong
  simp [observers, Kernel.deterministic_apply] at wrong

/-- Root receipts retain their property kind and the complete request. -/
theorem extraction_receipt : Receipt (.extraction (I := Interface) (extraction true 1)) :=
  ⟨extraction_established⟩

theorem statistical_receipt : Receipt (.statisticalSimulation (statistical false)) :=
  ⟨statistical_established⟩

theorem distinguishing_receipt : Receipt (.distinguisherSimulation (distinguishing false)) :=
  ⟨distinguishing_established⟩

/-- A receipt for a different algorithm cannot establish this algorithm's request. -/
theorem wrong_extractor_receipt_refused :
    ¬ Receipt (.extraction (I := Interface) (extraction false 1)) :=
  fun receipt ↦ wrong_extractor_refused receipt.proof

/-- The full execution law cannot be replaced by a law that resets reached state. -/
theorem extractor_state_reset_refused :
    (extractor true).experiment.run true ≠
      Measure.dirac ⟨.returned (some true), 0, [true]⟩ := by
  rw [extractor_law]
  intro wrong
  have observed := congrArg
    (fun law : Measure (Execution Nat Bool (Option Bool)) ↦
      law {⟨.returned (some true), 1, [true]⟩}) wrong
  simp at observed

/-- Retaining the witness and state does not authorize erasing reached events. -/
theorem extractor_event_erasure_refused :
    (extractor true).experiment.run true ≠
      Measure.dirac ⟨.returned (some true), 1, []⟩ := by
  rw [extractor_law]
  intro wrong
  have observed := congrArg
    (fun law : Measure (Execution Nat Bool (Option Bool)) ↦
      law {⟨.returned (some true), 1, [true]⟩}) wrong
  simp at observed

/-- Every terminal process stop has zero remaining abstract-call cost. -/
theorem stopped_call_bound (reason : Stop) :
    (OperationCost.calls Interface).bound
      ((Process.halt reason).bind fun _ : Bool ↦ adaptiveCalls) = 0 := by
  simp

/-- A stopped service still updates persistent state and emits its reached event. -/
@[expose] noncomputable def stoppingService (reason : Stop) : System Bool Interface Nat Bool where
  operations context _ := Kernel.deterministic
    (fun counter ↦ ⟨.stopped reason, counter + 1, [context]⟩) (measurable_of_countable _)
  initial _ := Measure.dirac 0
  operation_mass _ _ _ := by simp [Kernel.deterministic_apply]
  initial_probability _ := inferInstance

@[expose] noncomputable def stoppingAccess (reason : Stop) :
    AccessExecution Bool Bool Interface Nat Bool Bool where
  system := stoppingService reason
  publicInput := id
  algorithm _ := .call () (fun _ ↦ .call () .done)

/-- A stopped first service call preserves its record and prevents the second call. -/
theorem handler_stop_law (reason : Stop) (context : Bool) :
    (stoppingAccess reason).experiment.run context =
      Measure.dirac ⟨.stopped reason, 1, [context]⟩ := by
  change ((stoppingService reason).experiment
    (fun _ ↦ .call () (fun _ ↦ .call () .done))).run context = _
  rw [(stoppingService reason).experiment_run]
  change (Measure.dirac 0).bind
    ((stoppingService reason).run context (.call () (fun _ ↦ .call () .done))) = _
  rw [Measure.dirac_bind ((stoppingService reason).run context _).measurable]
  exact (stoppingService reason).run_eq_dirac context
    (fun _ counter ↦ ⟨.stopped reason, counter + 1, [context]⟩)
    (fun _ _ ↦ rfl) _ 0

/-- Stopping is a complete normalized execution, not an absent extraction result. -/
@[expose] noncomputable def stoppedExtraction (reason : Stop) :
    ExtractionRequest Bool Bool Interface Nat Bool Bool Bool :=
  { extraction true 0 with
    execution := { extractor true with algorithm := fun _ ↦ .halt reason }
    measurable_success := fun _ ↦ MeasurableSet.of_discrete }

theorem stopped_extractor_law (reason : Stop) (context : Bool) :
    (stoppedExtraction reason).execution.experiment.run context =
      Measure.dirac ⟨.stopped reason, 0, []⟩ := by
  change (service.experiment (fun _ ↦ .halt reason)).run context = _
  rw [service.experiment_run]
  change (Measure.dirac 0).bind (service.run context (.halt reason)) = _
  rw [Measure.dirac_bind (service.run context _).measurable]
  simp [System.run, Kernel.comap_apply]

/-- Reject, abort, exhaustion, incompleteness and refusal all fail positive extraction. -/
theorem stopped_extractor_refused (reason : Stop) : ¬ (stoppedExtraction reason).Holds := by
  intro h
  have wrong := h.1 true trivial () trivial
  change _ ≤ (stoppedExtraction reason).execution.experiment.run true _ at wrong
  rw [stopped_extractor_law] at wrong
  simp [stoppedExtraction, extraction, ExtractionRequest.successRequest,
    ExtractionGuarantee.direct, Measure.dirac_apply' _ MeasurableSet.of_discrete] at wrong

/-- The real view explicitly records a stop while the selected simulator returns a bit. -/
@[expose] noncomputable def stoppedReal (reason : Stop) :
    StatisticalSimulationRequest Bool Bool Bool Bool Interface Nat Bool :=
  { statistical false with
    profile := { profile false with real := {
      run := fun _ ↦ Measure.dirac (Outcome.stopped reason : Outcome Bool)
      normalized := fun _ ↦ inferInstance } } }

/-- Every stopped real view is distinguishable from an always-returning simulation. -/
theorem stopped_real_refused (reason : Stop) : ¬ (stoppedReal reason).Holds := by
  intro h
  have wrong := (h.1 false true trivial {.stopped reason} MeasurableSet.of_discrete).1
  change Measure.dirac (Outcome.stopped reason : Outcome Bool) {.stopped reason} ≤
    (profile false).simulated.run false {.stopped reason} + 0 at wrong
  rw [simulated_law] at wrong
  simp at wrong

/-- Observing a halted simulator retains its exact reason with mass one. -/
@[expose] noncomputable def stoppedProfile (reason : Stop) :
    SimulationProfile Bool Bool Bool Bool Interface Nat Bool :=
  { profile false with
    simulation := { simulator with algorithm := fun _ ↦ .halt reason }
    real := {
      run := fun _ ↦ Measure.dirac (Outcome.stopped reason : Outcome Bool)
      normalized := fun _ ↦ inferInstance } }

theorem stopped_simulated_law (reason : Stop) (context : Bool) :
    (stoppedProfile reason).simulated.run context =
      Measure.dirac (Outcome.stopped reason : Outcome Bool) := by
  change ((service.experiment (fun _ ↦ .halt reason)).run context).map
    (Execution.outcome : Execution Nat Bool Bool → Outcome Bool) = _
  rw [service.experiment_run]
  change ((Measure.dirac 0).bind (service.run context (.halt reason))).map
    Execution.outcome = _
  rw [Measure.dirac_bind (service.run context _).measurable]
  simp [System.run, Kernel.comap_apply]

/-- Different terminal reasons cannot be identified by a perfect statistical simulation. -/
theorem different_stops_refused :
    ¬ (ViewComparison.mk (stoppedProfile .abort).real
      (stoppedProfile .refused).simulated (fun _ _ ↦ True) (fun _ ↦ 0)).Holds := by
  intro h
  have wrong := (h false true trivial {.stopped .abort} MeasurableSet.of_discrete).1
  change Measure.dirac (Outcome.stopped .abort : Outcome Bool) {.stopped .abort} ≤
    (stoppedProfile .refused).simulated.run false {.stopped .abort} + 0 at wrong
  rw [stopped_simulated_law] at wrong
  simp at wrong

end ProtocolProofExamples.PropertyProfiles
