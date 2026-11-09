module

public import ProtocolProof.Claims.Receipt
public import ProtocolProof.Claims.Diagnostics

/-!
# Closed property profiles and refused mutations

These complete finite experiments exercise fixed statements, access, extraction guarantees,
resource budgets and simulation. They test the framework's meanings, not a production protocol.
The service preserves a persistent call counter and returns the context's public bit. A real
simulation view either returns that bit or leaks a separate private witness.
-/

public section

open ProtocolProof PFunctor MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProtocolProofExamples.PropertyProfiles

local instance : MeasurableSpace (Option Bool) := ⊤

abbrev Interface : PFunctor := ⟨Unit, fun _ ↦ Bool⟩

@[expose] noncomputable def service : System Bool Interface Nat where
  operations context _ := Kernel.deterministic (fun counter ↦ (context, counter + 1))
    (measurable_of_countable _)
  initial _ := Measure.dirac 0
  operation_mass _ _ _ := by simp [Kernel.deterministic_apply]
  initial_probability _ := inferInstance

@[expose] def extractProgram (correct : Bool) (_ : Bool) : FreeM Interface (Option Bool) := do
  let answer ← FreeM.lift ()
  pure (some (if correct then answer else !answer))

@[expose] noncomputable def extractor (correct : Bool) :
    AccessExecution Bool Bool Interface Nat (Option Bool) where
  system := service
  publicInput := id
  algorithm := extractProgram correct

theorem extractor_law (correct context : Bool) :
    (extractor correct).experiment.run context =
      Measure.dirac (some (if correct then context else !context), 1) := by
  change (Measure.dirac 0).bind
    (FreeM.runKernel (service.operations context) (extractProgram correct context)) = _
  rw [Measure.dirac_bind (measurable_of_countable _)]
  change FreeM.runKernel (service.operations context)
    ((FreeM.lift (P := Interface) ()).bind fun answer ↦
      pure (some (if correct then answer else !answer))) 0 = _
  simp only [FreeM.runKernel_bind (P := Interface) (service.operations context),
    FreeM.runKernel_lift (P := Interface) (service.operations context),
    FreeM.runKernel_pure (P := Interface) (service.operations context)]
  simp only [service, Kernel.deterministic_apply]
  rw [Measure.dirac_bind (measurable_of_countable _)]

theorem extractor_calls (correct context : Bool) :
    (OperationCost.calls Interface).bound ((extractor correct).algorithm context) = 1 := by
  simp [extractor, extractProgram, OperationCost.bound, OperationCost.calls,
    OpSpec.charge]

@[expose] noncomputable def extraction (correct : Bool) (budget : ℝ≥0∞) :
    ExtractionRequest Bool Bool Interface Nat Bool Bool where
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
    ExtractionRequest Bool Bool Interface Nat Bool Bool :=
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
@[expose] def adaptiveCalls : FreeM Interface Unit :=
  (FreeM.lift (P := Interface) ()).bind fun answer ↦
    if answer then (FreeM.lift (P := Interface) ()).bind (fun _ ↦ pure ()) else pure ()

theorem adaptive_call_bound : (OperationCost.calls Interface).bound adaptiveCalls = 2 := by
  simp only [OperationCost.bound, OperationCost.calls, adaptiveCalls]
  rw [FreeM.wpFold_bind' (P := Interface)]
  simp [OpSpec.charge, iSup_bool_eq]
  norm_num

/-- A zero success function cannot have a useful extraction threshold. -/
theorem zero_guarantee_refused (guarantee : ExtractionGuarantee)
    (informative : guarantee.Informative) (zero : guarantee.lower 1 = 0) : False := by
  have positive := guarantee.positive 1 le_rfl informative
  rw [zero] at positive
  exact (lt_irrefl 0) positive

@[expose] def simulateProgram (_ : Bool) : FreeM Interface Bool := FreeM.lift ()

@[expose] noncomputable def simulator : AccessExecution Bool Bool Interface Nat Bool where
  system := service
  publicInput := id
  algorithm := simulateProgram

theorem simulator_law (context : Bool) :
    simulator.experiment.run context = Measure.dirac (context, 1) := by
  change (Measure.dirac 0).bind
    (FreeM.runKernel (service.operations context) (FreeM.lift (P := Interface) ())) = _
  rw [Measure.dirac_bind (measurable_of_countable _), FreeM.runKernel_lift (P := Interface)]
  rfl

@[expose] noncomputable def profile (leaks : Bool) :
    SimulationProfile Bool Bool Bool Bool Interface Nat where
  real := {
    run := fun input ↦ Measure.dirac (if leaks then input.2 else input.1)
    normalized := fun _ ↦ inferInstance }
  simulation := simulator
  valid _ _ := True

theorem simulated_law (leaks context : Bool) :
    (profile leaks).simulated.run context = Measure.dirac context := by
  change (simulator.experiment.run context).map Prod.fst = _
  rw [simulator_law]
  simp

theorem simulation_calls (leaks : Bool) :
    (profile leaks).CallsBounded (OperationCost.calls Interface) (fun _ ↦ 1) := by
  intro context _ _
  simp [profile, simulator, simulateProgram, OperationCost.bound, OperationCost.calls,
    OpSpec.charge]

@[expose] noncomputable def statistical (leaks : Bool) :
    StatisticalSimulationRequest Bool Bool Bool Bool Interface Nat where
  profile := profile leaks
  error _ := 0
  cost := OperationCost.calls Interface
  budget _ := 1

/-- One simulator is fixed before every private witness is quantified. -/
theorem statistical_established : (statistical false).Holds := by
  apply (statistical false).establish_exact
  · intro context witness _
    change Measure.dirac context = (profile false).simulated.run context
    exact (simulated_law false context).symm
  · exact simulation_calls false

theorem leaking_statistical_refused : ¬ (statistical true).Holds := by
  intro h
  have wrong := (h.1 false true trivial {true} MeasurableSet.of_discrete).1
  change Measure.dirac true {true} ≤ (profile true).simulated.run false {true} + 0 at wrong
  rw [simulated_law] at wrong
  simp at wrong

/-- An observer that returns exactly the observed bit. -/
@[expose] noncomputable def observers : ObserverFamily Bool Bool Unit where
  admitted _ _ := True
  kernel _ _ := Kernel.deterministic id measurable_id
  normalized _ _ _ := by simp [Kernel.deterministic_apply]

@[expose] noncomputable def distinguishing (leaks : Bool) :
    DistinguisherSimulationRequest Bool Bool Bool Bool Interface Nat Unit where
  profile := profile leaks
  observers := observers
  error _ := 0
  cost := OperationCost.calls Interface
  budget _ := 1

theorem distinguishing_established : (distinguishing false).Holds := by
  apply (distinguishing false).establish_exact
  · intro context witness _
    change Measure.dirac context = (profile false).simulated.run context
    exact (simulated_law false context).symm
  · exact simulation_calls false

theorem leaking_distinguishing_refused : ¬ (distinguishing true).Holds := by
  intro h
  have wrong := (h.1 false true trivial () trivial).1
  change (Measure.dirac true).bind (observers.kernel false ()) {true} ≤
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

end ProtocolProofExamples.PropertyProfiles
