module

public import ProtocolProof.Claims.View
public import ProtocolProof.Semantics.Access

/-!
# Request-fixed simulation profiles

The simulator has public input and typed service access; the real experiment additionally has
a private witness. Statistical and distinguisher-restricted observations have distinct meanings.
Weighted abstract calls do not certify host runtime or a polynomial-time distinguisher class.
-/

public section

open MeasureTheory ProbabilityTheory PFunctor
open scoped ENNReal

namespace ProtocolProof

universe uP uC uW uV uA uB uS uD

variable (Public : Type uP) (Context : Type uC) (Witness : Type uW) (View : Type uV)
  (Interface : PFunctor.{uA, uB}) (State : Type uS)
  [∀ op, MeasurableSpace (Interface.B op)] [MeasurableSpace State] [MeasurableSpace View]

/-- One simulator works for all valid witnesses of each context. The context can fix a verifier. -/
structure SimulationProfile where
  real : Experiment (Context × Witness) View
  simulation : AccessExecution Public Context Interface State View
  valid : Context → Witness → Prop

variable {Public Context Witness View Interface State}
  [∀ op, Countable (Interface.B op)] [∀ op, MeasurableSingletonClass (Interface.B op)]

namespace SimulationProfile

variable (profile : SimulationProfile Public Context Witness View Interface State)

/-- Only the specified returned view is observed; private handler state is not silently exposed. -/
@[expose] noncomputable def simulated : Experiment Context View :=
  profile.simulation.experiment.observe Observation.result

/-- The selected simulator's resource statement retains the same valid-context quantification. -/
@[expose] def CallsBounded (cost : OperationCost Interface) (budget : Context → ℝ≥0∞) : Prop :=
  ∀ context witness, profile.valid context witness →
    cost.bound (profile.simulation.algorithm (profile.simulation.publicInput context)) ≤
      budget context

end SimulationProfile

/-- Statistical simulation of the fixed view, together with a weighted-call bound. -/
structure StatisticalSimulationRequest (Public : Type uP) (Context : Type uC)
    (Witness : Type uW) (View : Type uV) (Interface : PFunctor.{uA, uB}) (State : Type uS)
    [∀ op, MeasurableSpace (Interface.B op)] [MeasurableSpace State] [MeasurableSpace View] where
  profile : SimulationProfile Public Context Witness View Interface State
  error : Context → ℝ≥0∞
  cost : OperationCost Interface
  budget : Context → ℝ≥0∞

namespace StatisticalSimulationRequest

variable (request : StatisticalSimulationRequest Public Context Witness View Interface State)

@[expose] noncomputable def comparison : ViewComparison Context Witness View where
  real := request.profile.real
  simulated := request.profile.simulated
  valid := request.profile.valid
  error := request.error

@[expose] def Holds : Prop :=
  request.comparison.Holds ∧ request.profile.CallsBounded request.cost request.budget

/-- An exact view law proves every statistical error budget, including perfect simulation. -/
theorem establish_exact
    (views : ∀ context witness, request.profile.valid context witness →
      request.profile.real.run (context, witness) = request.profile.simulated.run context)
    (resources : request.profile.CallsBounded request.cost request.budget) : request.Holds :=
  ⟨request.comparison.establish_exact views, resources⟩

end StatisticalSimulationRequest

/-- Normalized observer kernels and admitted tests; no efficiency assertion is implicit. -/
structure ObserverFamily (Context : Type uC) (View : Type uV) (Test : Type uD)
    [MeasurableSpace View] where
  admitted : Context → Test → Prop
  kernel : Context → Test → Kernel View Bool
  normalized : ∀ context test view, kernel context test view Set.univ = 1

/-- Distinguishing against the selected observer family, rather than all measurable events. -/
structure DistinguisherSimulationRequest (Public : Type uP) (Context : Type uC)
    (Witness : Type uW) (View : Type uV) (Interface : PFunctor.{uA, uB}) (State : Type uS)
    (Test : Type uD) [∀ op, MeasurableSpace (Interface.B op)]
    [MeasurableSpace State] [MeasurableSpace View] where
  profile : SimulationProfile Public Context Witness View Interface State
  observers : ObserverFamily Context View Test
  error : Context → ℝ≥0∞
  cost : OperationCost Interface
  budget : Context → ℝ≥0∞

namespace DistinguisherSimulationRequest

variable {Test : Type uD}
  (request : DistinguisherSimulationRequest Public Context Witness View Interface State Test)

@[expose] def ViewsIndistinguishable : Prop := ∀ context witness,
  request.profile.valid context witness → ∀ test, request.observers.admitted context test →
    let real := (request.profile.real.run (context, witness)).bind
      (request.observers.kernel context test)
    let simulated := (request.profile.simulated.run context).bind
      (request.observers.kernel context test)
    real {true} ≤ simulated {true} + request.error context ∧
      simulated {true} ≤ real {true} + request.error context

@[expose] def Holds : Prop := request.ViewsIndistinguishable ∧
  request.profile.CallsBounded request.cost request.budget

theorem establish_exact
    (views : ∀ context witness, request.profile.valid context witness →
      request.profile.real.run (context, witness) = request.profile.simulated.run context)
    (resources : request.profile.CallsBounded request.cost request.budget) : request.Holds := by
  refine ⟨?_, resources⟩
  intro context witness hvalid test _
  dsimp
  rw [views context witness hvalid]
  exact ⟨le_add_right le_rfl, le_add_right le_rfl⟩

end DistinguisherSimulationRequest

end ProtocolProof
