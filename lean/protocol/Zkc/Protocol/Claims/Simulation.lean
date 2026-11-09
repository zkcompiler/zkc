module

public import Zkc.Protocol.Claims.View
public import Zkc.Protocol.Semantics.Access

/-!
# Request-fixed simulation profiles

The simulator has public input and typed service access; the real experiment additionally has
a private witness. Statistical and distinguisher-restricted observations have distinct meanings.
Weighted abstract calls do not certify host runtime or a polynomial-time distinguisher class.
-/

public section

open MeasureTheory ProbabilityTheory PIR
open scoped ENNReal

namespace ProtocolProof

universe uC uV uD

variable (Public Context Witness View : Type) (Interface : Signature) (State Event : Type)
  [∀ op, MeasurableSpace (Interface.Reply op)]
  [MeasurableSpace State] [MeasurableSpace Event] [MeasurableSpace View]

/-- One simulator works for all valid witnesses of each context. The context can fix a verifier. -/
structure SimulationProfile where
  real : Experiment (Context × Witness) (Outcome View)
  simulation : AccessExecution Public Context Interface State Event View
  valid : Context → Witness → Prop

variable {Public Context Witness View Interface State Event}
  [∀ op, Countable (Interface.Reply op)] [∀ op, MeasurableSingletonClass (Interface.Reply op)]

namespace SimulationProfile

variable (profile : SimulationProfile Public Context Witness View Interface State Event)

/-- The view includes every stop; the real experiment must likewise return `Outcome View`. -/
@[expose] noncomputable def simulated : Experiment Context (Outcome View) :=
  profile.simulation.experiment.observe Observation.outcome

/-- The selected simulator's resource statement retains the same valid-context quantification. -/
@[expose] def CallsBounded (cost : OperationCost Interface) (budget : Context → ℝ≥0∞) : Prop :=
  ∀ context witness, profile.valid context witness →
    cost.bound (profile.simulation.algorithm (profile.simulation.publicInput context)) ≤
      budget context

end SimulationProfile

/-- Statistical simulation of the fixed view, together with a weighted-call bound. -/
structure StatisticalSimulationRequest (Public Context Witness View : Type)
    (Interface : Signature) (State Event : Type)
    [∀ op, MeasurableSpace (Interface.Reply op)]
    [MeasurableSpace State] [MeasurableSpace Event] [MeasurableSpace View] where
  profile : SimulationProfile Public Context Witness View Interface State Event
  error : Context → ℝ≥0∞
  cost : OperationCost Interface
  budget : Context → ℝ≥0∞

namespace StatisticalSimulationRequest

variable (request : StatisticalSimulationRequest Public Context Witness View Interface State Event)

@[expose] noncomputable def comparison : ViewComparison Context Witness (Outcome View) where
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
structure DistinguisherSimulationRequest (Public Context Witness View : Type)
    (Interface : Signature) (State Event : Type)
    (Test : Type) [∀ op, MeasurableSpace (Interface.Reply op)]
      [MeasurableSpace State] [MeasurableSpace Event] [MeasurableSpace View] where
  profile : SimulationProfile Public Context Witness View Interface State Event
  observers : ObserverFamily Context (Outcome View) Test
  error : Context → ℝ≥0∞
  cost : OperationCost Interface
  budget : Context → ℝ≥0∞

namespace DistinguisherSimulationRequest

variable {Test : Type}
  (request : DistinguisherSimulationRequest Public Context Witness View Interface State Event Test)

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
