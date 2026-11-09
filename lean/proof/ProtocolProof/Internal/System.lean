module

public import ProtocolProof.Semantics.Experiment
public import ProtocolProof.Internal.Quantitative

/-!
# Fixed stateful execution environments

A `System` fixes the joint operation kernels and the initial law. Environments can contain
adversary implementations, public inputs and setup. The caller's typed interface determines
what an adversary can see; this privileged semantic state is not an adversary argument.
`experiment` uses the upstream interpreter and proves normalization once for every client.
-/

public section

open MeasureTheory PFunctor

universe uE uA uB uS uX

namespace ProtocolProof.Internal

variable (E : Type uE) (P : PFunctor.{uA, uB}) (S : Type uS)
  [∀ a, MeasurableSpace (P.B a)] [MeasurableSpace S]

/-- Normalized services with persistent shared state, fixed before a proof method is chosen. -/
structure System where
  operations : E → KernelHandler P S
  initial : E → Measure S
  operation_mass : ∀ environment operation state,
    operations environment operation state Set.univ = 1
  initial_probability : ∀ environment, IsProbabilityMeasure (initial environment)

variable {E P S} [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)]
  {X : Type uX} [MeasurableSpace X]

/-- Closing any client preserves all final state and every returned failure value. -/
@[expose] noncomputable def System.experiment (system : System E P S)
    (client : E → FreeM P X) : Experiment E (X × S) where
  run environment := (system.initial environment).bind
    (FreeM.runKernel (system.operations environment) (client environment))
  normalized environment := by
    let := system.initial_probability environment
    exact ⟨closed_mass_one (system.operations environment) (system.operation_mass environment)
      (client environment) (system.initial environment)⟩

end ProtocolProof.Internal
