module

public import Zkc.Protocol.Semantics.Experiment

/-!
Mathematical view comparison. Operational simulation profiles additionally fix access and costs.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ProtocolProof

universe u v w

/-- A fixed simulator receives public inputs only. The property quantifies over every valid
private witness afterwards; it is not `∀ witness, ∃ simulator`. Observations must include the
view claimed by the request. This is statistical view security, not a computational reduction. -/
structure ViewComparison (Public : Type u) (Witness : Type v) (View : Type w)
    [MeasurableSpace View] where
  real : Experiment (Public × Witness) View
  simulated : Experiment Public View
  valid : Public → Witness → Prop
  error : Public → ℝ≥0∞

@[expose] def ViewComparison.Holds {P : Type u} {W : Type v} {V : Type w} [MeasurableSpace V]
    (request : ViewComparison P W V) : Prop :=
  ∀ publicInput witness, request.valid publicInput witness →
    ∀ event, MeasurableSet event →
      request.real.run (publicInput, witness) event ≤
        request.simulated.run publicInput event + request.error publicInput ∧
      request.simulated.run publicInput event ≤
        request.real.run (publicInput, witness) event + request.error publicInput

/-- Exact equality of permitted views establishes the statistical comparison at any error.
The same simulator is fixed outside the private-witness quantifier. -/
theorem ViewComparison.establish_exact {P : Type u} {W : Type v} {V : Type w}
    [MeasurableSpace V] (request : ViewComparison P W V)
    (equalViews : ∀ publicInput witness, request.valid publicInput witness →
      request.real.run (publicInput, witness) = request.simulated.run publicInput) :
    request.Holds := by
  intro publicInput witness hvalid event _
  rw [equalViews publicInput witness hvalid]
  exact ⟨le_add_right le_rfl, le_add_right le_rfl⟩


end ProtocolProof
