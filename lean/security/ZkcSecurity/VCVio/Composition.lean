module

public import ZkcSecurity.VCVio.Execution
public import VCVio.EvalDist.ProbabilityBounds

@[expose] public section

namespace ZkcSecurity.VCVio.Composition

open OracleComp ZkcSecurity.VCVio.Execution

/-- Acceptance after a call is bounded by the callee's residual event when
every accepting continuation implies that event. The local implication holds
at every residual state, including states changed by an effectful prefix.
Stops on either side are nonaccepting; no losslessness premise is needed. -/
theorem acceptance_bind_le {I : PIR.Signature} {S E A B : Type}
    (h : PIR.MonadHandler ProbComp I S E) (p : PIR.Process I A)
    (next : A → PIR.Process I B) (s : S)
    (accepted : B → Prop) (residual : A → Prop)
    (terminal : ∀ a state, ∀ e ∈ support ((next a).runM h state),
      returnedSatisfies accepted e → residual a) :
    mass (acceptance h (p.bind next) s accepted) ≤
      mass (acceptance h p s residual) := by
  unfold acceptance mass
  rw [PIR.runM_bind]
  apply prEvent_bind_le_prEvent_of_support
  intro prior _ notResidual
  cases prior with | mk outcome state events =>
    cases outcome with
    | stopped why => simp [PIR.Execution.followM, returnedSatisfies]
    | returned a =>
      simp only [PIR.Execution.followM, bind_assoc, pure_bind]
      exact OracleComp.prEvent_eq_zero_of_forall_mem_support ((next a).runM h state)
        (returnedSatisfies accepted) fun e he ha => notResidual (terminal a state e he ha)

end ZkcSecurity.VCVio.Composition
