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
  have bound := prEvent_bind_le_prEvent_of_support (p.runM h s)
    (fun prior => prior.followM fun a state => (next a).runM h state)
    (returnedSatisfies residual) (returnedSatisfies accepted) (fun prior _ notResidual => by
      cases prior with | mk outcome state events =>
        cases outcome with
        | stopped why => simp [PIR.Execution.followM, returnedSatisfies]
        | returned a =>
          simp only [PIR.Execution.followM, prEvent_norm]
          exact prEvent_eq_zero_of_forall_mem_support ((next a).runM h state)
            (returnedSatisfies accepted) fun e he ha => notResidual (terminal a state e he ha))
  simpa only [mass, acceptance, PIR.runM_bind, prEvent_def, map_eq_bind_pure_comp,
    Function.comp_def] using bound

end ZkcSecurity.VCVio.Composition
