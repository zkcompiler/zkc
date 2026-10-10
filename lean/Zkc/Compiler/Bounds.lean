import Zkc.Compiler.Checking
import Zkc.Source.Bounds
import Zkc.Semantics.ExecutionPath

/-! Transfer a public source bound to actual calls of the checked logical plan.
No phase-analysis certificate is needed for this bound. Each source operation
must have its stated uniform interface-call bound for every typed argument list.
-/

set_option autoImplicit false

namespace Zkc.Compiler.CheckedPlan

open Source

theorem calls_bounded {language : Language} [DecidableEq language.Ty]
    {Γ : List language.Ty} {ty : language.Ty}
    {source : Program language Γ ty} {candidate : RawProgram language.Ty language.Op}
    (checked : CheckedPlan source candidate) {interface : PIR.Signature}
    (meaning : Interpretation language interface) (interaction : PIR.Interaction interface)
    (operationBound : language.Op → Nat)
    (operations : ∀ op args, PIR.Within (operationBound op) (meaning.operation op args))
    {S E : Type} (handler : PIR.Handler interface S E)
    (env : Environment meaning.Value Γ) (phase : interaction.Phase) (state : S) :
    ((checked.plan.run meaning (PIR.ExecutionPath.handler interaction handler)
      env (phase, state)).events.filterMap (fun
        | .inl call => some call | .inr _ => none)).length ≤ source.callBound operationBound := by
  rw [checked.correct]
  refine Nat.le_trans (Nat.le_of_eq ?_) (PIR.ExecutionPath.calls_bounded interaction handler (source.denote meaning env)
    (source.callBound operationBound) phase state
    (source.denote_within meaning operationBound operations env))
  congr 2
  funext event
  cases event <;> rfl

end Zkc.Compiler.CheckedPlan
