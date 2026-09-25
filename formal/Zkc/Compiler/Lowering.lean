import Zkc.Compiler.Plan

/-! Direct lowering preserves complete execution for every runtime binding.

The result concerns the actual typed plan produced by `lower`. A certificate
checker must separately bind an externally supplied candidate to that result.
-/

set_option autoImplicit false

namespace Zkc.Compiler

open Source

variable {language : Language} {interface : PIR.Signature} {S E A : Type}

def lower {Γ ty} : Program language Γ ty → Plan language Γ ty
  | .ret value => .yield value
  | .stop reason => .stop reason
  | .letOp op arguments next => .execute op arguments (lower next)
  | .branch condition yes no => .select condition (lower yes) (lower no)
  | .iterate count initial body next => .loop count initial (lower body) (lower next)

theorem executeLoop_eq_run (handler : PIR.Handler interface S E)
    (body : A → PIR.Proc interface A) (count : Nat) (value : A) (state : S) :
    executeLoop (fun value => (body value).run handler) count value state =
      (PIR.repeatN count body value).run handler state := by
  induction count generalizing value state with
  | zero => rfl
  | succ count ih =>
    simp only [executeLoop, PIR.repeatN, PIR.run_bind]
    congr 1
    funext next last
    exact ih next last

/-- No success assumption, chosen private input or handler law is needed. -/
theorem lower_correct (meaning : Interpretation language interface)
    (handler : PIR.Handler interface S E) {Γ ty} (program : Program language Γ ty)
    (env : Environment meaning.Value Γ) (state : S) :
    (lower program).run meaning handler env state = (program.denote meaning env).run handler state := by
  induction program generalizing state with
  | ret value => rfl
  | stop reason => rfl
  | letOp op arguments next ih =>
    simp only [lower, Plan.run, Program.denote, PIR.run_bind]
    congr 1
    funext value last
    exact ih (env.push value) last
  | branch condition yes no yesIH noIH =>
    simp only [lower, Plan.run, Program.denote]
    split <;> simp_all
  | iterate count initial body next bodyIH nextIH =>
    simp only [lower, Plan.run, Program.denote, PIR.run_bind]
    have bodySame :
        (fun value => (lower body).run meaning handler (env.push value)) =
        (fun value => (body.denote meaning (env.push value)).run handler) := by
      funext value last
      exact bodyIH (env.push value) last
    rw [bodySame, executeLoop_eq_run]
    congr 1
    funext value last
    exact nextIH (env.push value) last

end Zkc.Compiler
