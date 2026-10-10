import Zkc.Modules.FactorScopes
import Zkc.Compiler.Analysis.FactorReuse

set_option autoImplicit false
namespace Zkc.Compiler.FactorScopes
open Zkc.Modules.Factor Zkc.Modules.FactorState Zkc.Modules.FactorBinding Zkc.Modules.Installation Zkc.Modules.Allocation Zkc.Modules.FactorScopes Zkc.Compiler.FactorReuse
variable {K : Type}

def choose (fs : Facts) (i : Nat) (q : Query) : Plan :=
  infer (fs i).toList q.point q

theorem chosen_value (fs : Facts) (ns : Names) (s : World K)
    (sound : Sound fs ns s) (i : Nat) (n : Namespace) (bound : ns i = some n) (q : Query) :
    runPlan s.values (query n q) (relocate n (choose fs i q)) =
      runQuery s.values (query n q) := by
  rw [relocated_plan,relocated_query]
  apply inferred_value
  intro f hf
  have hf' : fs i = some f := by simpa using hf
  exact local_means n s.values f (sound i f n hf' bound)

def compile (fs : Facts) : Source K → Code K
  | .stop => .stop
  | .demand i q next => .demand i q (choose fs i q) (compile fs next)
  | .bind r yes no => .bind r (compile (entered (Zkc.Source.FactorInputs.fact r.source r.handle)) yes) (compile fs no)
  | .clobber i h v next => .clobber i h v (compile emptyFacts next)
/-- Static source pass, dynamic name relocation, exact whole-result equality.
    No runtime invocation of infer, assumed Legal proof, or global freshness. -/
theorem compile_correct (quota cap : Nat) (src : Source K) (fs : Facts) (ns : Names)
    (p : Pool) (s : World K) (sound : Sound fs ns s) :
    run quota cap (compile fs src) ns p s = run quota cap (direct src) ns p s := by
  induction src generalizing fs ns p s with
  | stop => rfl
  | demand i q next ih =>
    simp only [compile,direct,run]
    cases hn : ns i with
    | none => rfl
    | some n =>
      simp only
      split
      · rw [ih fs ns p s sound,chosen_value fs ns s sound i n hn q]
        rfl
      · rfl
  | bind r yes no iy ino =>
    simp only [compile,direct,run]
    cases hn : (allocate quota cap p r s).allocated with
    | none =>
      simp only
      rw [ino fs ns _ _ (by simpa [allocated_none quota cap p r s hn] using sound)]
    | some n =>
      simp only
      rw [iy _ _ _ _ (entered_sound quota cap p r s ns n hn)]
  | clobber i h v next ih =>
    simp only [compile,direct,run]
    cases ns i with
    | none => rfl
    | some n => simp only; rw [ih emptyFacts ns p _ (empty_sound ns _)]

theorem closed_correct (quota cap : Nat) (src : Source K) (p : Pool) (s : World K) :
    run quota cap (compile emptyFacts src) emptyNames p s =
      run quota cap (direct src) emptyNames p s :=
  compile_correct quota cap src emptyFacts emptyNames p s (empty_sound _ _)

end Zkc.Compiler.FactorScopes
