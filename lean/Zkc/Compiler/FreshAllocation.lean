import Zkc.Modules.FreshAllocation
import Zkc.Compiler.FactorScopes

set_option autoImplicit false
namespace Zkc.Compiler.FreshAllocation
open Zkc.Modules.Factor Zkc.Modules.FactorState Zkc.Modules.FactorBinding Zkc.Modules.Installation Zkc.Modules.Allocation Zkc.Modules.FactorScopes Zkc.Modules.FreshAllocation
open Zkc.Compiler.FactorScopes (choose chosen_value)
variable {K : Type}

def compile (fs : Facts) : Source K → Code K
  | .stop => .stop
  | .demand i q next => .demand i q (choose fs i q) (compile fs next)
  | .bind r yes no => .bind r (compile (enterKeep (Zkc.Source.FactorInputs.fact r.source r.handle) fs) yes) (compile fs no)
  | .clobber i h v next => .clobber i h v (compile emptyFacts next)

/-- Same interpreter and factor-plan inference; a stronger, established resource invariant
    retains outer facts across nested bindings. No per-instance pass theorem. -/
theorem compile_correct (quota cap : Nat) (src : Source K) (fs : Facts) (ns : Names)
    (p : Pool) (s : World K) (good : p.Good) (reg : Registered p ns) (sound : Sound fs ns s) :
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
      · rw [ih fs ns p s good reg sound,chosen_value fs ns s sound i n hn q]; rfl
      · rfl
  | bind r yes no iy ino =>
    simp only [compile,direct,run]
    have good' := allocation_good quota cap p r s good
    cases hn : (allocate quota cap p r s).allocated with
    | none =>
      simp only
      have reg' : Registered (allocate quota cap p r s).pool ns := by
        simpa [allocated_none_pool quota cap p r s hn] using reg
      have sound' : Sound fs ns (allocate quota cap p r s).returned.world := by
        simpa [allocated_none quota cap p r s hn] using sound
      rw [ino fs ns _ _ good' reg' sound']
    | some n =>
      simp only
      have reg' : Registered (allocate quota cap p r s).pool (push n ns) := by
        rw [allocated_some_pool quota cap p r s n hn,(allocated_some quota cap p r s n hn).1]
        exact registered_push p ns reg
      rw [iy _ _ _ _ good' reg' (kept_sound quota cap p r s fs ns good reg sound n hn)]
  | clobber i h v next ih =>
    simp only [compile,direct,run]
    cases ns i with
    | none => rfl
    | some n => simp only; rw [ih emptyFacts ns p _ good reg (empty_sound ns _)]

theorem closed_correct (quota cap : Nat) (src : Source K) (s : World K) :
    run quota cap (compile emptyFacts src) emptyNames empty s =
      run quota cap (direct src) emptyNames empty s := by
  apply compile_correct quota cap src emptyFacts emptyNames empty s empty_good
  · intro i n h; simp [emptyNames] at h
  · exact empty_sound _ _

end Zkc.Compiler.FreshAllocation
