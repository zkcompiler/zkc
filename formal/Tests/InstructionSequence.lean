import Zkc.Realization.InstructionSimulation
import Zkc.Realization.InstructionComposition

set_option autoImplicit false

namespace Tests.InstructionSequence
open Zkc.Realization.InstructionSequence

def step (stop : Bool) (state : Nat) : Step Nat Nat :=
  if stop then .halt .incomplete (state + 1) [state]
  else .next (state + 1) [state]

/-- A primitive's incomplete exit stops before the suffix. It is not falloff. -/
example : (source [true, false]).run (sourceHandler step) 7 =
    ⟨.returned .incomplete, 8, [7]⟩ := rfl

example : (source [false, true]).run (sourceHandler step) 7 =
    ⟨.returned .incomplete, 9, [7, 8]⟩ := rfl

example : (source ([] : List Bool)).run (sourceHandler step) 7 =
    ⟨.returned .incomplete, 7, []⟩ := rfl

/-- The no-incomplete-halt premise of `run_append` cannot be dropped. -/
example : run step ([true] ++ [false]) 7 ≠
    resume (run step [false]) (run step [true] 7) := by
  intro same
  have states := congrArg (fun out : Terminal Nat Nat => out.state) same
  exact (by decide : 8 ≠ 9) states

/-- Without that restriction, block resumption runs past the explicit halt and
retains the extra mutation and event. Flattening stops at the first primitive. -/
example : runBlocks step [[true], [false]] 7 = ⟨.incomplete, 9, [7, 8]⟩ := rfl

example : run step [[true], [false]].flatten 7 = ⟨.incomplete, 8, [7]⟩ := rfl

end Tests.InstructionSequence
