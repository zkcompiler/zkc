import Zkc.Source.Size
import Zkc.Compiler.Lowering
import Zkc.Compiler.PlanEncoding

/-! Direct lowering preserves the structural size of the actual erased plan. -/

set_option autoImplicit false

namespace Zkc.Compiler

open Source

theorem lower_nodeCount {language : Language} [DecidableEq language.Ty]
    {Γ ty} (source : Program language Γ ty) :
    (lower source).erase.nodeCount = source.erase.nodeCount := by
  induction source with
  | ret value => rfl
  | stop why => rfl
  | letOp op args next ih => simpa only [lower, Plan.erase, Program.erase, RawProgram.nodeCount] using congrArg (1 + ·) ih
  | branch condition yes no ihYes ihNo =>
      simp only [lower, Plan.erase, Program.erase, RawProgram.nodeCount, ihYes, ihNo]
  | iterate count initial body next ihBody ihNext =>
      simp only [lower, Plan.erase, Program.erase, RawProgram.nodeCount, ihBody, ihNext]

end Zkc.Compiler
