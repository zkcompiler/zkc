import Zkc.Compiler.FactorOptimization.Conservative
import Zkc.Compiler.PlanSize

/-! Conservative factor planning preserves the source's structural node count.

The theorem covers all finite control trees, not just equal-transfer chains.
It does not bound descriptor bytes, fact lists, certificate size or checker time.
-/

set_option autoImplicit false

namespace Zkc.Compiler.FactorOptimization.Conservative

open Source Source.FactorQueries Modules.Factor Modules.FactorState

theorem direct_nodeCount {Γ ty} (source : Program language Γ ty) :
    (direct source).erase.nodeCount = source.erase.nodeCount := by
  induction source with
  | ret value => rfl
  | stop why => rfl
  | letOp op args next ih =>
      cases op <;> simp only [direct, Program.erase, RawProgram.nodeCount] <;>
        exact congrArg (1 + ·) ih
  | branch condition yes no ihYes ihNo =>
      simp only [direct, Program.erase, RawProgram.nodeCount, ihYes, ihNo]
  | iterate count initial body next ihBody ihNext =>
      simp only [direct, Program.erase, RawProgram.nodeCount, ihBody, ihNext]

theorem rewrite_nodeCount (summaries : Nat → Bool → Summary) (facts : List Fact)
    (available : List Nat) {Γ ty} (source : Program language Γ ty) :
    (rewrite summaries facts available source).erase.nodeCount = source.erase.nodeCount := by
  induction source generalizing facts available with
  | ret value => rfl
  | stop why => rfl
  | letOp op args next ih =>
      cases op <;> simp only [rewrite, Program.erase, RawProgram.nodeCount] <;>
        exact congrArg (1 + ·) (ih _ _)
  | branch condition yes no ihYes ihNo =>
      simp only [rewrite, Program.erase, RawProgram.nodeCount, ihYes, ihNo]
  | iterate count initial body next _ ihNext =>
      simp only [rewrite, Program.erase, RawProgram.nodeCount, ihNext]
      exact congrArg (fun n => 1 + n + next.erase.nodeCount) (direct_nodeCount body)

theorem candidate_nodeCount (summaries : Nat → Bool → Summary) {Γ ty}
    (source : Program language Γ ty) :
    (lower (rewrite summaries [] [] source)).erase.nodeCount = source.erase.nodeCount := by
  exact (lower_nodeCount (language := plannedLanguage) _).trans
    (rewrite_nodeCount summaries [] [] source)

end Zkc.Compiler.FactorOptimization.Conservative
