import ZkcArkLib.Sumcheck.OneRound.Kernel

/-! A downstream client of the actual ArkLib reduction.
The conditional sampling premise stays explicit at the call site.
-/

set_option autoImplicit false

namespace Client
open OracleComp ENNReal

theorem conditional_round_bound
    {F D S : Type} [Field F] [DecidableEq F] [Fintype D]
    (embed : D → F) (injective : Function.Injective embed)
    (coins : ProbComp S) (draw : S → ProbComp D)
    (choose : F → S → Zkc.Protocols.AlgebraicRounds.Early.Message F)
    (claim : F) (error : ℝ≥0∞)
    (cap : ∀ state ∈ support coins, ∀ d, Pr[= d | draw state] ≤ error)
    (falseClaim : claim ≠ 2) :
    Pr[= some () | ZkcArkLib.Sumcheck.OneRound.Kernel.experiment
      embed coins draw choose claim] ≤ 2 * error :=
  ZkcArkLib.Sumcheck.OneRound.Kernel.experiment_bound
    embed injective coins draw choose claim error cap falseClaim

end Client
