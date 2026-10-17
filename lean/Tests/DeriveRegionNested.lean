import Zkc.Source.DeriveRegion
import Tests.RegionDerivation
import Tests.DerivationCounter

-- The counter is intentionally outside tactic backtracking; serialize these tests.
set_option Elab.async false
set_option maxHeartbeats 200000

namespace Tests.DeriveRegionNested
open Lean Elab Tactic Zkc.Source PIR Tests.RegionDerivation
open Tests.DerivationCounter

private def nested : Nat → Region dialect [Ty.scalar, Ty.scalar, Ty.scalar] []
  | 0 => .letOp .check
      (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))
      .nil (.ret .nil)
  | depth + 1 => .bind (nested depth) (.ret .nil)

private theorem check_reverse (a b c : Nat) (commutes : a + b = b + a) :
    source.OperationLaw lower .check (.cons a (.cons b (.cons c .nil))) .nil
      (.done (.cons (c == b + a) .nil)) := by
  apply RegionMeaning.OperationLaw.ofTranslation translation
  change @Eq (Proc interface (Values Value [Ty.boolean]))
    (.done (.cons (c == a + b) .nil)) (.done (.cons (c == b + a) .nil))
  rw [commutes]

/-- Twelve nested binds retain the open arithmetic premise and visit the leaf once. -/
theorem nested_open (a b c : Nat) :
    Region.Derivation source lower (nested 12) (Values.cons a (.cons b (.cons c .nil))).get
      (.done .nil) := by
  run_tac do solverCalls.set 0
  derive_region using (
    run_tac do solverCalls.modify (· + 1)
    apply check_reverse)
  run_tac do
    let calls ← solverCalls.get
    unless calls == 1 do throwError "nested bind revisited the local solver: {calls}"
    logInfo m!"NESTED-BIND-SOLVER-CALLS {calls} depth=12"
  exact Nat.add_comm _ _

/-- The same open leaf is visited once inside a universally quantified callback. -/
theorem nested_callback_open :
    ∃ targets, Regions.Derivation source lower (.cons (nested 12) .nil) targets := by
  refine ⟨?targets, ?proof⟩
  case proof =>
    run_tac do solverCalls.set 0
    derive_region using (
      run_tac do solverCalls.modify (· + 1)
      apply check_reverse)
    run_tac do
      let calls ← solverCalls.get
      unless calls == 1 do throwError "nested callback revisited the local solver: {calls}"
      logInfo m!"NESTED-CALLBACK-SOLVER-CALLS {calls} depth=12"
    exact Nat.add_comm _ _

end Tests.DeriveRegionNested
