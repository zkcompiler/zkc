import Zkc.Protocols.Sumcheck.Optimization
import Zkc.Protocols.Sumcheck.Framed
import Zkc.Source.Arithmetic
import Zkc.Compiler.Checking

/-! A downstream client of source security and checked evaluation.
This file builds in a separate Lake package, without importing library tests.
-/

set_option autoImplicit false

namespace Client
open Zkc.Protocols.Sumcheck Zkc.Polynomial

variable {F S : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The client can state its own source-bound claim at any dimension. -/
theorem optimized_false_claim
    (send : S → Zkc.Protocols.AlgebraicRounds.Message F × S)
    (react : S → F → S) {n : Nat} (polynomial : Quadratic F n)
    (claim : F) (state : S) (falseClaim : claim ≠ polynomial.booleanSum) :
    Optimization.acceptance send react polynomial claim state ≤
      (2 * (n : ℚ)) / Fintype.card F :=
  Optimization.soundness send react polynomial claim state falseClaim

/-- Honest completeness uses the same optimized verifier and original object. -/
theorem optimized_honest {n : Nat} (polynomial : Quadratic F n) :
    Optimization.acceptance Security.honestSend Security.honestReact
      polynomial polynomial.booleanSum ⟨n, polynomial⟩ = 1 :=
  Optimization.perfect_completeness polynomial

namespace CheckedInvocation
open Zkc.Source Zkc.Compiler Zkc.Source.Arithmetic

/-- Use the library vocabulary with a client-owned, stateful invocation. -/
abbrev interface : PIR.Signature := ⟨Nat, fun _ => Nat⟩
abbrev meaning : Interpretation language interface :=
  interpretation (fun value : Nat => .call value .done)

def handler : PIR.Handler interface Nat Nat := fun value state =>
  ⟨if state = 0 then .returned value else .stopped .abort, state + 1, [value]⟩

/-- The second invocation stops after recording its attempted argument. -/
theorem invocation_failure (value state : Nat) (failed : state ≠ 0) :
    ((meaning.operation .invoke (.cons value .nil)).run handler state) =
      ⟨.stopped .abort, state + 1, [value]⟩ := by
  simp [meaning, interpretation, handler, PIR.Proc.run, PIR.Execution.follow, failed]

/-- An effectful prefix, pure arithmetic, and two further invocations. -/
def source : Program language [.scalar] .scalar :=
  .letOp .invoke (.cons .here .nil)
    (.letOp .add (.cons .here (.cons .here .nil))
      (.letOp .invoke (.cons .here .nil)
        (.letOp .invoke (.cons .here .nil) (.ret .here))))

/-- Independently supplied serialized candidate, checked against the retained source. -/
def candidate : RawProgram Ty Op :=
  .letOp .invoke [0] (.letOp .add [0, 0]
    (.letOp .invoke [0] (.letOp .invoke [0] (.ret 0))))

def checked : CheckedPlan source candidate :=
  (checkDirect source candidate).get (by decide)

example : (checkDirect source (.ret 0)).isNone = true := by decide

/-- Consume the checker's proof to retain the actual failure, state, and event prefix.
The third invocation cannot execute, even though its operand is well formed. -/
theorem candidate_stops_after_second_call (value : Nat) :
    checked.plan.run meaning handler (Values.cons value .nil).get 0 =
      ⟨.stopped .abort, 2, [value, value + value]⟩ := by
  rw [checked.correct meaning handler]
  rfl

end CheckedInvocation

end Client
