import Zkc.Source.Definitions
import Zkc.Protocols.Sumcheck.Execution

/-! The maintained Sumcheck verifier source as a shared, typed definition.
The call transports its exact source meaning and uses the same staged interactive
execution. It adds no commitment or security premise.
-/

set_option autoImplicit false

namespace Zkc.Protocols.Sumcheck.Definitions

open Zkc.Source
open Zkc.Protocols.Sumcheck.Source

abbrev signature : DefinitionSignature Ty := ⟨[.accumulator, .polynomial], .boolean⟩

def definitions (count : Nat) : Definitions language [signature] :=
  Definitions.snoc (language := language) .nil signature
    ((program count).toRegion.withDefinitions [])

def invocation :
    Region (language.withDefinitions [signature]) signature.arguments signature.result :=
  .letOp (.call .here) (.cons .here (.cons (.there .here) .nil)) (.ret .here)

/-- The call executes the stored source, including its loop, checks and terminal. -/
theorem invocation_denote {F : Type} {n : Nat} [CommSemiring F] [DecidableEq F]
    (count : Nat) (env : Environment (Value F n) signature.arguments) :
    invocation.denote ((definitions count).meaning meaning) env =
      (program count).denote meaning env := by
  change
    ((((program count).toRegion.withDefinitions []).denote
      ((Definitions.nil (language := language)).meaning meaning)
      (Values.cons (env .here) (Values.cons (env (.there .here)) Values.nil)).get).bind
      PIR.Proc.done) = _
  rw [PIR.Proc.bind_done, Region.denote_withDefinitions, Program.denote_toRegion]
  congr 1
  funext ty value
  cases value with
  | here => rfl
  | there value => cases value with
    | here => rfl
    | there value => cases value

/-- No honest-message or successful-return assumption is required. -/
theorem invocation_execution {F : Type} {n : Nat} [CommSemiring F] [DecidableEq F]
    {S E : Type} (handler : PIR.Handler (Zkc.Protocols.AlgebraicRounds.interface F) S E)
    (count : Nat) (env : Environment (Value F n) signature.arguments) (state : S) :
    (invocation.denote ((definitions count).meaning meaning) env).run handler state =
      ((program count).denote meaning env).run handler state := by
  rw [invocation_denote]

/-- Execute the stored verifier source with the existing interactive handler. -/
def run {F S : Type} [CommSemiring F] [DecidableEq F]
    (send : S → AlgebraicRounds.Message F × S) (react : S → F → S)
    {n : Nat} (polynomial : Zkc.Polynomial.Quadratic F n)
    (claim : F) (prover : S) (coins : List F) :
    PIR.Execution (S × List F) (AlgebraicRounds.Construction.Event F) Bool :=
  (invocation.denote ((definitions n).meaning meaning)
    (Values.cons (ty := Ty.accumulator) ⟨claim, []⟩
      (Values.cons (ty := Ty.polynomial) polynomial .nil)).get).run
    (Execution.handler send react) (prover, coins)

/-- Shared-definition execution is the same complete run as the maintained staged source. -/
theorem run_eq_source {F S : Type} [CommSemiring F] [DecidableEq F]
    (send : S → AlgebraicRounds.Message F × S) (react : S → F → S)
    {n : Nat} (polynomial : Zkc.Polynomial.Quadratic F n)
    (claim : F) (prover : S) (coins : List F) :
    run send react polynomial claim prover coins =
      Execution.run send react polynomial claim prover coins := by
  rw [run, invocation_execution, Execution.run, Program.denote_translate,
    PIR.Proc.run_interpret, ← Execution.handler_fresh]

end Zkc.Protocols.Sumcheck.Definitions
