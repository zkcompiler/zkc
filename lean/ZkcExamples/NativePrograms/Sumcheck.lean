module

public import ZkcExamples.NativePrograms.Sumcheck.Program

public import Zkc.Protocols.Sumcheck.Common

@[expose] public section

/-! Security of the actual imported two-round verifier under fresh uniform coins. -/

set_option autoImplicit false

namespace ZkcExamples.NativePrograms.Sumcheck

open Zkc.Source Zkc.Source.Common Zkc.Source.Common.Native
open Zkc.Protocols.AlgebraicRounds (Message)
open Zkc.Polynomial Zkc.Probability

variable {F : Type} [Field F] [DecidableEq F]

export Zkc.Protocols.Sumcheck.Common
  (Strategy strategy strategy_surjective received transcriptHandler handler_receive_field handler_query
    handler_send honestStrategy honest_strategy)

abbrev run := Zkc.Protocols.Sumcheck.Common.run (verifier (F := F))

theorem run_outcome (coefficients : Coefficients F) (claim : F) (service : Nat)
    (prover : Strategy F) (first second : F) :
    (run coefficients claim service prover first second).outcome =
      if wireBoundary prover.first = claim then
        if wireBoundary (prover.second first) = wireEvaluate prover.first first then
          .returned (some (decide (wireEvaluate (prover.second first) second =
            evaluate coefficients first second)))
        else .stopped .reject
      else .stopped .reject := by
  exact contract.run_outcome coefficients claim service prover first second

/-- The accepting event comes from the actual imported execution, including
both early rejection branches and the final false result. -/
theorem accepted_iff (coefficients : Coefficients F) (claim : F) (service : Nat)
    (prover : Strategy F) (first second : F) :
    (run coefficients claim service prover first second).outcome = .returned (some true) ↔
      Zkc.Protocols.Sumcheck.verify (polynomial coefficients) claim (strategy prover)
        (first, second, ()) = true := by
  exact contract.accepted_iff coefficients claim service prover first second

theorem completeness (coefficients : Coefficients F) (service : Nat) (first second : F) :
    (run coefficients (polynomial coefficients).booleanSum service
      (honestStrategy coefficients) first second).outcome = .returned (some true) := by
  exact contract.completeness coefficients service first second


end ZkcExamples.NativePrograms.Sumcheck
