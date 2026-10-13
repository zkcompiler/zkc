module

public import ZkcSecurity.ArkLib.Sumcheck.FiatShamir
public import ZkcExamples.NativePrograms.SumcheckVariants

@[expose] public section

set_option autoImplicit false

/-! Canonical-restoration consumers for actual common-source imports in three
source forms. These subjects are the imported interactive verifier programs;
this is not a theorem identifying the native constructed Merlin participant. -/

namespace ZkcSecurity.Examples.SumcheckFiatShamir

open OracleComp OracleSpec
open Zkc.Protocols.Sumcheck.Common
open ZkcSecurity.ArkLib.Sumcheck.FiatShamir
open ZkcExamples.NativePrograms.SumcheckVariants (Form verifier contract)

variable {F : Type} [Field F] [DecidableEq F] [Fintype F] [SampleableType F]
variable {Salt : Type} [DecidableEq Salt]

/-- Helper factoring and Horner arithmetic inherit the same adversarial bound. -/
theorem sourceForms_soundness (form : Form) (service : Nat) (adversary : Adversary F Salt)
    (Q : Nat) (queryBound : IsTotalQueryBound adversary Q) :
    Pr{let result ← (simulateQ randomOracle
      (programGame (verifier form) service adversary)).run' ∅}[
      result.2.outcome = PIR.Outcome.returned (some true) ∧
        result.1.claim ≠ (polynomial result.1.coefficients).booleanSum] ≤
          (Q + 2 : ENNReal) * (2 / (Fintype.card F : ENNReal)) :=
  program_soundness (contract form) service adversary Q queryBound

end ZkcSecurity.Examples.SumcheckFiatShamir
