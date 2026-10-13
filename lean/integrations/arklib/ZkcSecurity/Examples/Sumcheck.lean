module

public import ZkcExamples.NativePrograms.Sumcheck.Program
public import ZkcSecurity.ArkLib.Sumcheck.Soundness

@[expose] public section

/-! ArkLib soundness of the actual exported two-round PIR verifier. -/

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace ZkcSecurity.Examples.Sumcheck
open Zkc.Protocols.Sumcheck.Common
open ZkcSecurity.ArkLib.Sumcheck
open scoped ENNReal
variable {F : Type} [Field F] [DecidableEq F] [Fintype F] [SampleableType F]

theorem soundness (coefficients : Coefficients F) (claim : F) (service : Nat)
    (prover : Strategy F) (falseClaim : claim ≠ (polynomial coefficients).booleanSum) :
    Pr{let result ← (execution ZkcExamples.NativePrograms.Sumcheck.verifier
      coefficients claim service prover)}[result.outcome = PIR.Outcome.returned (some true)] ≤
        4 / (Fintype.card F : ENNReal) :=
  ArkLib.Sumcheck.soundness ZkcExamples.NativePrograms.Sumcheck.contract
    coefficients claim service prover falseClaim

end ZkcSecurity.Examples.Sumcheck
