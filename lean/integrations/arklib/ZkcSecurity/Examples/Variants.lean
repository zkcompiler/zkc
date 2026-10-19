module

public import ZkcExamples.NativePrograms.SchnorrVariants
public import ZkcExamples.NativePrograms.SumcheckVariants
public import ZkcSecurity.VCVio.Schnorr
public import ZkcSecurity.ArkLib.Sumcheck.Soundness

@[expose] public section

namespace ZkcSecurity.Examples.Variants
open ZkcExamples.NativePrograms Zkc.Verification

/-- Three different source forms reuse the same independent simulation consumer. -/
theorem schnorr {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G]
    [Module F G] [DecidableEq G] [SampleableType F]
    (form : SchnorrVariants.Form) (base : G) (secret challenge : F) (service : Nat)
    (event : VCVio.Schnorr.View F G → Prop) :
    (VCVio.Schnorr.simulationProperty base secret challenge service event).conclusion
      (SchnorrVariants.verifier form) :=
  (VCVio.Schnorr.simulationConsumer Schnorr.wiring base secret challenge service event).prove
    _ (SchnorrVariants.contract form) trivial

/-- Original, helper and Horner forms reuse ArkLib's same soundness consumer. -/
theorem sumcheck {F : Type} [Field F] [DecidableEq F] [Fintype F] [SampleableType F]
    (form : SumcheckVariants.Form) (coefficients : Zkc.Protocols.Sumcheck.Common.Coefficients F)
    (claim : F) (service : Nat) (provers : ProbComp (Zkc.Protocols.Sumcheck.Common.Strategy F))
    (falseClaim : claim ≠ (Zkc.Protocols.Sumcheck.Common.polynomial coefficients).booleanSum) :
    (ArkLib.Sumcheck.soundnessProperty coefficients claim service provers).conclusion
      (SumcheckVariants.verifier form) :=
  (ArkLib.Sumcheck.soundnessConsumer Sumcheck.wiring coefficients claim service provers).prove
    _ (SumcheckVariants.contract form) falseClaim

end ZkcSecurity.Examples.Variants
