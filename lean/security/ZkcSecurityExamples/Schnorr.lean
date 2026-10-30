module

public import ZkcExamples.NativePrograms.Schnorr
public import ZkcSecurity.Families.Sigma.Schnorr

@[expose] public section


/-! VCVio simulation security of the admitted native-export constructor data.
Source correspondence is the checked `ZkcExamples.NativePrograms.Schnorr.contract`.
The byte exporter and native arithmetic remain separately tested boundaries. -/

namespace ZkcSecurity.Examples.Schnorr
open ZkcSecurity.VCVio.Schnorr
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
  [SampleableType F]

theorem honest_verifier_zero_knowledge (base : G) (secret challenge : F)
    (service : Nat) (event : View F G → Prop) :
    Pr{let nonce ← $ᵗ F}[
      event (honestView ZkcExamples.NativePrograms.Schnorr.verifier base secret challenge nonce service)] =
    Pr{let response ← $ᵗ F}[
      event (simulatedView ZkcExamples.NativePrograms.Schnorr.verifier base (secret • base)
        challenge response service)] :=
  VCVio.Schnorr.honest_verifier_zero_knowledge ZkcExamples.NativePrograms.Schnorr.contract
    base secret challenge service event

end ZkcSecurity.Examples.Schnorr
