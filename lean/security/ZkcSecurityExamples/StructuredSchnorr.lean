module

public import ZkcExamples.Structured.SchnorrVariants
public import ZkcSecurity.Families.Sigma.Schnorr

@[expose] public section

/-! The existing abstract security consumer applied to the actual original-stage
structured Interactive subject. The source process equation supplies its
contract; the exporter, native curve implementation, random provider and authored
relation binding are separate boundaries. -/
namespace ZkcSecurity.Examples.StructuredSchnorr
open ZkcSecurity.VCVio.Schnorr
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
  [SampleableType F]

theorem honest_verifier_zero_knowledge (base : G) (secret challenge : F)
    (service : Nat) (event : View F G → Prop) :
    Pr{let nonce ← $ᵗ F}[
      event (honestView ZkcExamples.Structured.SchnorrInteractive.verifier
        base secret challenge nonce service)] =
    Pr{let response ← $ᵗ F}[
      event (simulatedView ZkcExamples.Structured.SchnorrInteractive.verifier
        base (secret • base) challenge response service)] :=
  VCVio.Schnorr.honest_verifier_zero_knowledge
    ZkcExamples.Structured.SchnorrInteractive.contract base secret challenge service event

/-- The same consumer applies to every admitted source form with the contract. -/
theorem variants_honest_verifier_zero_knowledge
    (form : ZkcExamples.Structured.SchnorrVariants.Form)
    (base : G) (secret challenge : F) (service : Nat) (event : View F G → Prop) :
    Pr{let nonce ← $ᵗ F}[
      event (honestView (ZkcExamples.Structured.SchnorrVariants.verifier form)
        base secret challenge nonce service)] =
    Pr{let response ← $ᵗ F}[
      event (simulatedView (ZkcExamples.Structured.SchnorrVariants.verifier form)
        base (secret • base) challenge response service)] :=
  VCVio.Schnorr.honest_verifier_zero_knowledge
    (ZkcExamples.Structured.SchnorrVariants.contract form) base secret challenge service event

end ZkcSecurity.Examples.StructuredSchnorr
