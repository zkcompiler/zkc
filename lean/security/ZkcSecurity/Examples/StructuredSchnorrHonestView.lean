module

public import ZkcExamples.Structured.SchnorrHonestProver
public import ZkcSecurity.VCVio.Schnorr

@[expose] public section

/-! Optional probability lift. The challenge is fixed outside nonce
sampling; no random native-provider correspondence or joint run is asserted. -/
namespace ZkcSecurity.Examples.StructuredSchnorrHonestView
open ZkcExamples.Structured
open SchnorrHonestProver

set_option autoImplicit false

variable {F G : Type} [Field F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Both public messages are taken from the actual prover's observed sends.
The outcome is that of the checked verifier under honest message delivery. -/
def sourceView (base : G) (secret challenge nonce : F) (nonceService challengeService : Nat) :
    VCVio.Schnorr.View F G :=
  let sent := messages base (secret • base) secret nonce challenge nonceService
  (sent.1, challenge, sent.2,
    (Zkc.Protocols.Schnorr.Common.run SchnorrInteractive.verifier
      base (secret • base) challengeService
      (strategy base (secret • base) secret nonce nonceService) challenge).outcome)

theorem sourceView_eq_honestView (base : G) (secret challenge nonce : F)
    (nonceService challengeService : Nat) :
    sourceView base secret challenge nonce nonceService challengeService =
      VCVio.Schnorr.honestView SchnorrInteractive.verifier
        base secret challenge nonce challengeService := by
  simp [sourceView, messages_eq, strategy_eq, VCVio.Schnorr.honestView]

theorem sourceView_transport (base : G) (secret challenge nonce : F)
    (nonceService challengeService : Nat) :
    sourceView base secret challenge nonce nonceService challengeService =
      VCVio.Schnorr.simulatedView SchnorrInteractive.verifier
        base (secret • base) challenge (nonce + challenge * secret) challengeService := by
  rw [sourceView_eq_honestView]
  exact VCVio.Schnorr.view_transport SchnorrInteractive.contract
    base secret challenge nonce challengeService

/-- Uniform nonce is the sole sampled input. The independently fixed challenge
and the two service handles are parameters, not assertions about provider laws.
The existing simulator depends on the public key, not on a witness argument. -/
theorem source_honest_verifier_zero_knowledge [SampleableType F]
    (base : G) (secret challenge : F) (nonceService challengeService : Nat)
    (event : VCVio.Schnorr.View F G → Prop) :
    Pr{let nonce ← $ᵗ F}[
      event (sourceView base secret challenge nonce nonceService challengeService)] =
    Pr{let response ← $ᵗ F}[
      event (VCVio.Schnorr.simulatedView SchnorrInteractive.verifier
        base (secret • base) challenge response challengeService)] := by
  simp_rw [sourceView_eq_honestView]
  exact VCVio.Schnorr.honest_verifier_zero_knowledge SchnorrInteractive.contract
    base secret challenge challengeService event

end ZkcSecurity.Examples.StructuredSchnorrHonestView
