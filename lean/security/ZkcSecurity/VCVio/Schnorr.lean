module

public import Zkc.Protocols.Schnorr.Common
public import Zkc.Specification
public import VCVio.OracleComp.Constructions.SampleableType.Measure

@[expose] public section

/-! Perfect simulation of the imported verifier's public one-session view.

The experiment fixes an honest verifier challenge independently of the prover
nonce. The simulator knows the public key, not the witness. The resulting view
includes the actual verifier outcome. This is honest-verifier zero knowledge;
it makes no malicious-verifier, concurrency or Fiat–Shamir claim.
-/

namespace ZkcSecurity.VCVio.Schnorr
open Zkc.Protocols.Schnorr.Common

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G] [DecidableEq G]

abbrev View (F G : Type) := G × F × F × PIR.Outcome (Option Bool)

def honestView (program : Verifier F G) (base : G) (secret challenge nonce : F)
    (service : Nat) : View F G :=
  (nonce • base, challenge, nonce + challenge * secret,
    (run program base (secret • base) service
      ⟨nonce • base, fun c => nonce + c * secret⟩ challenge).outcome)

def simulatedView (program : Verifier F G) (base key : G) (challenge response : F)
    (service : Nat) : View F G :=
  (response • base - challenge • key, challenge, response,
    (run program base key service
      ⟨response • base - challenge • key, fun _ => response⟩ challenge).outcome)

theorem simulator_accepts {wiring : Wiring} {program : Verifier F G}
    (certificate : VerifierContract wiring program) (base key : G)
    (challenge response : F) (service : Nat) :
    (run program base key service
      ⟨response • base - challenge • key, fun _ => response⟩ challenge).outcome =
      .returned (some true) := by
  rw [certificate.accepted_iff]
  exact (sub_add_cancel _ _).symm

theorem view_transport {wiring : Wiring} {program : Verifier F G}
    (certificate : VerifierContract wiring program) (base : G)
    (secret challenge nonce : F) (service : Nat) :
    honestView program base secret challenge nonce service =
      simulatedView program base (secret • base) challenge (nonce + challenge * secret) service := by
  unfold honestView simulatedView
  rw [certificate.perfect_completeness, simulator_accepts certificate]
  simp only [add_smul, mul_smul, add_sub_cancel_right]

variable [SampleableType F]

/-- Every event on the public transcript and actual verifier result has exactly
its simulator probability. The quantification is over every admitted verifier
implementing the contract, not over a single handwritten protocol. -/
theorem honest_verifier_zero_knowledge {wiring : Wiring} {program : Verifier F G}
    (certificate : VerifierContract wiring program) (base : G)
    (secret challenge : F) (service : Nat) (event : View F G → Prop) :
    Pr{let nonce ← $ᵗ F}[event (honestView program base secret challenge nonce service)] =
    Pr{let response ← $ᵗ F}[
      event (simulatedView program base (secret • base) challenge response service)] := by
  simp_rw [view_transport certificate]
  exact SampleableType.prEvent_uniformSample_comp_of_bijective
    (AddGroup.addRight_bijective (challenge * secret))
    (fun response => event (simulatedView program base (secret • base) challenge response service))

/-- Explicit experiment selection, reusable across source certificates. -/
noncomputable def simulationProperty (base : G) (secret challenge : F)
    (service : Nat) (event : View F G → Prop) : Zkc.Verification.Property (Verifier F G) where
  assumptions _ := True
  conclusion program :=
    Pr{let nonce ← $ᵗ F}[event (honestView program base secret challenge nonce service)] =
    Pr{let response ← $ᵗ F}[
      event (simulatedView program base (secret • base) challenge response service)]

theorem simulationConsumer (wiring : Wiring) (base : G) (secret challenge : F)
    (service : Nat) (event : View F G → Prop) :
    Zkc.Verification.Consumer (VerifierContract wiring)
      (simulationProperty base secret challenge service event) :=
  ⟨fun _ certificate _ =>
    honest_verifier_zero_knowledge certificate base secret challenge service event⟩

end ZkcSecurity.VCVio.Schnorr
