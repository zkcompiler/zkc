module

public import ZkcSecurity.VCVio.SigmaAnd
public import VCVio.Schemes.Schnorr.SigmaProtocol

@[expose] public section

/-! VCVio's Schnorr Σ-protocol in the shared-challenge composition.

Upstream proves Schnorr's perfect HVZK with a simulator that draws the
challenge first and then a uniform response; that simulator is the
challenge-first form of the per-challenge simulator below, so special HVZK
follows over a finite field without a new simulation argument. The composition
of two Schnorr instances, one base each, then has perfect completeness, special
soundness and perfect HVZK. -/

open OracleComp

namespace ZkcSecurity.VCVio.SigmaAndSchnorr
open ZkcSecurity.VCVio.SigmaAnd

variable (F : Type) [Field F] [SampleableType F]
  (G : Type) [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]

/-- Given the challenge, draw a uniform response and solve for the commitment. -/
def simulate (base key : G) (challenge : F) : ProbComp (G × F) := do
  let response ← $ᵗ F
  pure (response • base - challenge • key, response)

omit [SampleableType G] [DecidableEq G] in
theorem challengeFirst_simulate (base : G) :
    challengeFirst (simulate F G base) = _root_.Schnorr.simTranscript F G base := by
  funext key
  simp [challengeFirst, simulate, _root_.Schnorr.simTranscript, monad_norm]

theorem specialHVZK [Fintype F] (base : G) :
    SpecialHVZK (_root_.Schnorr.sigma F G base).toChallengeVerifyProtocol (simulate F G base) := by
  apply SpecialHVZK.of_perfectHVZK
  rw [challengeFirst_simulate]
  exact _root_.Schnorr.sigma_hvzk F G base

/-- Two Schnorr statements, one per base, with independent witnesses and one
shared challenge. -/
abbrev sigma (firstBase secondBase : G) :=
  and (_root_.Schnorr.sigma F G firstBase) (_root_.Schnorr.sigma F G secondBase)

theorem complete (firstBase secondBase : G) : (sigma F G firstBase secondBase).PerfectlyComplete :=
  perfectlyComplete _ _ (_root_.Schnorr.sigma_complete F G firstBase)
    (_root_.Schnorr.sigma_complete F G secondBase)

theorem speciallySound (firstBase secondBase : G) : (sigma F G firstBase secondBase).SpeciallySound :=
  SigmaAnd.speciallySound _ _ (_root_.Schnorr.sigma_speciallySound F G firstBase)
    (_root_.Schnorr.sigma_speciallySound F G secondBase)

theorem hvzk [Fintype F] (firstBase secondBase : G) :
    (sigma F G firstBase secondBase).PerfectHVZK (challengeFirst
      (simulateAnd (simulate F G firstBase) (simulate F G secondBase))) :=
  (SigmaAnd.specialHVZK _ _ (specialHVZK F G firstBase) (specialHVZK F G secondBase)).perfectHVZK

end ZkcSecurity.VCVio.SigmaAndSchnorr
