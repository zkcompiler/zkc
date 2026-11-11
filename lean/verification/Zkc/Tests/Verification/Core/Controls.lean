import Zkc.Tests.IR.Core.Schnorr
import Zkc.Tools.Verification.CoreConstruction

/-! Controls for the readings of a side: the two policies for secrets, a side that sends, and a
side of two roles. -/

set_option autoImplicit false
set_option experimental.vcgen true

open PIR Zkc.Source Zkc.Core Zkc.Core.Transcript Std.WP ProtocolProof
open ZkcSecurity.Obligations ZkcSecurity.Obligations.WeakestPrecondition
open Zkc.Tests.Core.Schnorr

namespace Zkc.Tests.Verification.Core.Controls

variable (M : Model) [Sampling M]

section Fresh

/-- The exact reading with secrets answered as queries. -/
noncomputable abbrev fresh :
    WPMonad (Process (Effects M)) (Assert (Event M.Value)) (StopAssert (Event M.Value)) :=
  chargedMonad (interface .fresh) exactEscape exactEscape_antitone

attribute [local instance] fresh

/-- The prover's side: the sample of the nonce, the sent commitment, the challenge, which the
verifier draws outside the side and announces to the prover alone, and the sent response. The
side never stops. The statement holds for every value of the nonce; it does not say that the
nonce is hidden from anyone. -/
theorem prover_transcript (g y : M.Value point) (x : M.Value scalar)
    (start : List (Event M.Value)) :
    ⦃fun history => ⟨history = start⟩⦄
      schnorr.schnorr.meaning M prover
        (.cons g (.cons y (.cons x (.cons () (.cons () .nil)))))
    ⦃fun _ history => ⟨∃ nonce challenge,
        history = start ++ [.sampled ⟨0, 0⟩ uniform .nil, .sent ⟨0, 1⟩ point (scale M g nonce),
          .received ⟨0, 2⟩ scalar challenge,
          .sent ⟨0, 3⟩ scalar (fieldAdd M nonce (mul M challenge x))]⟩;
      estack⟨fun _ _ => ⟨False⟩⟩⦄ := by
  open_core_definition
  construct_region
  rintro rfl raw nonce read challenge
  exact ⟨nonce, challenge,
    by simp only [List.append_assoc, List.cons_append, List.nil_append]; rfl⟩

/-- Both roles together: the nonce and the challenge are the only events, the exchanged
messages are internal, and the decision is the check on the honest response. -/
theorem honest_decision (g y : M.Value point) (x : M.Value scalar) (g' y' : M.Value point)
    (start : List (Event M.Value)) :
    ⦃fun history => ⟨history = start⟩⦄
      schnorr.schnorr.meaning M both
        (.cons g (.cons y (.cons x (.cons g' (.cons y' .nil)))))
    ⦃fun out history => ⟨∃ nonce challenge,
        history = start ++ [.sampled ⟨0, 0⟩ uniform .nil, .drawn ⟨0, 2⟩ uniform .nil] ∧
        out.get .here = equal M (scale M g' (fieldAdd M nonce (mul M challenge x)))
          (add M (scale M g nonce) (scale M y' challenge))⟩;
      estack⟨fun _ _ => ⟨False⟩⟩⦄ := by
  open_core_definition
  construct_region
  rintro rfl rawNonce nonce readNonce rawChallenge challenge readChallenge
  exact ⟨nonce, challenge,
    by simp only [List.append_assoc, List.cons_append, List.nil_append]; rfl, rfl⟩

end Fresh

section Refused

/-- The exact reading with secrets refused. -/
noncomputable abbrev refused :
    WPMonad (Process (Effects M)) (Assert (Event M.Value)) (StopAssert (Event M.Value)) :=
  chargedMonad (interface .refused) exactEscape exactEscape_antitone

attribute [local instance] refused

/-- With secrets refused, the prover's side refuses at the sample of its nonce, and every
reading accepts the refusal: even a triple with false postconditions holds. Over this interface
a triple says nothing about a side after it samples. -/
theorem prover_refused (g y : M.Value point) (x : M.Value scalar) :
    ⦃fun _ => ⟨True⟩⦄
      schnorr.schnorr.meaning M prover
        (.cons g (.cons y (.cons x (.cons () (.cons () .nil)))))
    ⦃fun _ _ => ⟨False⟩; estack⟨fun _ _ => ⟨False⟩⟩⦄ := by
  open_core_definition
  construct_region

end Refused

end Zkc.Tests.Verification.Core.Controls

#print axioms Zkc.Tests.Verification.Core.Controls.prover_transcript
#print axioms Zkc.Tests.Verification.Core.Controls.honest_decision
#print axioms Zkc.Tests.Verification.Core.Controls.prover_refused
