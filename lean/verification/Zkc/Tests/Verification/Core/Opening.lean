import Zkc.Tests.IR.Core.Opening
import Zkc.Tools.Verification.CoreConstruction

/-! The setup and the verifier of the imported opening package under the exact reading.

The side holds two of the three roles. The setup samples a secret, sends the reference string
to the prover and gives the verification key to the verifier inside the side; the verifier
receives the commitment, draws the point, receives the evaluation and the proof, and checks
with the pairing. The secret is answered as a query (`Secrets.fresh`), so the triple speaks of
every value of the secret.

The statement characterizes every run: the reached history and the returned decision, for every
secret and every received value, and no stop with the reason `incomplete`, the stop of a side
whose roles disagree on a control value. It is not a soundness statement. The prover's messages
are received after the reference string, which is computed from the secret, has been sent: the
triple quantifies over every commitment, evaluation and proof, including ones chosen with
knowledge of the reference string or of the secret itself, and says only what the verifier then
decides. That a prover who sees the reference string alone cannot open a commitment to two
values is a computational property of the group and the pairing, which no reading here states:
the charged reading bounds events of the verifier's own coins, and the strategies of the
interactive experiment see the raw answer of the secret. -/

set_option autoImplicit false
set_option experimental.vcgen true

open PIR Zkc.Source Zkc.Core Zkc.Core.Transcript Std.WP ProtocolProof
open ZkcSecurity.Obligations ZkcSecurity.Obligations.WeakestPrecondition
open Zkc.Tests.Core.Opening

namespace Zkc.Tests.Verification.Core.Opening

variable (M : Model) [Sampling M]

/-- The exact reading of the side of the setup and the verifier, with the setup's secret
answered as a query. -/
noncomputable abbrev logic :
    WPMonad (Process (Effects M)) (Assert (Event M.Value)) (StopAssert (Event M.Value)) :=
  chargedMonad (interface .fresh) exactEscape exactEscape_antitone

attribute [local instance] logic

/-- Every returning run of the setup and the verifier appends six events to the history: the
occurrence of the secret, the sent reference string for that secret, the received commitment,
the occurrence of the point, the received evaluation and the received proof. It returns the
point, the evaluation and the model's pairing check of the commitment, the evaluation and the
proof against the key that the setup computed from the same secret. The side never stops with
the reason `incomplete`. -/
theorem setup_verifier_decides (start : List (Event M.Value)) :
    ⦃fun history => ⟨history = start⟩⦄
      opening.opening.meaning M setupAndVerifier (.cons () .nil)
    ⦃fun out history => ⟨∃ secret commitment point evaluation proof,
        history = start ++ [.sampled ⟨0, 0⟩ uniform .nil,
          .sent ⟨0, 1⟩ points (referenceString M secret),
          .received ⟨0, 3⟩ first commitment, .drawn ⟨0, 4⟩ uniform .nil,
          .received ⟨0, 5⟩ scalar evaluation, .received ⟨0, 6⟩ first proof] ∧
        out = .cons point (.cons evaluation (.cons
          (accepts M (scale₂ M (generator₂ M) secret) commitment point evaluation proof) .nil))⟩;
      estack⟨fun reason _ => ⟨reason ≠ .incomplete⟩⟩⦄ := by
  open_core_definition
  construct_region
  -- One obligation remains: the reached history and the returned values, for every reading of
  -- the secret and of the point and for every received commitment, evaluation and proof.
  rintro rfl rawSecret secret readSecret commitment rawPoint point readPoint evaluation proof
  exact ⟨secret, commitment, point, evaluation, proof,
    by simp only [List.append_assoc, List.cons_append, List.nil_append]; rfl, rfl⟩

end Zkc.Tests.Verification.Core.Opening

#print axioms Zkc.Tests.Verification.Core.Opening.setup_verifier_decides
