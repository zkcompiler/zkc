import Zkc.Tests.IR.Core.Schnorr
import Zkc.Tools.Verification.CoreConstruction

/-! The verifier of the imported Schnorr package under the exact reading.

The program is the side meaning of the imported protocol for the verifier's role. The common
constructor walks its eleven instructions with the steps of the core language; the one
obligation that remains is the reached history and the returned decision, for every received
commitment, every reply of the challenge and every received response. No law of the model is
used: the statement holds for every model and every sample space. -/

set_option autoImplicit false
set_option experimental.vcgen true

open PIR Zkc.Source Zkc.Core Zkc.Core.Transcript Std.WP ProtocolProof
open ZkcSecurity.Obligations ZkcSecurity.Obligations.WeakestPrecondition
open Zkc.Tests.Core.Schnorr

namespace Zkc.Tests.Verification.Core.Schnorr

variable (M : Model) [Sampling M]

/-- The exact reading of the verifier's side. The verifier samples no secret, so the policy for
secrets does not matter. -/
noncomputable abbrev logic :
    WPMonad (Process (Effects M)) (Assert (Event M.Value)) (StopAssert (Event M.Value)) :=
  chargedMonad (interface .refused) exactEscape exactEscape_antitone

attribute [local instance] logic

/-- Every returning run of the verifier, for every commitment, challenge and response, appends
three events to the history: the received commitment, the occurrence of the challenge and the
received response. It returns the model's check of the response against the commitment and the
challenge, on the verifier's own copies of `g` and `y`. The challenge event records the
occurrence and not the reply. -/
theorem verifier_decides (g y : M.Value point) (start : List (Event M.Value)) :
    ⦃fun history => ⟨history = start⟩⦄
      schnorr.schnorr.meaning M verifier
        (.cons () (.cons () (.cons () (.cons g (.cons y .nil)))))
    ⦃fun out history => ⟨∃ commitment challenge response,
        history = start ++ [.received ⟨0, 1⟩ point commitment, .drawn ⟨0, 2⟩ uniform .nil,
          .received ⟨0, 3⟩ scalar response] ∧
        out.get .here = equal M (scale M g response) (add M commitment (scale M y challenge))⟩;
      estack⟨fun _ _ => ⟨True⟩⟩⦄ := by
  open_core_definition
  construct_region
  -- One obligation remains: the reached history and the returned decision, for every
  -- commitment, every decoded reply of the challenge and every response.
  rintro rfl commitment raw challenge decoded response
  exact ⟨commitment, challenge, response,
    by simp only [List.append_assoc, List.cons_append, List.nil_append]; rfl, rfl⟩

/-- Every accepting run returns from a transcript whose response passes the check: the decision
is the check itself. Exact evidence is charged evidence for every bounded judgment, whatever the
charge, when the sample spaces are sampled uniformly. -/
theorem verifier_decides_bounded
    [∀ (law : SamplingRow) (inputs : Values M.Value law.inputs),
      SampleableType (Sampling.Raw law inputs)]
    (g y : M.Value point) (charge : List (Event M.Value) → Event M.Value → ENNReal) :
    (interface (model := M) .refused).Charged (boundedEscape charge)
      (fun history out => ∃ commitment challenge response,
        history = [.received ⟨0, 1⟩ point commitment, .drawn ⟨0, 2⟩ uniform .nil,
          .received ⟨0, 3⟩ scalar response] ∧
        out.get .here = equal M (scale M g response) (add M commitment (scale M y challenge)))
      (schnorr.schnorr.meaning M verifier
        (.cons () (.cons () (.cons () (.cons g (.cons y .nil)))))) [] :=
  bounded_of_exact (interface .refused) charge
    (charged_of_triple (interface .refused) exactEscape exactEscape_antitone
      (verifier_decides M g y []) [] rfl)

end Zkc.Tests.Verification.Core.Schnorr

/-- info: 'Zkc.Tests.Verification.Core.Schnorr.verifier_decides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zkc.Tests.Verification.Core.Schnorr.verifier_decides

/--
info: 'Zkc.Tests.Verification.Core.Schnorr.verifier_decides_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Zkc.Tests.Verification.Core.Schnorr.verifier_decides_bounded
