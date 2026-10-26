import ZkcExamples.Construction.SchnorrAndProof
import ZkcExamples.Construction.ChaumPedersenProof
import Mathlib.Algebra.Field.ZMod

/-! Non-vacuity controls for the compiled Sigma proof Entries.

`SchnorrAndProof.compiled_transform` and `ChaumPedersenProof.compiled_transform`
equate the compiled verifier's actual Domain execution with the Fiat–Shamir transform of
the original validator. These controls evaluate the canonical compiled side in the kernel
over `ZMod 3`, with group elements in `ZMod 3` as well and a constant challenge,
so the equations are not about a verifier that always stops: an honest proof is
accepted exactly at the challenge it answers, a wrong response is rejected, and
a truncated proof stops with a refusal. -/

namespace Tests.SigmaProofControls
open Zkc.Construction ZkcExamples.Construction

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

abbrev Scalar := ZMod 3

def point (value : Scalar) : Payload Scalar Scalar := .group "bls12-381.g1" value

def scalar (value : Scalar) : Payload Scalar Scalar := .field "bls12-381.fr" value

namespace SchnorrAnd
open ZkcExamples.Construction.SchnorrAndProof

/-- The left side of `SchnorrAndProof.compiled_transform` with a constant
challenge: the compiled verifier's actual Domain execution on the public inputs, read
through the acceptance output. -/
def compiled (challenge : Scalar) (firstBase firstPoint secondBase secondPoint : Scalar)
    (proof : Proof Scalar Scalar) : PIR.Outcome (Option Bool) × Proof Scalar Scalar :=
  compiledVerifier (F := Scalar) (G := Scalar) (m := Id) (fun _ => challenge)
    firstBase firstPoint secondBase secondPoint [] proof

/-- The honest proof for the statements `2 = 2 • 1` and `2 = 1 • 2` at the
challenge `2`: nonces `1` and `2` give the commitments `1` and `1` and the
responses `2` and `1`. -/
def honest : Proof Scalar Scalar := [point 1, point 1, scalar 2, scalar 1]

theorem honest_accepted (challenge : Scalar) :
    (compiled challenge 1 2 2 2 honest).1 = .returned (some (decide (challenge = 2))) := by
  revert challenge
  decide +kernel

theorem wrong_response_rejected :
    (compiled 2 1 2 2 2 [point 1, point 1, scalar 2, scalar 0]).1 = .returned (some false) := by
  decide +kernel

theorem truncated_refused (challenge : Scalar) :
    (compiled challenge 1 2 2 2 [point 1, point 1, scalar 2]).1 = .stopped .refused := by
  revert challenge
  decide +kernel

end SchnorrAnd

namespace ChaumPedersen
open ZkcExamples.Construction.ChaumPedersenProof

/-- The left side of `ChaumPedersenProof.compiled_transform` with a constant
challenge. -/
def compiled (challenge : Scalar) (firstBase firstPoint secondBase secondPoint : Scalar)
    (proof : Proof Scalar Scalar) : PIR.Outcome (Option Bool) × Proof Scalar Scalar :=
  compiledVerifier (F := Scalar) (G := Scalar) (m := Id) (fun _ => challenge)
    firstBase firstPoint secondBase secondPoint [] proof

/-- The honest proof for the shared witness `2` of `2 = 2 • 1` and `1 = 2 • 2`
at the challenge `2`: the nonce `1` gives the commitments `1` and `2` and the
response `2`. -/
def honest : Proof Scalar Scalar := [point 1, point 2, scalar 2]

theorem honest_accepted (challenge : Scalar) :
    (compiled challenge 1 2 2 1 honest).1 = .returned (some (decide (challenge = 2))) := by
  revert challenge
  decide +kernel

theorem wrong_response_rejected :
    (compiled 2 1 2 2 1 [point 1, point 2, scalar 0]).1 = .returned (some false) := by
  decide +kernel

theorem truncated_refused (challenge : Scalar) :
    (compiled challenge 1 2 2 1 [point 1, point 2]).1 = .stopped .refused := by
  revert challenge
  decide +kernel

end ChaumPedersen

end Tests.SigmaProofControls
