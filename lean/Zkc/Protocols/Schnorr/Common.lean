module

public import Zkc.Source.Common.Scalar
public import Zkc.Semantics.ExactRefinement
public import Zkc.Protocols.Schnorr

@[expose] public section

/-! Reusable common-source verifier contract for the Schnorr equation.
The wiring names actual effect sites and the challenge service. A certificate
is an open-process equality, not an assumption of security. Probability,
rewinding, honest-prover source correspondence and native arithmetic are separate.
-/
set_option autoImplicit false

namespace Zkc.Protocols.Schnorr.Common
open Zkc.Source Zkc.Source.Common Zkc.Source.Common.Native

structure Wiring where
  prover : Nat
  groupDomain : String
  fieldDomain : String
  commitmentSite : String
  challengeSite : String
  deliverySite : String
  responseSite : String

variable {F G : Type} [Field F]
    [AddCommGroup G] [Module F G] [DecidableEq G]

abbrev actions := interface Nat language services (ScalarValue F G)
abbrev Verifier (F G : Type) [Field F] [AddCommGroup G] [Module F G] :=
  G → G → Nat → PIR.Proc (actions (F := F) (G := G)) (Option Bool)

def experiment (wiring : Wiring) (base key : G) (service : Nat) :
    PIR.Proc (actions (F := F) (G := G)) (Option Bool) :=
  .call (.receive (.group wiring.groupDomain) wiring.commitmentSite wiring.prover) fun commitment =>
  .call (.query wiring.challengeSite wiring.fieldDomain (.cons service .nil)) fun challenge =>
  .call (.send (ty := .field wiring.fieldDomain) wiring.deliverySite wiring.prover challenge) fun _ =>
  .call (.receive (.field wiring.fieldDomain) wiring.responseSite wiring.prover) fun response =>
  .done (some (decide (response • base = commitment + challenge • key)))

structure VerifierContract (wiring : Wiring) (program : Verifier F G) : Prop where
  realizes : ∀ base key service,
    PIR.ExactRefinement (program base key service) (experiment wiring base key service)

/-- Causal one-session strategies; any fixed private state is part of the choice. -/
structure Strategy (F G : Type) where
  commitment : G
  response : F → F

def transcriptHandler (prover : Strategy F G) (challenge : F) :
    PIR.Handler (actions (F := F) (G := G)) Unit
      (Action Nat language services (ScalarValue F G))
  | action@(.send ..), state => ⟨.returned (), state, [action]⟩
  | action@(.query ..), state => ⟨.returned challenge, state, [action]⟩
  | action@(.receive ty ..), state =>
      ⟨.returned (match ty with
        | .boolean => false
        | .field _ => prover.response challenge
        | .group _ => prover.commitment
        | .service _ => 0), state, [action]⟩

def run (program : Verifier F G) (base key : G) (service : Nat)
    (prover : Strategy F G) (challenge : F) :=
  (program base key service).run (transcriptHandler prover challenge) ()

theorem VerifierContract.accepted_iff {wiring : Wiring} {program : Verifier F G}
    (certificate : VerifierContract wiring program)
    (base key : G) (service : Nat) (prover : Strategy F G) (challenge : F) :
    (run program base key service prover challenge).outcome = .returned (some true) ↔
      prover.response challenge • base = prover.commitment + challenge • key := by
  rw [run, (certificate.realizes base key service).process_eq]
  change PIR.Outcome.returned (some (decide (prover.response challenge • base =
    prover.commitment + challenge • key))) = PIR.Outcome.returned (some true) ↔ _
  simp

theorem VerifierContract.perfect_completeness {wiring : Wiring} {program : Verifier F G}
    (certificate : VerifierContract wiring program)
    (base : G) (secret nonce challenge : F) (service : Nat) :
    (run program base (secret • base) service
      ⟨nonce • base, fun c => nonce + c * secret⟩ challenge).outcome = .returned (some true) := by
  rw [certificate.accepted_iff]
  exact response_equation nonce challenge secret base

theorem VerifierContract.special_soundness {wiring : Wiring} {program : Verifier F G}
    (certificate : VerifierContract wiring program)
    (base key : G) (service : Nat) (prover : Strategy F G)
    (first second : F) (distinct : first ≠ second)
    (acceptFirst : (run program base key service prover first).outcome = .returned (some true))
    (acceptSecond : (run program base key service prover second).outcome = .returned (some true)) :
    ((prover.response first - prover.response second) / (first - second)) • base = key := by
  exact extract_public_key base key prover.commitment first second
    (prover.response first) (prover.response second) distinct
    ((certificate.accepted_iff base key service prover first).mp acceptFirst)
    ((certificate.accepted_iff base key service prover second).mp acceptSecond)

end Zkc.Protocols.Schnorr.Common
